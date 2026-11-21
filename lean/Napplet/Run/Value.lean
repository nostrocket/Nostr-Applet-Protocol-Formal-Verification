/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Value

/-!
# NAP-VALUE runtime component

Upstream: `napplet/naps` PR #30, `naps/NAP-VALUE.md` at `e468764d`.

Wire (napplet → shell): `value.quote {id, request}`, `value.send {id, request}`,
`value.status {id, transferId}`.
Wire (shell → napplet): `value.quote.result {id, quote, error?}`,
`value.send.result {id, result}` or `{id, error}`, `value.status.result {id, status}`
or `{id, error}`, push `value.status.changed {status}` (no `id`).

Flow of `value.send` (every step is a host call; nothing blocks):

1. Policy (`policyError`): rail enabled, target inspectable, `0 < amountMsat ≤` the
   per-napplet maximum. A failure is a top-level `error`; no transfer is created.
2. A transfer id `value-<k>` is allocated. If a configured allowance for this
   napplet (catalog id) and rail covers the amount, it is debited at once;
   otherwise the user is asked (`Call.prompt .value "send"`). A refusal ends the
   transfer as `cancelled` with `"user cancelled"`.
3. For the `zap` rail the shell builds the kind 9734 zap request itself
   (`zapRequest`) and signs it with `Call.sign`.
4. `Call.nap .value "pay"` asks the wallet backend to pay. Its reply gives the
   initial status, which goes back in `value.send.result`. A later
   `HostEvent.nap .value "status"` (for example a zap receipt observed) moves a
   `pending` transfer to `settled` or `failed` and pushes `value.status.changed`
   to the endpoint that sent it.

`settled` is recorded only together with a preimage the backend reported
(`settled` without one stays `pending`); the preimage is disclosed to the napplet
only if `Cfg.disclosePreimage` (default off: NAP-VALUE §Shell Behavior requires
preimages to stay out of the sandbox).

Transfers are scoped to the napplet's catalog id (`transferId` is "scoped to the
requesting napplet") and outlive the endpoint; the endpoint port recorded on a
transfer (where `value.status.changed` goes) is per-endpoint state and is cleared
on teardown. Pending host calls are per-endpoint and are cancelled on teardown.
-/

/-! ## Host operations

| Operation | Args (JSON) | Reply | Contract |
|---|---|---|---|
| `Call.prompt .value "send" d` | `d` = the `ValueRequest` JSON (`rail`, `amountMsat`, `target`, `comment?`, `metadata?`) plus `transferId` | `decision allowed _` | NAP-VALUE consent: the host shows amount, rail, target and recipient identity, comment, metadata and the requesting napplet's verified identity. Any reply other than `decision true _` is a refusal. |
| `Call.sign ev` | kind 9734 `UnsignedEvent` built by `zapRequest` | `signed` | Core `Call.sign` contract (NIP-01 / BIP-340). |
| `Call.nap .value "quote" a` | `a` = `ValueRequest` JSON | `json {feesMsat?: uint, expiresAt?: uint, error?: tstr}` | Best-effort, MUST NOT move money or sign anything. MAY resolve LNURL-pay (LUD-06/LUD-16) to validate payability and estimate fees. `error` uses the NAP-VALUE error strings. |
| `Call.nap .value "pay" a` | `a` = `{transferId, rail, amountMsat, target, comment?, metadata?, zapRequest?}`; `zapRequest` is the signed kind 9734 event (zap rail only) | `json {status: "pending"\|"settled"\|"failed", preimage?: tstr, event?: NostrEvent, error?: tstr}` | Pay exactly `amountMsat` once. `zap`: NIP-57 (resolve the recipient's LNURL-pay endpoint from their kind 0 `lud16`/`lud06`, request an invoice with `nostr=<zapRequest>` and `amount`, check the invoice amount, pay). `lnurl`: LNURL-pay (LUD-06/LUD-16) to `target.lnurl`. Payment through NWC (NIP-47) or an internal wallet. `settled` only on backend confirmation, with the `preimage`; `event` is a NIP-57 zap receipt (kind 9735) when observed. Credentials never leave the host. Cancelling the call (`Effect.cancel`) does not promise a refund. |
| `HostEvent.nap .value "status" a` | `a` = `{transferId, status, preimage?, event?, error?}` | — | Later settlement news for a transfer the host was asked to pay (for example a zap receipt observed on relays). Same meaning as the `pay` reply. |
| `Effect.cancel ⟨.value, n⟩` | — | — | Core contract; issued on endpoint teardown for every outstanding call. |
-/

namespace Napplet.Run.Value

/-! ### Wire types -/

structure ZapTarget where
  pubkey : Option String := none
  eventId : Option String := none
  address : Option String := none
  relays : Option (List String) := none
  deriving DecidableEq, Repr

inductive Target where
  | zap (z : ZapTarget)
  | lnurl (lnurl : String)
  /-- `ValueExtensionTarget`: discriminator and the other members, verbatim. -/
  | ext (type : String) (fields : List (String × Json))
  deriving DecidableEq, Repr

/-- `ValueRequest`. `metadata` is an open map, kept as object members. -/
structure VReq where
  rail : String
  amountMsat : Nat
  comment : Option String := none
  target : Target
  metadata : Option (List (String × Json)) := none
  deriving DecidableEq, Repr

inductive Req where
  | quote (id : String) (r : VReq)
  | send (id : String) (r : VReq)
  | status (id : String) (transferId : String)
  deriving DecidableEq, Repr

/-- Requests whose JSON form is unambiguous: an extension target's discriminator is
not `zap`/`lnurl` and its other members do not repeat `type`. -/
def Target.WF : Target → Prop
  | .ext t fs => t ≠ "zap" ∧ t ≠ "lnurl" ∧ ∀ kv ∈ fs, kv.1 ≠ "type"
  | _ => True

def Req.WF : Req → Prop
  | .quote _ r | .send _ r => r.target.WF
  | .status .. => True

/-! ### Codec -/

/-- An optional member: absent is `some none`; present but malformed is `none`. -/
def optF {α : Type} (j : Json) (k : String) (f : Json → Option α) : Option (Option α) :=
  match j.get? k with
  | none => some none
  | some v => (f v).map some

def asObj? : Json → Option (List (String × Json))
  | .obj kvs => some kvs
  | _ => none

def zapJson (z : ZapTarget) : Json :=
  Json.mkObj [("type", some (.str "zap")), ("pubkey", z.pubkey.map .str),
    ("eventId", z.eventId.map .str), ("address", z.address.map .str),
    ("relays", z.relays.map Json.strs)]

def targetJson : Target → Json
  | .zap z => zapJson z
  | .lnurl u => .obj [("type", .str "lnurl"), ("lnurl", .str u)]
  | .ext t fs => .obj (("type", .str t) :: fs)

def targetOf? (j : Json) : Option Target :=
  match j with
  | .obj kvs =>
    match j.getStr? "type" with
    | none => none
    | some t =>
      if t = "zap" then do
        some (.zap ⟨← optF j "pubkey" Json.asStr?, ← optF j "eventId" Json.asStr?,
          ← optF j "address" Json.asStr?, ← optF j "relays" Json.asStrs?⟩)
      else if t = "lnurl" then (j.getStr? "lnurl").map .lnurl
      else some (.ext t (kvs.filter (·.1 != "type")))
  | _ => none

def vreqJson (r : VReq) : Json :=
  Json.mkObj [("rail", some (.str r.rail)), ("amountMsat", some (.nat r.amountMsat)),
    ("comment", r.comment.map .str), ("target", some (targetJson r.target)),
    ("metadata", r.metadata.map .obj)]

/-- Decode a `ValueRequest`. A bad target is `"invalid target"`; anything else
malformed is `"invalid request"`. -/
def vreqOf? (j : Json) : Except String VReq :=
  match (do
      let rail ← j.getStr? "rail"
      let amountMsat ← (j.get? "amountMsat").bind Json.asNat?
      let comment ← optF j "comment" Json.asStr?
      let metadata ← optF j "metadata" asObj?
      some (rail, amountMsat, comment, metadata)) with
  | none => .error "invalid request"
  | some (rail, amountMsat, comment, metadata) =>
    match (j.get? "target").bind targetOf? with
    | none => .error "invalid target"
    | some target => .ok { rail, amountMsat, comment, target, metadata }

def requestOf? (j : Json) : Except String VReq :=
  match j.get? "request" with
  | none => .error "invalid request"
  | some r => vreqOf? r

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | none => .unknown
  | some t =>
    if t = "value.quote" ∨ t = "value.send" then
      match reqId? j with
      | none => .reject []
      | some id =>
        match requestOf? j with
        | .ok r => .ok (if t = "value.quote" then .quote id r else .send id r)
        | .error e => .reject (errorReply (resultType t) j e)
    else if t = "value.status" then
      match reqId? j with
      | none => .reject []
      | some id =>
        match j.getStr? "transferId" with
        | some tid => .ok (.status id tid)
        | none => .reject (errorReply "value.status.result" j "invalid request")
    else .unknown

def encodeReq : Req → Json
  | .quote id r => Json.msg "value.quote" [("id", some (.str id)), ("request", some (vreqJson r))]
  | .send id r => Json.msg "value.send" [("id", some (.str id)), ("request", some (vreqJson r))]
  | .status id tid => Json.msg "value.status" [("id", some (.str id)), ("transferId", some (.str tid))]

/-! ### State and policy -/

/-- A standing allowance the user configured outside the napplet, bound to one
napplet (catalog id) and rail. -/
structure Allowance where
  napplet : String
  rail : String
  maxPerTransfer : Nat
  remaining : Nat
  deriving DecidableEq, Repr

structure Cfg where
  /-- Enabled rails. -/
  rails : List String := ["zap", "lnurl"]
  /-- Per-napplet (catalog id) and per-rail maximum amount in msat. -/
  maxAmount : String → String → Nat := fun _ _ => 100000000
  /-- Relays written into a zap request's `relays` tag when the target gives none. -/
  receiptRelays : List String := []
  /-- Disclose payment preimages to napplets. -/
  disclosePreimage : Bool := false
  /-- Allowances configured before the session. -/
  allowances : List Allowance := []

inductive TState where
  | pending | settled | failed | cancelled
  deriving DecidableEq, Repr

def TState.name : TState → String
  | .pending => "pending" | .settled => "settled" | .failed => "failed" | .cancelled => "cancelled"

structure Transfer where
  transferId : String
  owner : String
  /-- Endpoint that receives `value.status.changed` (per-endpoint; cleared on teardown). -/
  port : Option PortId
  rail : String
  amountMsat : Nat
  status : TState
  event : Option NostrEvent
  /-- Backend proof of settlement. -/
  preimage : Option String
  error : Option String
  updatedAt : Nat
  deriving DecidableEq, Repr

/-- How a transfer was authorised. -/
inductive Auth where
  | allowance
  | consent
  deriving DecidableEq, Repr

inductive Stage where
  | quote | consent | sign | pay
  deriving DecidableEq, Repr

/-- An outstanding host call for one endpoint's request. -/
structure Pending where
  n : Nat
  port : PortId
  id : String
  owner : String
  req : VReq
  transferId : String
  stage : Stage
  auth : Option Auth
  deriving DecidableEq, Repr

structure St where
  cfg : Cfg
  allowances : List Allowance
  pending : List Pending
  transfers : List Transfer
  next : Nat
  nextTransfer : Nat

def St.init (cfg : Cfg := {}) : St := ⟨cfg, cfg.allowances, [], [], 0, 1⟩

/-- Pubkey component of a NIP-01 address `kind:pubkey:d`. -/
def addrPubkey (a : String) : String := (a.splitOn ":").getD 1 ""

/-- Recipient pubkey of a zap target. -/
def zapRecipient (z : ZapTarget) : Option String :=
  match z.pubkey with
  | some p => some p
  | none => z.address.map addrPubkey

/-- Can the shell inspect and present this target for this rail? -/
def inspectable (r : VReq) : Bool :=
  match r.target with
  | .zap z => r.rail == "zap" && (zapRecipient z).isSome
  | .lnurl u => r.rail == "lnurl" && u != ""
  | .ext _ _ => r.rail != "zap" && r.rail != "lnurl"

def policyError (cfg : Cfg) (owner : String) (r : VReq) : Option String :=
  if r.rail ∉ cfg.rails then some "unsupported rail"
  else if inspectable r = false then some "invalid target"
  else if r.amountMsat = 0 ∨ r.amountMsat > cfg.maxAmount owner r.rail then some "amount out of policy"
  else none

def covers (owner : String) (r : VReq) (a : Allowance) : Bool :=
  a.napplet == owner && a.rail == r.rail && decide (r.amountMsat ≤ a.maxPerTransfer) &&
    decide (r.amountMsat ≤ a.remaining)

def debit (owner : String) (r : VReq) : List Allowance → List Allowance
  | [] => []
  | a :: as =>
    if covers owner r a then { a with remaining := a.remaining - r.amountMsat } :: as
    else a :: debit owner r as

def total (l : List Allowance) : Nat := (l.map (·.remaining)).sum

/-- The NIP-57 kind 9734 zap request, built entirely by the shell. -/
def zapRequest (cfg : Cfg) (w : World) (r : VReq) : UnsignedEvent :=
  let tags : List EventTag := match r.target with
    | .zap z =>
      (match zapRecipient z with | some p => [["p", p]] | none => []) ++
      (match z.eventId with | some e => [["e", e]] | none => []) ++
      (match z.address with | some a => [["a", a]] | none => []) ++
      [["amount", toString r.amountMsat], "relays" :: z.relays.getD cfg.receiptRelays] ++
      (match r.metadata.bind (fun m => (Json.obj m).getStr? "lnurl") with
        | some l => [["lnurl", l]] | none => [])
    | _ => []
  { pubkey := w.user, createdAt := w.now, kind := 9734, tags, content := r.comment.getD "" }

def payArgs (tid : String) (r : VReq) (zap : Option NostrEvent) : Json :=
  Json.mkObj [("transferId", some (.str tid)), ("rail", some (.str r.rail)),
    ("amountMsat", some (.nat r.amountMsat)), ("target", some (targetJson r.target)),
    ("comment", r.comment.map .str), ("metadata", r.metadata.map .obj),
    ("zapRequest", zap.map NostrEvent.toJson)]

def promptArgs (tid : String) (r : VReq) : Json :=
  Json.mkObj [("transferId", some (.str tid)), ("rail", some (.str r.rail)),
    ("amountMsat", some (.nat r.amountMsat)), ("target", some (targetJson r.target)),
    ("comment", r.comment.map .str), ("metadata", r.metadata.map .obj)]

/-! ### Results -/

def TState.ok : TState → Bool
  | .pending | .settled => true
  | _ => false

def resultFields (cfg : Cfg) (t : Transfer) : List (String × Option Json) :=
  [("ok", some (.bool t.status.ok)), ("transferId", some (.str t.transferId)),
   ("status", some (.str t.status.name)), ("rail", some (.str t.rail)),
   ("amountMsat", some (.nat t.amountMsat)), ("event", t.event.map NostrEvent.toJson),
   ("preimage", if cfg.disclosePreimage then t.preimage.map .str else none),
   ("error", t.error.map .str)]

/-- `ValueResult`. -/
def resultJson (cfg : Cfg) (t : Transfer) : Json := Json.mkObj (resultFields cfg t)

/-- `ValueStatus`. -/
def statusJson (cfg : Cfg) (t : Transfer) : Json :=
  Json.mkObj (resultFields cfg t ++ [("updatedAt", some (.nat t.updatedAt))])

def sendResult (cfg : Cfg) (id : String) (t : Transfer) : Json :=
  Json.msg "value.send.result" [("id", some (.str id)), ("result", some (resultJson cfg t))]

def changedJson (cfg : Cfg) (t : Transfer) : Json :=
  Json.msg "value.status.changed" [("status", some (statusJson cfg t))]

def topError (type id e : String) : Json :=
  Json.msg type [("id", some (.str id)), ("error", some (.str e))]

def quoteJson (id : String) (r : VReq) (fees expires : Option Nat) (err : Option String) : Json :=
  Json.msg "value.quote.result"
    [("id", some (.str id)),
     ("quote", some (Json.mkObj [("ok", some (.bool err.isNone)), ("rail", some (.str r.rail)),
        ("amountMsat", some (.nat r.amountMsat)), ("feesMsat", fees.map Json.nat),
        ("expiresAt", expires.map Json.nat), ("error", err.map .str)])),
     ("error", err.map .str)]

/-- Settlement news from the backend. `settled` needs a preimage, otherwise the
transfer stays `pending`; anything else is a failure. -/
def outcome (j : Json) : TState × Option String × Option String :=
  let pre := j.getStr? "preimage"
  match j.getStr? "status" with
  | some "settled" => if pre.isSome then (.settled, pre, none) else (.pending, none, none)
  | some "pending" => (.pending, none, none)
  | _ => (.failed, none, some ((j.getStr? "error").getD "payment failed"))

/-! ### Component -/

def addPending (s : St) (p : Pending) : St := { s with pending := p :: s.pending, next := s.next + 1 }

/-- Continue an authorised transfer: sign the zap request, or pay. -/
def proceed (s : St) (w : World) (port : PortId) (id owner : String) (r : VReq) (tid : String)
    (a : Auth) : St × List Eff :=
  if r.rail = "zap" then
    (addPending s ⟨s.next, port, id, owner, r, tid, .sign, some a⟩,
     [.call ⟨.value, s.next⟩ (.sign (zapRequest s.cfg w r))])
  else
    (addPending s ⟨s.next, port, id, owner, r, tid, .pay, some a⟩,
     [.call ⟨.value, s.next⟩ (.nap .value "pay" (payArgs tid r none))])

/-- Record a transfer and answer the `value.send`. -/
def finish (s : St) (w : World) (p : Pending) (st : TState) (ev : Option NostrEvent)
    (pre err : Option String) : St × List Eff :=
  let t : Transfer := ⟨p.transferId, p.owner, some p.port, p.req.rail, p.req.amountMsat, st, ev,
    pre, err, w.now⟩
  ({ s with transfers := t :: s.transfers }, [.send p.port (sendResult s.cfg p.id t)])

def handle (_h : Host) (w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .quote id r =>
    match policyError s.cfg cx.catalogId r with
    | some e => (s, [.send cx.port (quoteJson id r none none (some e))])
    | none =>
      (addPending s ⟨s.next, cx.port, id, cx.catalogId, r, "", .quote, none⟩,
       [.call ⟨.value, s.next⟩ (.nap .value "quote" (vreqJson r))])
  | .send id r =>
    match policyError s.cfg cx.catalogId r with
    | some e => (s, [.send cx.port (topError "value.send.result" id e)])
    | none =>
      let tid := "value-" ++ toString s.nextTransfer
      let s1 := { s with nextTransfer := s.nextTransfer + 1 }
      if s.allowances.any (covers cx.catalogId r) then
        proceed { s1 with allowances := debit cx.catalogId r s.allowances } w cx.port id
          cx.catalogId r tid .allowance
      else
        (addPending s1 ⟨s.next, cx.port, id, cx.catalogId, r, tid, .consent, none⟩,
         [.call ⟨.value, s.next⟩ (.prompt .value "send" (promptArgs tid r))])
  | .status id tid =>
    match s.transfers.find? (fun t => t.transferId == tid && t.owner == cx.catalogId) with
    | some t => (s, [.send cx.port (Json.msg "value.status.result"
        [("id", some (.str id)), ("status", some (statusJson s.cfg t))])])
    | none => (s, [.send cx.port (topError "value.status.result" id "transfer not found")])

def onReply (_h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.pending.find? (·.n == n) with
  | none => (s, [])
  | some p =>
    let s' := { s with pending := s.pending.filter (·.n != n) }
    match p.stage, rep with
    | .quote, .json j =>
      (s', [.send p.port (quoteJson p.id p.req ((j.get? "feesMsat").bind Json.asNat?)
        ((j.get? "expiresAt").bind Json.asNat?) (j.getStr? "error"))])
    | .quote, _ => (s', [.send p.port (quoteJson p.id p.req none none (some "wallet unavailable"))])
    | .consent, .decision true _ => proceed s' w p.port p.id p.owner p.req p.transferId .consent
    | .consent, _ => finish s' w p .cancelled none none (some "user cancelled")
    | .sign, .signed (some ev) =>
      (addPending s' { p with n := s'.next, stage := .pay },
       [.call ⟨.value, s'.next⟩ (.nap .value "pay" (payArgs p.transferId p.req (some ev)))])
    | .sign, _ => finish s' w p .failed none none (some "payment failed")
    | .pay, .json j =>
      let (st, pre, err) := outcome j
      finish s' w p st ((j.get? "event").bind NostrEvent.ofJson?) pre err
    | .pay, _ => finish s' w p .failed none none (some "payment failed")

/-- Apply settlement news to a pending transfer. Terminal states never change. -/
def settle (w : World) (j : Json) (t : Transfer) : Transfer :=
  let (st, pre, err) := outcome j
  { t with status := st, preimage := pre, error := err, updatedAt := w.now,
           event := ((j.get? "event").bind NostrEvent.ofJson?).orElse fun _ => t.event }

def onEvent (_h : Host) (w : World) (s : St) : HostEvent → St × List Eff
  | .nap .value "status" j =>
    match j.getStr? "transferId" with
    | none => (s, [])
    | some tid =>
      match s.transfers.find? (fun t => t.transferId == tid && t.status == .pending) with
      | none => (s, [])
      | some t =>
        let t' := settle w j t
        if t'.status = .pending then (s, [])
        else
          ({ s with transfers := s.transfers.map fun x =>
              if x.transferId == tid && x.status == .pending then settle w j x else x },
           match t.port with
           | some p => [.send p (changedJson s.cfg t')]
           | none => [])
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with pending := s.pending.filter (·.port != p),
            transfers := s.transfers.map fun t => if t.port = some p then { t with port := none } else t },
   (s.pending.filter (·.port == p)).map fun q => .effect (.cancel ⟨.value, q.n⟩))

def mentions (s : St) (p : PortId) : Bool :=
  s.pending.any (·.port == p) || s.transfers.any (·.port == some p)

/-! ### Codec properties -/

theorem lookup_none {l : List (String × Json)} {k : String} (h : ∀ kv ∈ l, kv.1 ≠ k) :
    Json.lookup l k = none := by
  induction l with
  | nil => rfl
  | cons kv l ih =>
    obtain ⟨k', v⟩ := kv
    simp only [Json.lookup]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have : k' ≠ k := h (k', v) (List.mem_cons_self ..)
    simp [this]

theorem targetOf?_targetJson (t : Target) (ht : t.WF) : targetOf? (targetJson t) = some t := by
  cases t with
  | zap z =>
    obtain ⟨a, b, c, d⟩ := z
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [targetOf?, targetJson, zapJson, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, optF]
  | lnurl u => simp [targetOf?, targetJson, Json.getStr?, Json.get?, Json.lookup]
  | ext t fs =>
    obtain ⟨h1, h2, h3⟩ := ht
    have hl : Json.lookup fs "type" = none := lookup_none h3
    have hf : fs.filter (·.1 != "type") = fs := by
      rw [List.filter_eq_self]; intro kv hkv; simpa using h3 kv hkv
    simp [targetOf?, targetJson, Json.getStr?, Json.get?, Json.lookup, hl, h1, h2, hf]

theorem vreqOf?_vreqJson (r : VReq) (hr : r.target.WF) : vreqOf? (vreqJson r) = .ok r := by
  obtain ⟨rail, amt, c, t, m⟩ := r
  have ht := targetOf?_targetJson t hr
  cases c <;> cases m <;>
    simp [vreqOf?, vreqJson, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, optF, Json.isObj,
      asObj?, ht]

theorem decode_encodeReq (r : Req) (hr : r.WF) : decode (encodeReq r) = .ok r := by
  cases r with
  | quote id v =>
    have := vreqOf?_vreqJson v hr
    simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?,
      requestOf?, this]
  | send id v =>
    have := vreqOf?_vreqJson v hr
    simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?,
      requestOf?, this]
  | status id tid =>
    simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]

/-! ### Teardown and `mentions` -/

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp only [drop, mentions, Bool.or_eq_false_iff, List.any_eq_false, List.mem_filter,
    List.mem_map]
  constructor
  · intro x hx; simpa using hx.2
  · rintro x ⟨t, -, rfl⟩
    by_cases h : t.port = some p <;> simp [h]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp only [drop, mentions, Bool.or_eq_true, List.any_eq_true, List.mem_filter,
    List.mem_map] at h ⊢
  rcases h with ⟨x, hx, hq⟩ | ⟨x, ⟨t, ht, rfl⟩, hq⟩
  · exact .inl ⟨x, hx.1, hq⟩
  · right
    refine ⟨t, ht, ?_⟩
    by_cases h : t.port = some p <;> simp_all

/-- Port-bound reasoning: a new state mentions only old ports or ports in `P`. -/
def Within (s s' : St) (P : PortId → Prop) : Prop :=
  ∀ q, mentions s' q = true → mentions s q = true ∨ P q

theorem within_of (s s' : St) (P : PortId → Prop)
    (hp : ∀ x ∈ s'.pending, x ∈ s.pending ∨ P x.port)
    (ht : ∀ t ∈ s'.transfers, (∃ u ∈ s.transfers, u.port = t.port) ∨ t.port = none ∨
      ∃ q, t.port = some q ∧ P q) : Within s s' P := by
  intro q hq
  simp only [mentions, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hq ⊢
  rcases hq with ⟨x, hx, rfl⟩ | ⟨t, htm, hq⟩
  · rcases hp x hx with h | h
    · exact .inl (.inl ⟨x, h, rfl⟩)
    · exact .inr h
  · rcases ht t htm with ⟨u, hu, hut⟩ | h | ⟨q', hq', hP⟩
    · exact .inl (.inr ⟨u, hu, hut.trans hq⟩)
    · rw [h] at hq; cases hq
    · rw [hq'] at hq; cases hq; exact .inr hP

theorem within_trans {s s1 s2 : St} {P : PortId → Prop} (h1 : Within s s1 P) (h2 : Within s1 s2 P) :
    Within s s2 P := by
  intro q hq
  rcases h2 q hq with h | h
  · exact h1 q h
  · exact .inr h

theorem within_refl (s : St) (P : PortId → Prop) : Within s s P := fun _ h => .inl h

theorem within_addPending (s : St) (x : Pending) : Within s (addPending s x) (· = x.port) :=
  within_of _ _ _ (by
    intro y hy; simp only [addPending, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact .inr rfl
    · exact .inl hy) (fun t ht => .inl ⟨t, ht, rfl⟩)

theorem within_mono {s s' : St} {P Q : PortId → Prop} (h : Within s s' P) (hPQ : ∀ q, P q → Q q) :
    Within s s' Q := fun q hq => (h q hq).imp id (hPQ q)

theorem within_proceed (s : St) (w : World) (port : PortId) (id owner : String) (r : VReq)
    (tid : String) (a : Auth) : Within s (proceed s w port id owner r tid a).1 (· = port) := by
  unfold proceed
  split
  · exact within_addPending s _
  · exact within_addPending s _

theorem within_finish (s : St) (w : World) (p : Pending) (st : TState) (ev : Option NostrEvent)
    (pre err : Option String) : Within s (finish s w p st ev pre err).1 (· = p.port) :=
  within_of _ _ _ (fun x hx => .inl hx) (by
    intro t ht; simp only [finish, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact .inr (.inr ⟨p.port, rfl, rfl⟩)
    · exact .inl ⟨t, ht, rfl⟩)

theorem within_fields (s : St) (al : List Allowance) (k : Nat) :
    Within s { s with allowances := al, nextTransfer := k } (fun _ => False) :=
  within_of _ _ _ (fun x hx => .inl hx) (fun t ht => .inl ⟨t, ht, rfl⟩)

theorem within_filterPending (s : St) (f : Pending → Bool) :
    Within s { s with pending := s.pending.filter f } (fun _ => False) :=
  within_of _ _ _ (fun x hx => .inl ((List.mem_filter.mp hx).1)) (fun t ht => .inl ⟨t, ht, rfl⟩)

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  have key : Within s (handle h w cx s r).1 (· = cx.port) := by
    cases r with
    | quote id v =>
      simp only [handle]; split
      · exact within_refl _ _
      · exact within_addPending s _
    | send id v =>
      simp only [handle]; split
      · exact within_refl _ _
      · (try dsimp only); split
        · exact within_trans (within_mono (within_fields s _ _) (by simp))
            (within_proceed _ _ _ _ _ _ _ _)
        · exact within_trans (within_mono (within_fields s s.allowances _) (by simp))
            (within_addPending _ _)
    | status id tid =>
      simp only [handle]; split <;> exact within_refl _ _
  rcases key q hm with h1 | h1
  · exact .inl h1
  · exact .inr ⟨cx, hcx, h1.symm⟩

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  simp only [onReply] at hm
  split at hm
  · exact hm
  · rename_i p hp
    have hpm : p ∈ s.pending := List.mem_of_find?_eq_some hp
    have hold : mentions s p.port = true := by
      simp only [mentions, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact .inl ⟨p, hpm, rfl⟩
    have hf := within_filterPending s (·.n != n)
    have key : Within s (onReply h w s n rep).1 (· = p.port) := by
      simp only [onReply, hp]
      split
      · exact within_mono hf (by simp)
      · exact within_mono hf (by simp)
      · exact within_trans (within_mono hf (by simp)) (within_proceed _ _ _ _ _ _ _ _)
      · exact within_trans (within_mono hf (by simp)) (within_finish _ _ _ _ _ _ _)
      · exact within_trans (within_mono hf (by simp)) (within_addPending _ _)
      · exact within_trans (within_mono hf (by simp)) (within_finish _ _ _ _ _ _ _)
      · exact within_trans (within_mono hf (by simp)) (within_finish _ _ _ _ _ _ _)
      · exact within_trans (within_mono hf (by simp)) (within_finish _ _ _ _ _ _ _)
    have hm' : mentions (onReply h w s n rep).1 q = true := by
      simp only [onReply]; rw [hp]; exact hm
    rcases key q (by simpa [onReply, hp] using hm) with h1 | h1
    · exact h1
    · exact h1 ▸ hold

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  have key : Within s (onEvent h w s e).1 (fun _ => False) := by
    unfold onEvent
    split
    · split
      · exact within_refl _ _
      · split
        · exact within_refl _ _
        · dsimp only
          split
          · exact within_refl _ _
          · refine within_of _ _ _ (fun x hx => .inl hx) ?_
            intro t ht
            simp only [List.mem_map] at ht
            obtain ⟨u, hu, rfl⟩ := ht
            refine .inl ⟨u, hu, ?_⟩
            split <;> simp [settle]
    · exact within_refl _ _
  rcases key q hm with h1 | h1
  · exact h1
  · exact h1.elim

/-! ### NAP-VALUE properties, lifted -/

/-- A payment instruction from `handle` happens only under a covering allowance of
this napplet (non-zap rails; zaps are signed first). -/
theorem handle_pay_covered (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (t : CallTag)
    (a : Json) (hp : Eff.call t (.nap .value "pay" a) ∈ (handle h w cx s r).2) :
    ∃ id v, r = .send id v ∧ policyError s.cfg cx.catalogId v = none ∧
      ∃ al ∈ s.allowances, covers cx.catalogId v al = true := by
  cases r with
  | quote id v =>
    simp only [handle] at hp; split at hp <;> simp at hp
  | status id tid =>
    simp only [handle] at hp; split at hp <;> simp at hp
  | send id v =>
    simp only [handle] at hp
    split at hp
    · simp at hp
    · rename_i hpol
      try dsimp only at hp
      split at hp
      · rename_i hcov
        simp only [List.any_eq_true] at hcov
        exact ⟨id, v, rfl, hpol, hcov⟩
      · simp at hp

/-- A payment or zap signature from `onReply` continues a request that was either
authorised by the user's prompt decision just received, or is in the signing stage
(which only authorised requests reach, `authOK_onReply`). -/
theorem onReply_pay_authorized (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (t : CallTag)
    (c : Call) (hc : Eff.call t c ∈ (onReply h w s n rep).2)
    (hk : (∃ a, c = .nap .value "pay" a) ∨ ∃ ev, c = .sign ev) :
    ∃ p ∈ s.pending, p.n = n ∧
      ((p.stage = .consent ∧ ∃ ch, rep = .decision true ch) ∨ p.stage = .sign) := by
  simp only [onReply] at hc
  split at hc
  · simp at hc
  · rename_i p hp
    have hpm := List.mem_of_find?_eq_some hp
    have hn : p.n = n := by simpa using List.find?_some hp
    refine ⟨p, hpm, hn, ?_⟩
    split at hc
    all_goals first
      | (simp [finish] at hc; done)
      | (simp at hc; rcases hk with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp_all; done)
      | (exact .inl ⟨by assumption, _, rfl⟩)
      | (exact .inr (by assumption))

/-- Every request past consent carries its authorisation. -/
def AuthOK (s : St) : Prop := ∀ p ∈ s.pending, p.stage = .sign ∨ p.stage = .pay → p.auth.isSome

theorem authOK_addPending {s : St} {x : Pending} (hs : AuthOK s)
    (hx : x.stage = .sign ∨ x.stage = .pay → x.auth.isSome) : AuthOK (addPending s x) := by
  intro p hp; simp only [addPending, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact hx
  · exact hs p hp

theorem authOK_proceed {s : St} (hs : AuthOK s) (w : World) (port : PortId) (id owner : String)
    (r : VReq) (tid : String) (a : Auth) : AuthOK (proceed s w port id owner r tid a).1 := by
  unfold proceed; split <;> exact authOK_addPending hs (by simp)

theorem authOK_handle (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (hs : AuthOK s) :
    AuthOK (handle h w cx s r).1 := by
  cases r with
  | quote id v =>
    simp only [handle]; split
    · exact hs
    · exact authOK_addPending hs (by simp)
  | send id v =>
    simp only [handle]; split
    · exact hs
    · (try dsimp only); split
      · apply authOK_proceed; exact fun p hp => hs p hp
      · apply authOK_addPending (fun p hp => hs p hp) (by simp)
  | status id tid => simp only [handle]; split <;> exact hs

theorem authOK_onReply (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (hs : AuthOK s) :
    AuthOK (onReply h w s n rep).1 := by
  have hf : AuthOK { s with pending := s.pending.filter (·.n != n) } :=
    fun p hp => hs p ((List.mem_filter.mp hp).1)
  simp only [onReply]
  split
  · exact hs
  · rename_i p hp
    have hpa := hs p (List.mem_of_find?_eq_some hp)
    split
    all_goals first
      | exact hf
      | exact authOK_proceed hf _ _ _ _ _ _ _
      | exact hf
      | (exact authOK_addPending hf (fun _ => hpa (.inl (by assumption))))

/-- `value.quote` is advisory: it never prompts, signs or pays, and leaves the
allowances untouched (NAP-VALUE: "A quote is advisory"). -/
theorem quote_not_binding (h : Host) (w : World) (cx : Ctx) (s : St) (id : String) (v : VReq) :
    (handle h w cx s (.quote id v)).1.allowances = s.allowances ∧
    ∀ e ∈ (handle h w cx s (.quote id v)).2,
      (∃ p m, e = .send p m) ∨ ∃ t, e = .call t (.nap .value "quote" (vreqJson v)) := by
  simp only [handle]
  split
  · simp
  · simp [addPending]

theorem debit_total {owner : String} {r : VReq} :
    ∀ {l : List Allowance}, l.any (covers owner r) = true → total (debit owner r l) + r.amountMsat = total l
  | [], h => by simp at h
  | b :: bs, h => by
    simp only [debit]
    split
    · rename_i hb
      simp only [covers, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [total, List.map_cons, List.sum_cons]
      omega
    · rename_i hb
      have : bs.any (covers owner r) = true := by
        simp only [List.any_cons, Bool.or_eq_true] at h
        rcases h with h | h
        · exact absurd h hb
        · exact h
      have ih := debit_total this
      simp only [total, List.map_cons, List.sum_cons] at ih ⊢
      omega

theorem debit_other {owner : String} {r : VReq} :
    ∀ {l : List Allowance} {a : Allowance}, a ∈ l → a.napplet ≠ owner → a ∈ debit owner r l
  | [], _, h, _ => by simp at h
  | b :: bs, a, h, hn => by
    simp only [debit]
    split
    · rename_i hb
      rcases List.mem_cons.mp h with rfl | h
      · simp only [covers, Bool.and_eq_true, beq_iff_eq] at hb
        exact absurd hb.1.1.1 hn
      · exact List.mem_cons_of_mem _ h
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (debit_other h hn)

theorem proceed_allowances (s : St) (w : World) (port : PortId) (id owner : String) (r : VReq)
    (tid : String) (a : Auth) : (proceed s w port id owner r tid a).1.allowances = s.allowances := by
  unfold proceed; split <;> rfl

/-- No overspend: a request either leaves the allowances unchanged, or (a covered
`value.send`) lowers the total remaining by exactly the amount. -/
theorem handle_allowance_no_overspend (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    (handle h w cx s r).1.allowances = s.allowances ∨
    ∃ id v, r = .send id v ∧ total (handle h w cx s r).1.allowances + v.amountMsat = total s.allowances := by
  cases r with
  | quote id v => left; simp only [handle]; split <;> rfl
  | status id tid => left; simp only [handle]; split <;> rfl
  | send id v =>
    simp only [handle]
    split
    · exact .inl rfl
    · try dsimp only
      split
      · rename_i hcov
        right
        refine ⟨id, v, rfl, ?_⟩
        rw [proceed_allowances]
        exact debit_total hcov
      · exact .inl rfl

/-- Other napplets' allowances are never touched by this napplet's spending. -/
theorem handle_allowance_other (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) {a : Allowance}
    (ha : a ∈ s.allowances) (hn : a.napplet ≠ cx.catalogId) : a ∈ (handle h w cx s r).1.allowances := by
  rcases handle_allowance_no_overspend h w cx s r with he | ⟨id, v, rfl, -⟩
  · rw [he]; exact ha
  · simp only [handle]
    split
    · exact ha
    · try dsimp only
      split
      · rw [proceed_allowances]; exact debit_other ha hn
      · exact ha

theorem onReply_allowances (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) :
    (onReply h w s n rep).1.allowances = s.allowances := by
  simp only [onReply]
  split
  · rfl
  · split <;> first | rfl | (rw [proceed_allowances]) | (simp [finish]) | (simp [addPending])

/-- Every signature the component asks for is the shell-built NIP-57 zap request
(kind 9734, the user's pubkey, the shell clock). -/
theorem sign_only_zap_request (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (t : CallTag)
    (ev : UnsignedEvent) (hs : Eff.call t (.sign ev) ∈ (handle h w cx s r).2) :
    ∃ id v, r = .send id v ∧ v.rail = "zap" ∧ ev = zapRequest s.cfg w v ∧ ev.kind = 9734 ∧
      ev.pubkey = w.user := by
  cases r with
  | quote id v => simp only [handle] at hs; split at hs <;> simp at hs
  | status id tid => simp only [handle] at hs; split at hs <;> simp at hs
  | send id v =>
    simp only [handle] at hs
    split at hs
    · simp at hs
    · try dsimp only at hs
      split at hs
      · simp only [proceed] at hs
        split at hs
        · rename_i hz
          simp at hs
          obtain ⟨-, rfl⟩ := hs
          exact ⟨id, v, rfl, hz, rfl, rfl, rfl⟩
        · simp at hs
      · simp at hs

/-- Every recorded `settled` transfer carries the backend's proof. -/
def SettledOK (s : St) : Prop := ∀ t ∈ s.transfers, t.status = .settled → t.preimage.isSome

theorem outcome_settled {j : Json} (h : (outcome j).1 = .settled) : ((outcome j).2.1).isSome := by
  unfold outcome at *
  dsimp only at *
  split at h
  · split at h
    · rename_i hp; split <;> simp_all
    · simp at h
  · simp at h
  · simp at h

theorem settledOK_handle (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (hs : SettledOK s) :
    SettledOK (handle h w cx s r).1 := by
  have : (handle h w cx s r).1.transfers = s.transfers := by
    cases r with
    | quote id v => simp only [handle]; split <;> rfl
    | status id tid => simp only [handle]; split <;> rfl
    | send id v =>
      simp only [handle]; split
      · rfl
      · try dsimp only
        split
        · simp only [proceed]; split <;> rfl
        · rfl
  intro t ht; rw [this] at ht; exact hs t ht

theorem settledOK_onReply (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (hs : SettledOK s) :
    SettledOK (onReply h w s n rep).1 := by
  have fin : ∀ (s' : St) (p : Pending) st ev pre err, SettledOK s' →
      (st = .settled → pre.isSome) → SettledOK (finish s' w p st ev pre err).1 := by
    intro s' p st ev pre err hs' hst t ht
    simp only [finish, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hst
    · exact hs' t ht
  have hf : SettledOK { s with pending := s.pending.filter (·.n != n) } := hs
  simp only [onReply]
  split
  · exact hs
  · split
    all_goals first
      | exact hf
      | (simp only [proceed]; split <;> exact hf)
      | exact (fin _ _ _ _ _ _ hf (by simp))
      | exact (fin _ _ _ _ _ _ hf outcome_settled)

theorem settledOK_onEvent (h : Host) (w : World) (s : St) (e : HostEvent) (hs : SettledOK s) :
    SettledOK (onEvent h w s e).1 := by
  unfold onEvent
  split
  · split
    · exact hs
    · split
      · exact hs
      · dsimp only
        split
        · exact hs
        · intro t ht
          simp only [List.mem_map] at ht
          obtain ⟨u, hu, rfl⟩ := ht
          split
          · intro h1
            simp only [settle] at h1 ⊢
            exact outcome_settled h1
          · exact hs u hu
  · exact hs

/-! ### Vectors (upstream examples) -/

def exReq : String := "{ \"rail\": \"zap\", \"amountMsat\": 21000, \"comment\": \"great note\", \"target\": { \"type\": \"zap\", \"eventId\": \"abc...\", \"pubkey\": \"def...\", \"relays\": [\"wss://relay.example.com\"] } }"

def exHost : Host :=
  { crypto := ⟨fun _ => "", fun _ => true⟩, verifyEvent := fun _ => true, sniff := fun _ => "",
    rasterize := fun _ => none, looksCiphertext := fun _ => false, encryptedWith := fun _ => none,
    transform := id }

def exId : Identity := { dTag := some "zapper", artifactHash := "h" }

def exCx : Ctx := { port := 7, window := 1, identity := exId, exposed := [.value], inst := 0 }

def exWorld : World := { now := 1234567890, live := [exCx], user := "user" }

/-- A shell with a 100 000 msat zap allowance for the example napplet. -/
def exSt : St := .init { allowances := [⟨exCx.catalogId, "zap", 100000, 100000⟩] }

def exSigned : NostrEvent :=
  { id := "zr", pubkey := "user", createdAt := 1234567890, kind := 9734, tags := [], content := "great note", sig := "s" }

-- decode the upstream requests
#guard decode (Json.parse! ("{ \"type\": \"value.quote\", \"id\": \"q1\", \"request\": " ++ exReq ++ " }")) matches
  .ok (.quote "q1" ⟨"zap", 21000, some "great note",
    .zap ⟨some "def...", some "abc...", none, some ["wss://relay.example.com"]⟩, none⟩)
#guard decode (Json.parse! ("{ \"type\": \"value.send\", \"id\": \"s1\", \"request\": " ++ exReq ++ " }")) matches
  .ok (.send "s1" _)
#guard decode (Json.parse! "{ \"type\": \"value.refund\", \"id\": \"x\" }") matches .unknown
#guard match decode (Json.parse! "{ \"type\": \"value.send\", \"id\": \"s9\", \"request\": { \"rail\": \"zap\", \"amountMsat\": 1, \"target\": 5 } }") with
  | .reject [m] => Json.same m (Json.parse! "{\"type\":\"value.send.result\",\"id\":\"s9\",\"error\":\"invalid target\"}")
  | _ => false

-- quote: policy passes, host quote reply, upstream `value.quote.result`
#guard
  match decode (Json.parse! ("{ \"type\": \"value.quote\", \"id\": \"q1\", \"request\": " ++ exReq ++ " }")) with
  | .ok r =>
    let (s1, e1) := handle exHost exWorld exCx exSt r
    match e1 with
    | [.call ⟨.value, n⟩ (.nap .value "quote" _)] =>
      match onReply exHost exWorld s1 n (.json (Json.parse! "{\"feesMsat\": 10, \"expiresAt\": 1234567999}")) with
      | (_, [.send 7 m]) => Json.same m (Json.parse! "{ \"type\": \"value.quote.result\", \"id\": \"q1\", \"quote\": { \"ok\": true, \"rail\": \"zap\", \"amountMsat\": 21000, \"feesMsat\": 10, \"expiresAt\": 1234567999 } }")
      | _ => false
    | _ => false
  | _ => false

-- send under an allowance: sign zap request, pay, `pending`, then settled push
#guard
  match decode (Json.parse! ("{ \"type\": \"value.send\", \"id\": \"s1\", \"request\": " ++ exReq ++ " }")) with
  | .ok r =>
    let (s1, e1) := handle exHost exWorld exCx exSt r
    match e1 with
    | [.call ⟨.value, n1⟩ (.sign ev)] =>
      ev.kind == 9734 && ev.tags == [["p", "def..."], ["e", "abc..."], ["amount", "21000"], ["relays", "wss://relay.example.com"]] &&
      match onReply exHost exWorld s1 n1 (.signed (some exSigned)) with
      | (s2, [.call ⟨.value, n2⟩ (.nap .value "pay" _)]) =>
        match onReply exHost exWorld s2 n2 (.json (Json.parse! "{\"status\": \"pending\"}")) with
        | (s3, [.send 7 m]) =>
          Json.same m (Json.parse! "{ \"type\": \"value.send.result\", \"id\": \"s1\", \"result\": { \"ok\": true, \"transferId\": \"value-1\", \"status\": \"pending\", \"rail\": \"zap\", \"amountMsat\": 21000 } }") &&
          match onEvent exHost { exWorld with now := 1234567901 } s3
              (.nap .value "status" (Json.parse! "{\"transferId\": \"value-1\", \"status\": \"settled\", \"preimage\": \"pp\"}")) with
          | (_, [.send 7 m2]) => Json.same m2 (Json.parse! "{ \"type\": \"value.status.changed\", \"status\": { \"ok\": true, \"transferId\": \"value-1\", \"status\": \"settled\", \"rail\": \"zap\", \"amountMsat\": 21000, \"updatedAt\": 1234567901 } }")
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false

-- user cancelled (no allowance; second transfer of the session)
#guard
  match decode (Json.parse! ("{ \"type\": \"value.send\", \"id\": \"s2\", \"request\": " ++ exReq ++ " }")) with
  | .ok r =>
    let (s1, e1) := handle exHost exWorld exCx { (St.init) with nextTransfer := 2 } r
    match e1 with
    | [.call ⟨.value, n⟩ (.prompt .value "send" _)] =>
      match onReply exHost exWorld s1 n (.decision false none) with
      | (_, [.send 7 m]) => Json.same m (Json.parse! "{ \"type\": \"value.send.result\", \"id\": \"s2\", \"result\": { \"ok\": false, \"transferId\": \"value-2\", \"status\": \"cancelled\", \"rail\": \"zap\", \"amountMsat\": 21000, \"error\": \"user cancelled\" } }")
      | _ => false
    | _ => false
  | _ => false

end Napplet.Run.Value
