/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Relay
import Napplet.Net

/-!
# NAP-RELAY runtime component

Upstream: `napplet/naps` PR #2 (branch `nub-relay`), `naps/NAP-RELAY.md` at `9f30b350`.

Wire (napplet → shell):
`relay.subscribe {id, subId, filters, relay?}`, `relay.close {id, subId}`,
`relay.publish {id, event}`, `relay.publishEncrypted {id, event, recipient, encryption?}`,
`relay.query {id, filters}`.

Wire (shell → napplet):
`relay.event {subId, result}`, `relay.eose {subId}`, `relay.closed {subId, reason?}`,
`relay.publish.result` / `relay.publishEncrypted.result {id, ok, event?, eventId?, error?}`,
`relay.query.result {id, events}` or `{id, error}` ("MAY include an `error` field instead
of `events`").

`result` is a `RelayEventResult` `{event, sidecar?}` with `sidecar {relayHints?}`.

Behaviour (this file is the executable model of `Napplet.NapRelay`):

* **Shell signs.** `publish` stamps the template (`EventTemplate.stamp`, user key and shell
  clock) and calls `Call.sign`; the signed event is the only thing ever handed to
  `Call.publish`. No user (`w.user = ""`) fails with `"no signer configured"`.
* **Never sign napplet ciphertext.** A template whose `content` satisfies
  `h.looksCiphertext` is refused with `"blocked: ciphertext from napplet"` before any
  host call (modelling decision 11); for `publishEncrypted` the napplet's plaintext is
  checked, then the host encrypts (`Call.encrypt`, NIP-44 unless `encryption` says
  `nip04`), and only the host's ciphertext is signed (encrypt, then sign).
* **Decrypt before delivery.** An incoming event with `h.encryptedWith ev = some sc` is
  never delivered raw: it is decrypted (`Call.decrypt`) and delivered with `content`
  replaced by the plaintext (modelling decision 8); an undecryptable event is not
  delivered at all. `relay.eose` (and the `relay.query.result`) waits for outstanding
  decryptions of stored events of that subscription.
* **Own subscriptions only.** Subscriptions live in the endpoint's own bucket, keyed by
  `subId`; `relay.close` only touches the caller's bucket. A reused `subId` replaces the
  caller's earlier subscription (modelling decision 10). `relay.close` is answered with
  `relay.closed {subId}` (modelling decision 9; kehto does the same).
* **Sidecar.** Byte pre-resolution (`sidecar.resources`) is never performed, so it is
  off by default and every opt-out is honoured trivially. `sidecar.relayHints` carries
  the relay the host observed the event on (`Cfg.relayHints`, default on, as upstream
  SHOULD); `relay.query` merges hints of duplicate events.
* **ACL.** `Cfg.canRead` gates `subscribe`/`query` (refused subscribe:
  `relay.closed {subId, reason: "policy denied"}`; refused query:
  `relay.query.result {id, error: "policy denied"}`), `Cfg.canWrite` gates publishing
  (`ok: false, error: "policy denied"`). Scoped relay URLs must pass `Cfg.scopedAllowed`
  (SSRF validation, default `Net.relayAllowed`: `wss://`, no localhost/`.local` names, no
  private or reserved IP literals) or the subscription is closed with
  `"invalid relay destination"`.
* **No foreign pubkey.** A `publish`/`publishEncrypted` template whose raw `event`
  carries a string `pubkey` other than the shell user's is refused with
  `ok: false, error: "policy denied"` instead of being re-stamped (NAP-POW: a mined event
  is signed verbatim or rejected; the template codec drops `pubkey`, so it is read from
  the raw JSON as `Req.publish … pk`).

Malformed requests: `relay.subscribe` with a string `subId` but a bad `id`, `filters` or
`relay` gets `relay.closed {subId, reason: "invalid relay subscription"}` (kehto's
string; there is no result envelope); `relay.publish`/`publishEncrypted` get
`{type: <type>.result, id, ok: false, error: "invalid request"}`; `relay.query` gets
`{type: relay.query.result, id, error: "invalid request"}`; `relay.close`, and any request
without a usable correlation field, gets nothing.

`filters` must be an array of JSON objects (NIP-01 filters, carried opaquely).

## Host operations

This component uses only core host calls; it adds no `Call.nap`, `Effect.nap`,
`HostEvent.nap` or `Call.prompt`.

* `Call.subscribe filters relays` (subscribe: `relays = some [relay]` when the napplet
  scoped it, else `none` = the shell's pool; query: `none`). Stream replies under one tag:
  `event ev relay` (signature already verified, NIP-01), one `eose`, `closed reason?`.
  Stopped with `Effect.unsubscribe`.
* `Call.sign unsigned` → `signed (some ev)` / `signed none`.
* `Call.encrypt scheme recipient plaintext` → `text (some ciphertext)` / `text none`
  (NIP-44 v2 or NIP-04; never another scheme).
* `Call.decrypt scheme ev` → `text (some plaintext)` / `text none`.
* `Call.publish ev none` → `published acks`; the result is `ok: true` iff some relay
  accepted, else `ok: false, error: "publish failed"`.
* `Effect.unsubscribe tag`, `Effect.cancel tag` on close, replacement and teardown.
-/

namespace Napplet.Run.Relay

/-- Shell policy for the relay domain. -/
structure Cfg where
  /-- Relay read ACL (subscribe, query). -/
  canRead : Identity → Bool := fun _ => true
  /-- Relay write ACL (publish, publishEncrypted). -/
  canWrite : Identity → Bool := fun _ => true
  /-- Validation of a napplet-scoped relay URL (SSRF guard). -/
  scopedAllowed : String → Bool := Net.relayAllowed
  /-- Attach `sidecar.relayHints` with the observed relay. -/
  relayHints : Bool := true

inductive Req where
  | subscribe (id subId : String) (filters : List Json) (relay : Option String)
  | close (id subId : String)
  /-- `pk`: the string `pubkey` member of the raw `event`, if any. -/
  | publish (id : String) (t : EventTemplate) (pk : Option String)
  | publishEncrypted (id : String) (t : EventTemplate) (recipient : String)
      (enc : Option Encryption) (pk : Option String)
  | query (id : String) (filters : List Json)
  deriving DecidableEq, Repr

/-- Well-formed request: every filter is a JSON object. -/
def Req.WF : Req → Prop
  | .subscribe _ _ fs _ => fs.all Json.isObj = true
  | .query _ fs => fs.all Json.isObj = true
  | _ => True

/-- Per-endpoint work in flight. Every entry is keyed by its host-call tag number. -/
inductive Job where
  /-- Live subscription; `eoseHeld` when EOSE arrived while stored events were still
  being decrypted. -/
  | sub (subId : String) (eoseHeld : Bool)
  /-- `relay.query` collecting results (event, relay hints); `eosed` after EOSE. -/
  | query (id : String) (acc : List (NostrEvent × List String)) (eosed : Bool)
  /-- Decrypting an event for the subscription or query with tag `parent`. -/
  | decrypt (parent : Nat) (ev : NostrEvent) (relay : String)
  | encrypt (id : String) (t : EventTemplate) (scheme : Encryption)
  | sign (id : String) (enc : Bool)
  | publish (id : String) (ev : NostrEvent) (enc : Bool)
  deriving DecidableEq, Repr

structure Entry where
  n : Nat
  job : Job
  deriving DecidableEq, Repr

abbrev Bucket := List Entry

structure St where
  cfg : Cfg
  /-- Per-endpoint buckets; a port has a bucket iff it has work in flight. -/
  buckets : List (PortId × Bucket)
  next : Nat

def St.init (cfg : Cfg := {}) : St := { cfg, buckets := [], next := 0 }

def St.bucket (s : St) (p : PortId) : Bucket :=
  ((s.buckets.find? (·.1 == p)).map (·.2)).getD []

/-- Replace port `p`'s bucket (removing it when empty). -/
def St.put (s : St) (p : PortId) (b : Bucket) : List (PortId × Bucket) :=
  if b.isEmpty then s.buckets.filter (·.1 != p)
  else if s.buckets.any (·.1 == p) then s.buckets.map fun x => (x.1, if x.1 == p then b else x.2)
  else (p, b) :: s.buckets

def tag (n : Nat) : CallTag := ⟨.relay, n⟩

/-! ### Messages -/

def resultJson (ev : NostrEvent) (hints : List String) : Json :=
  Json.mkObj [("event", some ev.toJson),
              ("sidecar", if hints.isEmpty then none else some (.obj [("relayHints", Json.strs hints)]))]

def eventMsg (sid : String) (ev : NostrEvent) (hints : List String) : Json :=
  Json.msg "relay.event" [("subId", some (.str sid)), ("result", some (resultJson ev hints))]

def eoseMsg (sid : String) : Json := Json.msg "relay.eose" [("subId", some (.str sid))]

def closedMsg (sid : String) (reason : Option String) : Json :=
  Json.msg "relay.closed" [("subId", some (.str sid)), ("reason", reason.map .str)]

def pubType (enc : Bool) : String :=
  if enc then "relay.publishEncrypted.result" else "relay.publish.result"

def pubOk (enc : Bool) (id : String) (ev : NostrEvent) : Json :=
  Json.msg (pubType enc) [("id", some (.str id)), ("ok", some (.bool true)),
    ("event", some ev.toJson), ("eventId", some (.str ev.id))]

def pubFail (enc : Bool) (id err : String) : Json :=
  Json.msg (pubType enc) [("id", some (.str id)), ("ok", some (.bool false)), ("error", some (.str err))]

def queryOk (id : String) (acc : List (NostrEvent × List String)) : Json :=
  Json.msg "relay.query.result"
    [("id", some (.str id)), ("events", some (.arr (acc.map fun x => resultJson x.1 x.2)))]

def queryFail (id err : String) : Json :=
  Json.msg "relay.query.result" [("id", some (.str id)), ("error", some (.str err))]

/-! ### Codec -/

def filtersOf? (j : Json) : Option (List Json) :=
  match j.get? "filters" with
  | some (.arr fs) => if fs.all Json.isObj then some fs else none
  | _ => none

def optStr? (j : Json) (k : String) : Option (Option String) :=
  match j.get? k with
  | none => some none
  | some (.str s) => some (some s)
  | some _ => none

def encOf? (j : Json) : Option (Option Encryption) :=
  match j.get? "encryption" with
  | none => some none
  | some (.str s) => (Encryption.ofName? s).map some
  | some _ => none

def templateOf? (j : Json) : Option EventTemplate := (j.get? "event").bind EventTemplate.ofJson?

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | none => .unknown
  | some t =>
    if t = "relay.subscribe" then
      match j.getStr? "subId" with
      | none => .reject []
      | some sid =>
        match reqId? j, filtersOf? j, optStr? j "relay" with
        | some id, some fs, some r => .ok (.subscribe id sid fs r)
        | _, _, _ => .reject [closedMsg sid (some "invalid relay subscription")]
    else if t = "relay.close" then
      match reqId? j, j.getStr? "subId" with
      | some id, some sid => .ok (.close id sid)
      | _, _ => .reject []
    else if t = "relay.publish" then
      match reqId? j with
      | none => .reject []
      | some id =>
        match templateOf? j with
        | some tp => .ok (.publish id tp ((j.get? "event").bind Net.claimedPubkey?))
        | none => .reject [pubFail false id "invalid request"]
    else if t = "relay.publishEncrypted" then
      match reqId? j with
      | none => .reject []
      | some id =>
        match templateOf? j, j.getStr? "recipient", encOf? j with
        | some tp, some rc, some e =>
          .ok (.publishEncrypted id tp rc e ((j.get? "event").bind Net.claimedPubkey?))
        | _, _, _ => .reject [pubFail true id "invalid request"]
    else if t = "relay.query" then
      match reqId? j with
      | none => .reject []
      | some id =>
        match filtersOf? j with
        | some fs => .ok (.query id fs)
        | none => .reject [queryFail id "invalid request"]
    else .unknown

def encodeReq : Req → Json
  | .subscribe id sid fs r => Json.msg "relay.subscribe"
      [("id", some (.str id)), ("subId", some (.str sid)), ("filters", some (.arr fs)),
       ("relay", r.map .str)]
  | .close id sid => Json.msg "relay.close" [("id", some (.str id)), ("subId", some (.str sid))]
  | .publish id t pk => Json.msg "relay.publish"
      [("id", some (.str id)), ("event", some (Net.withPubkey t.toJson pk))]
  | .publishEncrypted id t rc e pk => Json.msg "relay.publishEncrypted"
      [("id", some (.str id)), ("event", some (Net.withPubkey t.toJson pk)),
       ("recipient", some (.str rc)),
       ("encryption", e.map fun x => .str x.name)]
  | .query id fs => Json.msg "relay.query" [("id", some (.str id)), ("filters", some (.arr fs))]

/-! ### Bucket operations -/

def isSubOf (sid : String) (e : Entry) : Bool :=
  match e.job with
  | .sub s _ => s == sid
  | _ => false

def childOf (n : Nat) (e : Entry) : Bool :=
  match e.job with
  | .decrypt p _ _ => p == n
  | _ => false

def setJob (b : Bucket) (n : Nat) (j : Job) : Bucket :=
  b.map fun e => if e.n == n then ⟨e.n, j⟩ else e

/-- Remove the caller's subscription `sid` and its pending decryptions. -/
def stopSub (b : Bucket) (sid : String) : Bucket × List Eff :=
  let subs := b.filter (isSubOf sid)
  let gone (e : Entry) : Bool := isSubOf sid e || subs.any fun s => childOf s.n e
  (b.filter (fun e => !gone e),
   subs.map (fun s => .effect (.unsubscribe (tag s.n))) ++
   (b.filter fun e => !isSubOf sid e && gone e).map fun k => .effect (.cancel (tag k.n)))

def hintsOf (cfg : Cfg) (relay : String) : List String :=
  if cfg.relayHints && relay != "" then [relay] else []

/-- Add an event to a query's results, merging relay hints of duplicates by `id`. -/
def merge (acc : List (NostrEvent × List String)) (ev : NostrEvent) (hs : List String) :
    List (NostrEvent × List String) :=
  if acc.any (·.1.id == ev.id) then
    acc.map fun x => if x.1.id == ev.id then (x.1, x.2 ++ hs.filter (· ∉ x.2)) else x
  else acc ++ [(ev, hs)]

/-! ### Requests -/

/-- One request against the caller's bucket: new bucket, effects, next tag number. -/
def stepReq (h : Host) (w : World) (cx : Ctx) (cfg : Cfg) (nx : Nat) (b : Bucket) :
    Req → Bucket × List Eff × Nat
  | .subscribe _ sid fs r =>
    if !cfg.canRead cx.identity then (b, [.send cx.port (closedMsg sid (some "policy denied"))], nx)
    else if r.any (fun u => !cfg.scopedAllowed u) then
      (b, [.send cx.port (closedMsg sid (some "invalid relay destination"))], nx)
    else
      let st := stopSub b sid
      (⟨nx, .sub sid false⟩ :: st.1, st.2 ++ [.call (tag nx) (.subscribe fs (r.map ([·])))], nx + 1)
  | .close _ sid =>
    let st := stopSub b sid
    (st.1, st.2 ++ [.send cx.port (closedMsg sid none)], nx)
  | .publish id t pk =>
    if !cfg.canWrite cx.identity then (b, [.send cx.port (pubFail false id "policy denied")], nx)
    else if !Net.pubkeyOk w.user pk then (b, [.send cx.port (pubFail false id "policy denied")], nx)
    else if h.looksCiphertext t.content then
      (b, [.send cx.port (pubFail false id "blocked: ciphertext from napplet")], nx)
    else if w.user = "" then (b, [.send cx.port (pubFail false id "no signer configured")], nx)
    else (⟨nx, .sign id false⟩ :: b, [.call (tag nx) (.sign (t.stamp w.user w.now))], nx + 1)
  | .publishEncrypted id t rc e pk =>
    if !cfg.canWrite cx.identity then (b, [.send cx.port (pubFail true id "policy denied")], nx)
    else if !Net.pubkeyOk w.user pk then (b, [.send cx.port (pubFail true id "policy denied")], nx)
    else if h.looksCiphertext t.content then
      (b, [.send cx.port (pubFail true id "blocked: ciphertext from napplet")], nx)
    else if w.user = "" then (b, [.send cx.port (pubFail true id "no signer configured")], nx)
    else
      (⟨nx, .encrypt id t (e.getD .nip44)⟩ :: b,
       [.call (tag nx) (.encrypt (e.getD .nip44) rc t.content)], nx + 1)
  | .query id fs =>
    if !cfg.canRead cx.identity then (b, [.send cx.port (queryFail id "policy denied")], nx)
    else (⟨nx, .query id [] false⟩ :: b, [.call (tag nx) (.subscribe fs none)], nx + 1)

/-! ### Replies -/

/-- A decryption finished (`pt = none`: failed) for the entry `parent`. -/
def finishDecrypt (cfg : Cfg) (port : PortId) (rest : Bucket) (parent : Nat) (ev : NostrEvent)
    (relay : String) (pt : Option String) : Bucket × List Eff :=
  let hs := hintsOf cfg relay
  match rest.find? (·.n == parent) with
  | some ⟨_, .sub sid held⟩ =>
    let out := match pt with
      | some p => [Eff.send port (eventMsg sid { ev with content := p } hs)]
      | none => []
    if held && !rest.any (childOf parent) then
      (setJob rest parent (.sub sid false), out ++ [.send port (eoseMsg sid)])
    else (rest, out)
  | some ⟨_, .query id acc eosed⟩ =>
    let acc' := match pt with
      | some p => merge acc { ev with content := p } hs
      | none => acc
    if eosed && !rest.any (childOf parent) then
      (rest.filter (·.n != parent), [.send port (queryOk id acc')])
    else (setJob rest parent (.query id acc' eosed), [])
  | _ => (rest, [])

def cancels (b : Bucket) (n : Nat) : List Eff :=
  (b.filter (childOf n)).map fun k => .effect (.cancel (tag k.n))

/-- One host reply for entry `n` of `port`'s bucket `b`. -/
def stepReply (h : Host) (w : World) (cfg : Cfg) (nx : Nat) (port : PortId) (b : Bucket)
    (n : Nat) (rep : Reply) : Bucket × List Eff × Nat :=
  match b.find? (·.n == n) with
  | none => (b, [], nx)
  | some e =>
    let rest := b.filter (·.n != n)
    match e.job, rep with
    | .sub sid _, .event ev r =>
      match h.encryptedWith ev with
      | none => (b, [.send port (eventMsg sid ev (hintsOf cfg r))], nx)
      | some sc => (⟨nx, .decrypt n ev r⟩ :: b, [.call (tag nx) (.decrypt sc ev)], nx + 1)
    | .sub sid _, .eose =>
      if b.any (childOf n) then (setJob b n (.sub sid true), [], nx)
      else (b, [.send port (eoseMsg sid)], nx)
    | .sub sid _, .closed reason =>
      (rest.filter (fun k => !childOf n k), cancels b n ++ [.send port (closedMsg sid reason)], nx)
    | .query id acc false, .event ev r =>
      match h.encryptedWith ev with
      | none => (setJob b n (.query id (merge acc ev (hintsOf cfg r)) false), [], nx)
      | some sc => (⟨nx, .decrypt n ev r⟩ :: b, [.call (tag nx) (.decrypt sc ev)], nx + 1)
    | .query id acc false, .eose =>
      if b.any (childOf n) then
        (setJob b n (.query id acc true), [.effect (.unsubscribe (tag n))], nx)
      else (rest, [.effect (.unsubscribe (tag n)), .send port (queryOk id acc)], nx)
    | .query id _ false, .closed reason =>
      (rest.filter (fun k => !childOf n k),
       cancels b n ++ [.send port (queryFail id (reason.getD "relay query closed"))], nx)
    | .decrypt parent ev r, rep =>
      let pt := match rep with | .text t => t | _ => none
      let fd := finishDecrypt cfg port rest parent ev r pt
      (fd.1, fd.2, nx)
    | .encrypt id t _, .text (some ct) =>
      if w.user = "" then (rest, [.send port (pubFail true id "no signer configured")], nx)
      else (⟨nx, .sign id true⟩ :: rest,
            [.call (tag nx) (.sign ({ t with content := ct }.stamp w.user w.now))], nx + 1)
    | .encrypt id _ _, _ => (rest, [.send port (pubFail true id "encryption failed")], nx)
    | .sign id enc, .signed (some ev) =>
      (⟨nx, .publish id ev enc⟩ :: rest, [.call (tag nx) (.publish ev none)], nx + 1)
    | .sign id enc, _ => (rest, [.send port (pubFail enc id "signing failed")], nx)
    | .publish id ev enc, .published acks =>
      (rest, [.send port (if acks.any (·.2) then pubOk enc id ev else pubFail enc id "publish failed")], nx)
    | .publish id _ enc, _ => (rest, [.send port (pubFail enc id "publish failed")], nx)
    | _, _ => (b, [], nx)

/-! ### Component -/

def handle (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) : St × List Eff :=
  let o := stepReq h w cx s.cfg s.next (s.bucket cx.port) r
  ({ s with buckets := s.put cx.port o.1, next := o.2.2 }, o.2.1)

def onReply (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.buckets.find? (fun x => x.2.any (·.n == n)) with
  | none => (s, [])
  | some x =>
    let o := stepReply h w s.cfg s.next x.1 x.2 n rep
    ({ s with buckets := s.put x.1 o.1, next := o.2.2 }, o.2.1)

def onEvent (_h : Host) (_w : World) (s : St) (_e : HostEvent) : St × List Eff := (s, [])

/-- Teardown effects: stop live subscriptions, abandon every other outstanding call. -/
def dropEffs (b : Bucket) : List Eff :=
  b.filterMap fun e =>
    match e.job with
    | .sub .. => some (.effect (.unsubscribe (tag e.n)))
    | .query _ _ false => some (.effect (.unsubscribe (tag e.n)))
    | .query _ _ true => none
    | _ => some (.effect (.cancel (tag e.n)))

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with buckets := s.buckets.filter (·.1 != p) }, dropEffs (s.bucket p))

def mentions (s : St) (p : PortId) : Bool := s.buckets.any (·.1 == p)


/-! ### Endpoint bookkeeping -/

theorem mentions_put {s : St} {p q : PortId} {b : Bucket}
    (hm : (s.put p b).any (·.1 == q) = true) : mentions s q = true ∨ q = p := by
  unfold St.put at hm
  simp only [mentions]
  split at hm
  · simp only [List.any_filter, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq] at hm
    obtain ⟨x, hx, -, rfl⟩ := hm
    exact .inl (List.any_eq_true.mpr ⟨x, hx, by simp⟩)
  · split at hm
    · simp only [List.any_map, Function.comp_def] at hm
      exact .inl hm
    · simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at hm
      rcases hm with rfl | hm
      · exact .inr rfl
      · exact .inl hm

theorem decode_encodeReq (r : Req) (hr : r.WF) : decode (encodeReq r) = .ok r := by
  cases r with
  | subscribe id sid fs rl =>
    simp only [Req.WF] at hr
    cases rl <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
      Json.lookup, reqId?, filtersOf?, optStr?, hr]
  | close id sid => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
      Json.lookup, reqId?]
  | publish id t pk => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
      Json.lookup, reqId?, templateOf?, Net.ofJson?_withPubkey, Net.claimedPubkey?_withPubkey]
  | publishEncrypted id t rc e pk =>
    rcases e with _ | ⟨_ | _⟩ <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?,
      Json.get?, Json.lookup, reqId?, templateOf?, encOf?, Encryption.name, Encryption.ofName?,
      Net.ofJson?_withPubkey, Net.claimedPubkey?_withPubkey]
  | query id fs =>
    simp only [Req.WF] at hr
    simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?,
      filtersOf?, hr]

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp only [drop, mentions, List.any_filter, List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨x, hx, -, hq⟩ := h
  exact ⟨x, hx, hq⟩

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  rcases mentions_put hm with hm | rfl
  · exact .inl hm
  · exact .inr ⟨cx, hcx, rfl⟩

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  simp only [onReply] at hm
  split at hm
  · exact hm
  · rename_i x hx
    rcases mentions_put hm with hm | rfl
    · exact hm
    · exact List.any_eq_true.mpr ⟨x, List.mem_of_find?_eq_some hx, by simp⟩

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q :=
  .inl hm


/-! ### Properties (lifted from `Napplet.NapRelay`) -/

theorem finishDecrypt_sends {cfg : Cfg} {port : PortId} {rest : Bucket} {parent : Nat}
    {ev : NostrEvent} {r : String} {pt : Option String} {x : Eff}
    (hx : x ∈ (finishDecrypt cfg port rest parent ev r pt).2) : ∃ m, x = .send port m := by
  unfold finishDecrypt at hx
  repeat' (split at hx)
  all_goals (simp at hx <;> (try rcases hx with hx | hx) <;> (try subst hx) <;> exact ⟨_, rfl⟩)

theorem stepReply_publish {h : Host} {w : World} {cfg : Cfg} {nx : Nat} {port : PortId}
    {b : Bucket} {n : Nat} {rep : Reply} {t : CallTag} {ev : NostrEvent}
    {rs : Option (List String)}
    (hm : Eff.call t (.publish ev rs) ∈ (stepReply h w cfg nx port b n rep).2.1) :
    rep = .signed (some ev) ∧ rs = none := by
  unfold stepReply at hm
  split at hm
  · simp at hm
  · split at hm <;> (try split at hm) <;> (try split at hm) <;> simp_all [cancels]
    all_goals (obtain ⟨_, hc⟩ := finishDecrypt_sends hm; cases hc)


theorem onReply_publish_signed {h : Host} {w : World} {s : St} {n : Nat} {rep : Reply}
    {t : CallTag} {ev : NostrEvent} {rs : Option (List String)}
    (hm : Eff.call t (.publish ev rs) ∈ (onReply h w s n rep).2) :
    rep = .signed (some ev) ∧ rs = none := by
  simp only [onReply] at hm
  split at hm
  · simp at hm
  · exact stepReply_publish hm

/-- Requests never publish directly: every event the shell hands to its relay pool is
the signer's output (`onReply_publish_signed`); napplets never sign. -/
theorem handle_no_publish (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (t : CallTag)
    (ev : NostrEvent) (rs : Option (List String)) :
    Eff.call t (.publish ev rs) ∉ (handle h w cx s r).2 := by
  intro hm
  cases r <;> simp only [handle, stepReq, stopSub] at hm <;> (repeat' split at hm) <;> simp at hm

/-- A request is signed only if the endpoint may write, the template claims no pubkey
other than the user's, a user is signed in, and the napplet-supplied content does not
look like ciphertext (NIP-5D §Security 7). The unsigned event is the napplet's template
stamped with the user's key. -/
theorem handle_sign {h : Host} {w : World} {cx : Ctx} {s : St} {r : Req} {t : CallTag}
    {u : UnsignedEvent} (hm : Eff.call t (.sign u) ∈ (handle h w cx s r).2) :
    s.cfg.canWrite cx.identity = true ∧ h.looksCiphertext u.content = false ∧
      w.user ≠ "" ∧ ∃ id tp pk, r = .publish id tp pk ∧ Net.pubkeyOk w.user pk = true ∧
        u = tp.stamp w.user w.now := by
  cases r <;> simp only [handle, stepReq, stopSub] at hm <;> (repeat' split at hm) <;>
    simp at hm
  rename_i id tp pk hw hp hc hu
  obtain ⟨-, rfl⟩ := hm
  exact ⟨by simpa using hw, by simpa [EventTemplate.stamp] using hc, hu, id, tp, pk, rfl,
    by simpa using hp, rfl⟩

/-- `publishEncrypted`: the shell encrypts the napplet's plaintext itself, after
checking it is not ciphertext, that the endpoint may write and that the template claims
no foreign pubkey. -/
theorem handle_encrypt {h : Host} {w : World} {cx : Ctx} {s : St} {r : Req} {t : CallTag}
    {sc : Encryption} {rc pt : String} (hm : Eff.call t (.encrypt sc rc pt) ∈ (handle h w cx s r).2) :
    s.cfg.canWrite cx.identity = true ∧ h.looksCiphertext pt = false ∧
      ∃ id tp e pk, r = .publishEncrypted id tp rc e pk ∧ Net.pubkeyOk w.user pk = true ∧
        pt = tp.content ∧ sc = e.getD .nip44 := by
  cases r <;> simp only [handle, stepReq, stopSub] at hm <;> (repeat' split at hm) <;>
    simp at hm
  rename_i id tp rc' e pk hw hp hc _
  obtain ⟨-, rfl, rfl, rfl⟩ := hm
  exact ⟨by simpa using hw, by simpa using hc, id, tp, e, pk, rfl, by simpa using hp, rfl, rfl⟩

theorem stepReply_sign {h : Host} {w : World} {cfg : Cfg} {nx : Nat} {port : PortId}
    {b : Bucket} {n : Nat} {rep : Reply} {t : CallTag} {u : UnsignedEvent}
    (hm : Eff.call t (.sign u) ∈ (stepReply h w cfg nx port b n rep).2.1) :
    rep = .text (some u.content) ∧ w.user ≠ "" ∧ u.pubkey = w.user := by
  unfold stepReply at hm
  split at hm
  · simp at hm
  · split at hm <;> (try split at hm) <;> (try split at hm) <;>
      simp_all [cancels, EventTemplate.stamp]
    all_goals (obtain ⟨_, hc⟩ := finishDecrypt_sends hm; cases hc)

/-- Encrypt, then sign: the only signature requested while handling a host reply is over
content the host's `Call.encrypt` returned, never over napplet-supplied content. -/
theorem onReply_sign_encrypted {h : Host} {w : World} {s : St} {n : Nat} {rep : Reply}
    {t : CallTag} {u : UnsignedEvent} (hm : Eff.call t (.sign u) ∈ (onReply h w s n rep).2) :
    rep = .text (some u.content) ∧ w.user ≠ "" ∧ u.pubkey = w.user := by
  simp only [onReply] at hm
  split at hm
  · simp at hm
  · exact stepReply_sign hm

/-- Subscriptions and queries are opened only for endpoints with relay read access. -/
theorem handle_subscribe_read {h : Host} {w : World} {cx : Ctx} {s : St} {r : Req}
    {t : CallTag} {fs : List Json} {rs : Option (List String)}
    (hm : Eff.call t (.subscribe fs rs) ∈ (handle h w cx s r).2) :
    s.cfg.canRead cx.identity = true := by
  cases r <;> simp only [handle, stepReq, stopSub] at hm <;> (repeat' split at hm) <;>
    simp at hm <;> simp_all

/-! #### Delivery is plaintext -/

/-- The event carried by a `relay.event` message. -/
def evOf (m : Json) : Option NostrEvent :=
  ((m.get? "result").bind (·.get? "event")).bind NostrEvent.ofJson?

@[simp] theorem type_eventMsg (sid : String) (v : NostrEvent) (hs : List String) :
    (eventMsg sid v hs).getStr? "type" = some "relay.event" := by
  simp only [eventMsg, resultJson]; split <;>
    simp [Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

@[simp] theorem evOf_eventMsg (sid : String) (v : NostrEvent) (hs : List String) :
    evOf (eventMsg sid v hs) = some v := by
  simp only [eventMsg, resultJson]; split <;>
    simp [evOf, Json.msg, Json.mkObj, Json.get?, Json.lookup]

@[simp] theorem type_eoseMsg (sid : String) : (eoseMsg sid).getStr? "type" = some "relay.eose" := by
  simp [eoseMsg, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

@[simp] theorem type_closedMsg (sid : String) (r : Option String) :
    (closedMsg sid r).getStr? "type" = some "relay.closed" := by
  cases r <;> simp [closedMsg, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

@[simp] theorem type_pubOk (enc : Bool) (id : String) (ev : NostrEvent) :
    (pubOk enc id ev).getStr? "type" = some (pubType enc) := by
  simp [pubOk, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

@[simp] theorem type_pubFail (enc : Bool) (id e : String) :
    (pubFail enc id e).getStr? "type" = some (pubType enc) := by
  simp [pubFail, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

@[simp] theorem type_queryOk (id : String) (acc : List (NostrEvent × List String)) :
    (queryOk id acc).getStr? "type" = some "relay.query.result" := by
  simp [queryOk, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

@[simp] theorem type_queryFail (id e : String) :
    (queryFail id e).getStr? "type" = some "relay.query.result" := by
  simp [queryFail, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

theorem finishDecrypt_event {cfg : Cfg} {port q : PortId} {rest : Bucket} {parent : Nat}
    {ev : NostrEvent} {r : String} {pt : Option String} {m : Json}
    (hm : Eff.send q m ∈ (finishDecrypt cfg port rest parent ev r pt).2)
    (ht : m.getStr? "type" = some "relay.event") :
    ∃ p, pt = some p ∧ evOf m = some { ev with content := p } := by
  unfold finishDecrypt at hm
  repeat' (split at hm)
  all_goals (simp at hm <;> (try rcases hm with hm | hm) <;> (try obtain ⟨-, rfl⟩ := hm) <;>
    simp_all)

theorem stepReply_event {h : Host} {w : World} {cfg : Cfg} {nx : Nat} {port q : PortId}
    {b : Bucket} {n : Nat} {rep : Reply} {m : Json}
    (hm : Eff.send q m ∈ (stepReply h w cfg nx port b n rep).2.1)
    (ht : m.getStr? "type" = some "relay.event") :
    ∃ v, evOf m = some v ∧
      ((∃ r, rep = .event v r ∧ h.encryptedWith v = none) ∨ rep = .text (some v.content)) := by
  unfold stepReply at hm
  split at hm
  · simp at hm
  · split at hm <;> (try split at hm) <;> (try split at hm)
    all_goals first
      | (obtain ⟨p, hp, hv⟩ := finishDecrypt_event hm ht
         refine ⟨_, hv, .inr ?_⟩
         rename_i rep' _ _ _ _ _
         cases rep' <;> simp_all)
      | (simp [cancels] at hm <;> (try rcases hm with hm | hm) <;>
          (try obtain ⟨-, rfl⟩ := hm) <;> simp_all [pubType] <;> (repeat' split at ht) <;> simp_all)

/-- Napplets receive plaintext: every `relay.event` the shell sends carries either an
event that is not encrypted to the user, delivered as received, or an event whose
`content` is exactly what the host's decryption returned. An undecryptable event
(`text none`) is never delivered. -/
theorem onReply_delivers_plaintext {h : Host} {w : World} {s : St} {n : Nat} {rep : Reply}
    {q : PortId} {m : Json} (hm : Eff.send q m ∈ (onReply h w s n rep).2)
    (ht : m.getStr? "type" = some "relay.event") :
    ∃ v, evOf m = some v ∧
      ((∃ r, rep = .event v r ∧ h.encryptedWith v = none) ∨ rep = .text (some v.content)) := by
  simp only [onReply] at hm
  split at hm
  · simp at hm
  · exact stepReply_event hm ht

/-- No delivered event ever carries pre-resolved sidecar resources (pre-resolution is
off by default and never performed). -/
theorem resultJson_no_resources (ev : NostrEvent) (hs : List String) :
    ((resultJson ev hs).get? "sidecar").bind (·.get? "resources") = none := by
  unfold resultJson; split <;> simp [Json.mkObj, Json.get?, Json.lookup]

/-! #### Subscriptions are per endpoint -/

theorem mem_put_of_ne {s : St} {p : PortId} {b : Bucket} {x : PortId × Bucket}
    (hx : x ∈ s.buckets) (hne : x.1 ≠ p) : x ∈ s.put p b := by
  unfold St.put
  split
  · simp [hx, hne]
  · split
    · exact List.mem_map.mpr ⟨x, hx, by simp [hne]⟩
    · exact List.mem_cons_of_mem _ hx

theorem put_self {s : St} {p : PortId} {b : Bucket} {x : PortId × Bucket}
    (hx : x ∈ s.put p b) (hp : x.1 = p) : x.2 = b := by
  unfold St.put at hx
  split at hx
  · simp at hx; exact absurd hp hx.2
  · split at hx
    · simp at hx; obtain ⟨a, c, -, rfl⟩ := hx; simp at hp; simp [hp]
    · rename_i hany
      simp at hx
      rcases hx with rfl | hx
      · rfl
      · simp at hany; subst hp; exact absurd hx (hany x.2)

/-- `relay.close` leaves every other endpoint's state untouched. -/
theorem close_only_own (h : Host) (w : World) (cx : Ctx) (s : St) (id sid : String)
    {x : PortId × Bucket} (hx : x ∈ s.buckets) (hne : x.1 ≠ cx.port) :
    x ∈ (handle h w cx s (.close id sid)).1.buckets :=
  mem_put_of_ne hx hne

/-- After `relay.close sid`, the caller holds no subscription `sid`, so later pool events
for it find no entry and are dropped. -/
theorem close_stops (h : Host) (w : World) (cx : Ctx) (s : St) (id sid : String)
    {x : PortId × Bucket} (hx : x ∈ (handle h w cx s (.close id sid)).1.buckets)
    (hp : x.1 = cx.port) : ∀ e ∈ x.2, isSubOf sid e = false := by
  have := put_self hx hp
  intro e he
  rw [this] at he
  simp only [stepReq, stopSub, List.mem_filter] at he
  simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true'] at he
  exact he.2.1


/-! ### Vectors (upstream examples, NAP-RELAY @ 9f30b350) -/

section Vectors

def vHost : Host where
  crypto := { sha256 := fun _ => "", verifySig := fun _ => true }
  verifyEvent := fun _ => true
  sniff := fun _ => "application/octet-stream"
  rasterize := fun _ => none
  looksCiphertext := fun c => (c.splitOn "?iv=").length > 1
  encryptedWith := fun e => if e.kind = 4 then some .nip04 else none
  transform := id

def vCtx : Ctx :=
  { port := 7, window := 1, identity := { dTag := some "feed", artifactHash := "h" },
    exposed := [.relay], inst := 0 }

def vWorld : World := { now := 1700000000, live := [vCtx], user := "def..." }

def sends (effs : List Eff) : List Json := effs.filterMap fun | .send _ m => some m | _ => none

/-- Run a request, then a sequence of host replies `(n, reply)`; all effects in order. -/
def run (s : St) (j : Json) (replies : List (Nat × Reply)) : St × List Eff :=
  match decode j with
  | .ok r =>
    let (s1, e1) := handle vHost vWorld vCtx s r
    replies.foldl (fun (acc : St × List Eff) (nr : Nat × Reply) =>
      let (s2, e2) := onReply vHost vWorld acc.1 nr.1 nr.2
      (s2, acc.2 ++ e2)) (s1, e1)
  | _ => (s, [])

def evJ (text : String) : NostrEvent := (NostrEvent.ofJson? (Json.parse! text)).getD default

def subReq : String :=
  "{ \"type\": \"relay.subscribe\", \"id\": \"a1\", \"subId\": \"sub-1\", \"filters\": [{ \"kinds\": [1], \"limit\": 50 }] }"
def ev1 : NostrEvent :=
  evJ "{ \"id\": \"abc...\", \"pubkey\": \"def...\", \"kind\": 1, \"content\": \"hello\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }"

#guard decode (Json.parse! subReq) matches .ok (.subscribe "a1" "sub-1" [_] none)

-- Subscribe: one host subscription, then `relay.event` (with relay hint) and `relay.eose`.
#guard (run (St.init) (Json.parse! subReq) []).2 ==
  [.call (tag 0) (.subscribe [Json.parse! "{ \"kinds\": [1], \"limit\": 50 }"] none)]
#guard match sends (run (St.init) (Json.parse! subReq)
    [(0, .event ev1 "wss://relay.example.com"), (0, .eose)]).2 with
  | [a, b] =>
    Json.same a (Json.parse! "{ \"type\": \"relay.event\", \"subId\": \"sub-1\", \"result\": { \"event\": { \"id\": \"abc...\", \"pubkey\": \"def...\", \"kind\": 1, \"content\": \"hello\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }, \"sidecar\": { \"relayHints\": [\"wss://relay.example.com\"] } } }") &&
    Json.same b (Json.parse! "{ \"type\": \"relay.eose\", \"subId\": \"sub-1\" }")
  | _ => false

-- Publish: the shell stamps and signs the template, publishes the signed event, replies.
def pubReq : String :=
  "{ \"type\": \"relay.publish\", \"id\": \"b2\", \"event\": { \"kind\": 1, \"content\": \"hello world\", \"tags\": [], \"created_at\": 1234567890 } }"
def ev2 : NostrEvent :=
  evJ "{ \"id\": \"abc...\", \"pubkey\": \"def...\", \"kind\": 1, \"content\": \"hello world\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"ghi...\" }"
#guard (run (St.init) (Json.parse! pubReq) []).2 ==
  [.call (tag 0) (.sign { pubkey := "def...", createdAt := 1234567890, kind := 1, tags := [], content := "hello world" })]
#guard (run (St.init) (Json.parse! pubReq) [(0, .signed (some ev2))]).2.getLast? ==
  some (.call (tag 1) (.publish ev2 none))
#guard match sends (run (St.init) (Json.parse! pubReq)
    [(0, .signed (some ev2)), (1, .published [("wss://relay.example.com", true)])]).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"relay.publish.result\", \"id\": \"b2\", \"ok\": true, \"event\": { \"id\": \"abc...\", \"pubkey\": \"def...\", \"kind\": 1, \"content\": \"hello world\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"ghi...\" }, \"eventId\": \"abc...\" }")
  | _ => false

-- Publish encrypted: the shell encrypts (NIP-44), then signs the ciphertext, then publishes.
def peReq : String :=
  "{ \"type\": \"relay.publishEncrypted\", \"id\": \"f6\", \"event\": { \"kind\": 4, \"content\": \"secret message\", \"tags\": [[\"p\", \"recipient...\"]], \"created_at\": 1234567890 }, \"recipient\": \"recipient...\", \"encryption\": \"nip44\" }"
def ev3 : NostrEvent :=
  evJ "{ \"id\": \"enc...\", \"pubkey\": \"def...\", \"kind\": 4, \"content\": \"encrypted...\", \"tags\": [[\"p\", \"recipient...\"]], \"created_at\": 1234567890, \"sig\": \"...\" }"
#guard (run (St.init) (Json.parse! peReq) []).2 ==
  [.call (tag 0) (.encrypt .nip44 "recipient..." "secret message")]
#guard (run (St.init) (Json.parse! peReq) [(0, .text (some "encrypted..."))]).2.getLast? ==
  some (.call (tag 1) (.sign { pubkey := "def...", createdAt := 1234567890, kind := 4, tags := [["p", "recipient..."]], content := "encrypted..." }))
#guard match sends (run (St.init) (Json.parse! peReq)
    [(0, .text (some "encrypted...")), (1, .signed (some ev3)), (2, .published [("wss://r", true)])]).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"relay.publishEncrypted.result\", \"id\": \"f6\", \"ok\": true, \"event\": { \"id\": \"enc...\", \"pubkey\": \"def...\", \"kind\": 4, \"content\": \"encrypted...\", \"tags\": [[\"p\", \"recipient...\"]], \"created_at\": 1234567890, \"sig\": \"...\" }, \"eventId\": \"enc...\" }")
  | _ => false

-- Query: subscribe, collect until EOSE, close, reply.
def qReq : String :=
  "{ \"type\": \"relay.query\", \"id\": \"c3\", \"filters\": [{ \"authors\": [\"def...\"], \"kinds\": [0], \"limit\": 1 }] }"
def ev4 : NostrEvent :=
  evJ "{ \"id\": \"xyz...\", \"pubkey\": \"def...\", \"kind\": 0, \"content\": \"{...}\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }"
#guard (run (St.init) (Json.parse! qReq) [(0, .event ev4 "wss://relay.example.com"), (0, .eose)]).2.take 2 ==
  [.call (tag 0) (.subscribe [Json.parse! "{ \"authors\": [\"def...\"], \"kinds\": [0], \"limit\": 1 }"] none),
   .effect (.unsubscribe (tag 0))]
#guard match sends (run (St.init) (Json.parse! qReq)
    [(0, .event ev4 "wss://relay.example.com"), (0, .event ev4 "wss://relay.example.com"), (0, .eose)]).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"relay.query.result\", \"id\": \"c3\", \"events\": [{ \"event\": { \"id\": \"xyz...\", \"pubkey\": \"def...\", \"kind\": 0, \"content\": \"{...}\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }, \"sidecar\": { \"relayHints\": [\"wss://relay.example.com\"] } }] }")
  | _ => false

-- Close: the subscription is stopped and `relay.closed` confirms it (modelling decision 9).
#guard
  let s1 := (run (St.init) (Json.parse! subReq) []).1
  let (s2, effs) := run s1 (Json.parse! "{ \"type\": \"relay.close\", \"id\": \"d4\", \"subId\": \"sub-1\" }") []
  effs.length == 2 && effs.head? == some (.effect (.unsubscribe (tag 0))) &&
  (match sends effs with
   | [m] => Json.same m (Json.parse! "{ \"type\": \"relay.closed\", \"subId\": \"sub-1\" }")
   | _ => false) &&
  (onReply vHost vWorld s2 0 (.event ev1 "wss://relay.example.com")).2.isEmpty &&
  !mentions s2 7

-- Scoped relay.
#guard (run (St.init) (Json.parse! "{ \"type\": \"relay.subscribe\", \"id\": \"e5\", \"subId\": \"sub-2\", \"filters\": [{ \"kinds\": [9, 10, 11, 12] }], \"relay\": \"wss://groups.example.com\" }") []).2 ==
  [.call (tag 0) (.subscribe [Json.parse! "{ \"kinds\": [9, 10, 11, 12] }"] (some ["wss://groups.example.com"]))]

-- Error shape.
#guard Json.same (pubFail false "b2" "blocked: content policy violation")
  (Json.parse! "{ \"type\": \"relay.publish.result\", \"id\": \"b2\", \"ok\": false, \"error\": \"blocked: content policy violation\" }")

-- Napplet-supplied ciphertext is never signed.
#guard match (run (St.init) (Json.parse! "{ \"type\": \"relay.publish\", \"id\": \"x\", \"event\": { \"kind\": 4, \"content\": \"YWJj?iv=ZGVm\" } }") []).2 with
  | [.send 7 m] => Json.same m (Json.parse! "{ \"type\": \"relay.publish.result\", \"id\": \"x\", \"ok\": false, \"error\": \"blocked: ciphertext from napplet\" }")
  | _ => false

-- An incoming encrypted event is decrypted before delivery; EOSE waits for it.
def ev5 : NostrEvent :=
  evJ "{ \"id\": \"dm...\", \"pubkey\": \"abc...\", \"kind\": 4, \"content\": \"Q0lQ?iv=SVY=\", \"tags\": [], \"created_at\": 1, \"sig\": \"...\" }"
#guard
  let effs := (run (St.init) (Json.parse! subReq) [(0, .event ev5 "wss://r"), (0, .eose)]).2
  effs == [.call (tag 0) (.subscribe [Json.parse! "{ \"kinds\": [1], \"limit\": 50 }"] none),
           .call (tag 1) (.decrypt .nip04 ev5)]
#guard match sends (run (St.init) (Json.parse! subReq)
    [(0, .event ev5 "wss://r"), (0, .eose), (1, .text (some "hi"))]).2 with
  | [a, b] => Json.same a (eventMsg "sub-1" { ev5 with content := "hi" } ["wss://r"]) &&
      Json.same b (Json.parse! "{ \"type\": \"relay.eose\", \"subId\": \"sub-1\" }")
  | _ => false
#guard match sends (run (St.init) (Json.parse! subReq)
    [(0, .event ev5 "wss://r"), (0, .eose), (1, .text none)]).2 with
  | [b] => Json.same b (Json.parse! "{ \"type\": \"relay.eose\", \"subId\": \"sub-1\" }")
  | _ => false

-- Malformed and unknown requests.
#guard decode (Json.parse! "{ \"type\": \"relay.count\", \"id\": \"z\" }") matches .unknown
#guard match decode (Json.parse! "{ \"type\": \"relay.query\", \"id\": \"q\", \"filters\": {} }") with
  | .reject [m] => Json.same m (Json.parse! "{ \"type\": \"relay.query.result\", \"id\": \"q\", \"error\": \"invalid request\" }")
  | _ => false
#guard match decode (Json.parse! "{ \"type\": \"relay.subscribe\", \"subId\": \"s\", \"filters\": [] }") with
  | .reject [m] => Json.same m (Json.parse! "{ \"type\": \"relay.closed\", \"subId\": \"s\", \"reason\": \"invalid relay subscription\" }")
  | _ => false
#guard decode (Json.parse! "{ \"type\": \"relay.close\", \"subId\": \"s\" }") matches .reject []

-- Teardown stops the subscription.
#guard (drop (run (St.init) (Json.parse! subReq) []).1 7).2 == [.effect (.unsubscribe (tag 0))]

-- A template claiming a pubkey other than the user's is refused, not re-stamped (NAP-POW).
#guard match sends (run (St.init) (Json.parse! "{ \"type\": \"relay.publish\", \"id\": \"b3\", \"event\": { \"kind\": 1, \"content\": \"x\", \"pubkey\": \"other...\" } }") []).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"relay.publish.result\", \"id\": \"b3\", \"ok\": false, \"error\": \"policy denied\" }")
  | _ => false
#guard match sends (run (St.init) (Json.parse! "{ \"type\": \"relay.publishEncrypted\", \"id\": \"f7\", \"event\": { \"kind\": 4, \"content\": \"x\", \"pubkey\": \"other...\" }, \"recipient\": \"r...\" }") []).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"relay.publishEncrypted.result\", \"id\": \"f7\", \"ok\": false, \"error\": \"policy denied\" }")
  | _ => false
-- The user's own pubkey is accepted and signed as usual.
#guard (run (St.init) (Json.parse! "{ \"type\": \"relay.publish\", \"id\": \"b4\", \"event\": { \"kind\": 1, \"content\": \"x\", \"created_at\": 5, \"pubkey\": \"def...\" } }") []).2 ==
  [.call (tag 0) (.sign { pubkey := "def...", createdAt := 5, kind := 1, tags := [], content := "x" })]
#guard decode (Json.parse! "{ \"type\": \"relay.publish\", \"id\": \"b4\", \"event\": { \"kind\": 1, \"pubkey\": \"def...\" } }") matches
  .ok (.publish "b4" { kind := 1, content := "", tags := [], createdAt := none } (some "def..."))

-- Scoped relays must pass `Net.relayAllowed`: no private or localhost relay.
#guard ["wss://127.0.0.1", "wss://localhost:7777", "wss://[::1]", "wss://192.168.1.2", "ws://relay.example.com"].all fun u =>
  match sends (run (St.init) (Json.parse! ("{ \"type\": \"relay.subscribe\", \"id\": \"a2\", \"subId\": \"s2\", \"filters\": [{}], \"relay\": \"" ++ u ++ "\" }")) []).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"relay.closed\", \"subId\": \"s2\", \"reason\": \"invalid relay destination\" }")
  | _ => false
#guard (run (St.init) (Json.parse! "{ \"type\": \"relay.subscribe\", \"id\": \"a3\", \"subId\": \"s3\", \"filters\": [{}], \"relay\": \"wss://groups.example.com\" }") []).2 ==
  [.call (tag 0) (.subscribe [Json.parse! "{}"] (some ["wss://groups.example.com"]))]

end Vectors

end Napplet.Run.Relay
