/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Intent

/-!
# NAP-INTENT runtime component

Upstream: `napplet/naps` `master`, `naps/NAP-INTENT.md` at `377bf939`.

Wire (napplet → runtime): `intent.invoke {id, request}`, `intent.available {id, archetype}`,
`intent.handlers {id}`. Wire (runtime → napplet): `intent.invoke.result {id, result}`,
`intent.available.result {id, availability, error?}`, `intent.handlers.result {id, handlers, error?}`,
pushes `intent.changed {availability}` and `intent.deliver {delivery}` (no `id`).

`request` is an `IntentRequest` `{archetype, action, convention, payload?, handler?,
handlerHint?: {address, relays?}, behavior?: {focus?, reuse?}}`; members the schema
does not define (for example a forged `sender`) are ignored.

## Catalog

The installed catalog is shell state fed by the host (`HostEvent.nap .intent "catalog"`):
one entry per verified installed manifest, carrying its catalog id, optional title and
the raw values of its `z` and `i` tags. The runtime derives everything else here, per
NAP-INTENT §Manifest Catalog Contract:

* a contract for role `r` is an `i` tag whose convention parses as
  `napplet:<r>/<action>` (`NapIntent.validIdent`) on an entry that also has `["z", r]`;
  its `params` are the tag's remaining values; tag order is irrelevant;
* a candidate for `r` is an entry with at least one such contract; its `conventions`
  and `actions` are derived from its contracts without duplicates;
* `handlers()` covers every role that has a candidate.

User defaults (one per archetype) are shell state fed by `HostEvent.nap .intent
"default"`. No napplet request changes the catalog or the defaults
(`handle_prefs_unchanged`).

## Invocation

1. `request` fields of the wrong JSON type: `{ok: false, error: "invalid convention"}`.
   `convention` must be exactly `napplet:<archetype>/<action>` with valid name
   segments, else `"invalid convention"`.
2. No candidate for the archetype: `"no handler"`. Candidates, none of which has a
   contract with exactly this convention: `"unsupported convention"`.
3. Selection (`NapIntent.resolve` precedence) among the compatible candidates:
   * an explicit catalog id must be compatible (else `"invoke rejected"`) and the user
     must authorize addressing it (`Call.prompt .intent "authorize"`; refusal →
     `"invoke rejected"`);
   * `"choose"` asks the user (`Call.prompt .intent "choose"`; cancel → `"user cancelled"`);
   * absent / `"default"`: the user's default if compatible, else a usable
     `handlerHint` (its `address` maps to catalog id `nip5d:<address>`, which must be a
     compatible candidate and `Cfg.hints` on), else the only compatible candidate,
     else the chooser prompt.
4. Acceptance sends `{ok: true, archetype, action, convention, handler}` first, then
   delivers `intent.deliver` to a live endpoint whose `Ctx.catalogId` is the handler
   and which has `intent` exposed. With none, the delivery is retained (independently
   of the source; not per-endpoint state) and `Effect.nap .intent "launch"` asks the
   host to start the handler; `flush` delivers retained deliveries once a target is
   live (`Runtime` calls it after every bind). `delivery.sender` is the source's
   `Ctx.catalogId`.

Malformed `intent.available` (non-string `archetype`) with a string `id` gets
`{id, availability: {archetype: "", available: false, candidates: [], hasDefault: false},
error: "invalid request"}` (the result requires `availability`). Any malformed message
without a string `id` is dropped.
-/

/-! ## Host operations

* `HostEvent.nap .intent "catalog" {"entries": [Entry]}` where
  `Entry = {"id": text, "title"?: text, "z": [text], "i": [[text, ...]]}`. The complete
  installed catalog, replacing the previous one. Contract: one entry per verified
  installed NIP-5D napplet manifest (kinds 5129, 15129, 35129; signature and artifact
  verified per NIP-5D); `id` is that manifest's catalog id exactly as
  `Identity.catalogId` computes it (`nip5d:35129:<pubkey>:<d>`, `nip5d:15129:<pubkey>`,
  `nip5d:5129:<event id>`), so it equals `Ctx.catalogId` of the running napplet;
  `title` is the manifest's title, if any; `z` lists the values of its `z` tags and `i`
  the full value lists (after the tag name) of its `i` tags, in tag order. The host
  sends it at start-up and whenever the installed set changes. A malformed payload is
  ignored. The runtime pushes `intent.changed` for every role whose availability changed.
* `HostEvent.nap .intent "default" {"archetype": text, "handler": text | null}`: the user
  set (or, with `null` / absent `handler`, cleared) the default handler for an
  archetype. Contract: only the user (shell UI or settings) causes it; the value is
  persistent user preference (`Host.lean` §Persistence) and is re-sent at start-up.
  The runtime pushes `intent.changed` for that archetype if its availability changed.
* `HostEvent.nap .intent "launchFailed" {"handler": text}`: the host could not start a
  napplet for that catalog id (not installed, refused by policy, load rejected, or the
  loaded napplet does not have `intent` exposed). Terminal failure: the runtime discards
  the retained deliveries for that handler. Nothing is reported to the source.
* `Effect.nap .intent "launch" {"handler": text, "behavior"?: {"focus"?: bool, "reuse"?: bool}}`:
  start the napplet whose verified catalog id is `handler`, through the ordinary NIP-5D
  load (`Input.create` … `Input.hello`), honouring `behavior` as hints. Emitted once per
  handler while deliveries for it are retained. Once the napplet is bound with `intent`
  exposed, the runtime delivers. If it cannot be started, the host sends `launchFailed`.
* `Effect.nap .intent "focus" {"window": number}`: `behavior.focus` was `true` and the
  delivery went to the already running napplet in that window; bring its surface
  forward if workspace policy allows. A hint; ignoring it is valid.
* `Call.prompt .intent "choose" {"sender": text, "archetype": text, "action": text,
  "convention": text, "candidates": [IntentCandidate]}` → `Reply.decision allowed choice`.
  Ask the user to pick a handler among `candidates` (NAP-INTENT `IntentCandidate`
  JSON). `allowed = true` with `choice = some <candidate id>` selects it; `allowed =
  false` or no choice means cancelled (`"user cancelled"`). A choice that is no longer a
  compatible candidate when the reply arrives yields `"invoke rejected"`.
* `Call.prompt .intent "authorize" {"sender": text, "handler": text, "archetype": text,
  "action": text, "convention": text}` → `Reply.decision allowed _`. Ask the user whether
  the source (`sender`, its catalog id) may address the installed handler `handler`
  explicitly (NAP-INTENT: "MUST NOT let a caller address a handler instance unless the
  user explicitly authorized that handler"). The host may answer from a rule the user
  configured. `allowed = false` yields `"invoke rejected"`.

A prompt reply other than `decision` counts as a refusal / cancellation. Prompts of a
torn-down source are cancelled with `Effect.cancel`.
-/

namespace Napplet.Run.Intent

open NapIntent

/-- Shell intent policy. -/
structure Cfg where
  /-- Consider `handlerHint` recommendations (resolution step 3). -/
  hints : Bool := true

/-! ### Catalog -/

/-- One installed manifest as the host reports it. -/
structure Entry where
  id : String
  title : Option String
  /-- `z` tag values. -/
  roles : List String
  /-- `i` tag values: convention followed by advertised parameter names. -/
  intents : List (List String)
  deriving DecidableEq, Repr

structure Contract where
  convention : String
  params : List String
  deriving DecidableEq, Repr

structure Candidate where
  id : String
  title : Option String
  contracts : List Contract
  isDefault : Bool
  deriving DecidableEq, Repr

def dedupStr (l : List String) : List String :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- `napplet:<archetype>/<action>` → `(archetype, action)`. -/
def parseConv (c : String) : Option (String × String) :=
  if validIdent c.toList then
    match splitFirst '/' (c.toList.drop 8) with
    | (a, some b) => some (String.ofList a, String.ofList b)
    | _ => none
  else none

/-- Eligible contracts of an entry for role `r`, first contract per convention. -/
def Entry.contracts (e : Entry) (r : String) : List Contract :=
  if r ∈ e.roles then
    (e.intents.filterMap fun t =>
      match t with
      | c :: ps =>
        match parseConv c with
        | some (a, _) => if a = r then some (Contract.mk c ps) else none
        | none => none
      | [] => none).foldl
      (fun acc c => if acc.any (·.convention == c.convention) then acc else acc ++ [c]) []
  else []

def Candidate.conventions (c : Candidate) : List String := dedupStr (c.contracts.map (·.convention))

def Candidate.actions (c : Candidate) : List String :=
  dedupStr (c.conventions.filterMap fun v => (parseConv v).map (·.2))

structure Behavior where
  focus : Option Bool := none
  reuse : Option Bool := none
  deriving DecidableEq, Repr

structure Hint where
  address : String
  relays : Option (List String) := none
  deriving DecidableEq, Repr

structure Request where
  archetype : String
  action : String
  convention : String
  payload : Option Json := none
  handler : Option String := none
  hint : Option Hint := none
  behavior : Option Behavior := none
  deriving DecidableEq, Repr

/-- An accepted, normalized delivery. `handler` is routing data, never sent. -/
structure Delivery where
  handler : String
  sender : String
  archetype : String
  action : String
  convention : String
  payload : Option Json
  behavior : Option Behavior
  deriving DecidableEq, Repr

/-- A source waiting on a prompt. -/
structure Pending where
  n : Nat
  port : PortId
  id : String
  sender : String
  req : Request
  sel : Selection
  deriving DecidableEq, Repr

structure St where
  cfg : Cfg
  catalog : List Entry
  /-- User default handler per archetype (persistent user preference). -/
  defaults : List (String × String)
  pending : List Pending
  /-- Accepted deliveries waiting for a live target (not per-endpoint). -/
  queue : List Delivery
  next : Nat

def St.init (cfg : Cfg := {}) : St := ⟨cfg, [], [], [], [], 0⟩

def St.defaultFor (s : St) (r : String) : Option String :=
  (s.defaults.find? (·.1 == r)).map (·.2)

def candidates (s : St) (r : String) : List Candidate :=
  s.catalog.filterMap fun e =>
    let cs := e.contracts r
    if cs.isEmpty then none else some ⟨e.id, e.title, cs, s.defaultFor r == some e.id⟩

/-- Every role with at least one candidate. -/
def roles (s : St) : List String :=
  dedupStr (s.catalog.flatMap fun e => e.roles.filter fun r => !(e.contracts r).isEmpty)

def compatible (s : St) (r : Request) : List Candidate :=
  (candidates s r.archetype).filter fun c => c.contracts.any (·.convention == r.convention)

/-! ### JSON -/

def contractJson (c : Contract) : Json :=
  .obj [("convention", .str c.convention), ("params", Json.strs c.params)]

def candidateJson (c : Candidate) : Json :=
  Json.mkObj
    [("id", some (.str c.id)), ("title", c.title.map .str),
     ("actions", some (Json.strs c.actions)), ("conventions", some (Json.strs c.conventions)),
     ("contracts", some (.arr (c.contracts.map contractJson))),
     ("isDefault", if c.isDefault then some (.bool true) else none)]

def availJson (s : St) (r : String) : Json :=
  let cs := candidates s r
  .obj [("archetype", .str r), ("available", .bool !cs.isEmpty),
        ("candidates", .arr (cs.map candidateJson)), ("hasDefault", .bool (cs.any (·.isDefault)))]

def optField {α : Type} (j : Json) (k : String) (f : Json → Option α) : Option (Option α) :=
  match j.get? k with
  | none => some none
  | some v => (f v).map some

def behaviorJson (b : Behavior) : Json :=
  Json.mkObj [("focus", b.focus.map .bool), ("reuse", b.reuse.map .bool)]

def behaviorOf? (j : Json) : Option Behavior :=
  if j.isObj then do
    some { focus := ← optField j "focus" Json.asBool?, reuse := ← optField j "reuse" Json.asBool? }
  else none

def hintJson (h : Hint) : Json :=
  Json.mkObj [("address", some (.str h.address)), ("relays", h.relays.map Json.strs)]

def hintOf? (j : Json) : Option Hint := do
  some { address := ← j.getStr? "address", relays := ← optField j "relays" Json.asStrs? }

def requestJson (r : Request) : Json :=
  Json.mkObj
    [("archetype", some (.str r.archetype)), ("action", some (.str r.action)),
     ("convention", some (.str r.convention)), ("payload", r.payload),
     ("handler", r.handler.map .str), ("handlerHint", r.hint.map hintJson),
     ("behavior", r.behavior.map behaviorJson)]

def requestOf? (j : Json) : Option Request := do
  some { archetype := ← j.getStr? "archetype", action := ← j.getStr? "action",
         convention := ← j.getStr? "convention", payload := j.get? "payload",
         handler := ← optField j "handler" Json.asStr?,
         hint := ← optField j "handlerHint" hintOf?,
         behavior := ← optField j "behavior" behaviorOf? }

def deliveryJson (d : Delivery) : Json :=
  Json.mkObj
    [("sender", some (.str d.sender)), ("archetype", some (.str d.archetype)),
     ("action", some (.str d.action)), ("convention", some (.str d.convention)),
     ("payload", d.payload)]

def deliverJson (d : Delivery) : Json := Json.msg "intent.deliver" [("delivery", some (deliveryJson d))]

def okJson (id : String) (d : Delivery) : Json :=
  Json.msg "intent.invoke.result"
    [("id", some (.str id)),
     ("result", some (.obj [("ok", .bool true), ("archetype", .str d.archetype),
       ("action", .str d.action), ("convention", .str d.convention), ("handler", .str d.handler)]))]

def invokeErr (id err : String) : Json :=
  Json.msg "intent.invoke.result"
    [("id", some (.str id)), ("result", some (.obj [("ok", .bool false), ("error", .str err)]))]

def availResult (id : String) (a : Json) (err : Option String := none) : Json :=
  Json.msg "intent.available.result" [("id", some (.str id)), ("availability", some a), ("error", err.map .str)]

def emptyAvail (r : String) : Json :=
  .obj [("archetype", .str r), ("available", .bool false), ("candidates", .arr []), ("hasDefault", .bool false)]

def handlersResult (id : String) (hs : List Json) : Json :=
  Json.msg "intent.handlers.result" [("id", some (.str id)), ("handlers", some (.arr hs))]

def changedJson (a : Json) : Json := Json.msg "intent.changed" [("availability", some a)]

/-! ### Codec -/

inductive Req where
  | invoke (id : String) (r : Request)
  | available (id : String) (archetype : String)
  | handlers (id : String)
  deriving DecidableEq, Repr

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some "intent.invoke" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match (j.get? "request").bind requestOf? with
      | some r => .ok (.invoke id r)
      | none => .reject [invokeErr id "invalid convention"]
  | some "intent.available" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match j.getStr? "archetype" with
      | some a => .ok (.available id a)
      | none => .reject [availResult id (emptyAvail "") (some "invalid request")]
  | some "intent.handlers" =>
    match reqId? j with
    | some id => .ok (.handlers id)
    | none => .reject []
  | _ => .unknown

def encodeReq : Req → Json
  | .invoke id r => Json.msg "intent.invoke" [("id", some (.str id)), ("request", some (requestJson r))]
  | .available id a => Json.msg "intent.available" [("id", some (.str id)), ("archetype", some (.str a))]
  | .handlers id => Json.msg "intent.handlers" [("id", some (.str id))]

/-! ### Component -/

/-- NAP-INTENT §Convention URI normalization: `convention` is exactly
`napplet:<archetype>/<action>` with valid segments (`NapIntent.conventionOk` + `validIdent`). -/
def convOk (r : Request) : Bool :=
  r.convention == "napplet:" ++ r.archetype ++ "/" ++ r.action && validIdent r.convention.toList

def selection (r : Request) : Selection :=
  match r.handler with
  | none => .auto
  | some "default" => .auto
  | some "choose" => .choose
  | some h => .explicit h

def isLowerHex (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- `35129:<64 lowercase hex>:<non-empty d>`. -/
def addressOk (a : String) : Bool :=
  let l := a.toList
  l.take 6 == "35129:".toList &&
    let rest := l.drop 6
    (rest.take 64).length == 64 && (rest.take 64).all isLowerHex &&
      match rest.drop 64 with
      | ':' :: d => !d.isEmpty
      | _ => false

/-- A recommendation's catalog id (`Identity.catalogId` of a named manifest). -/
def hintId (h : Hint) : Option String :=
  if addressOk h.address then some ("nip5d:" ++ h.address) else none

def mkDelivery (sender : String) (r : Request) (h : String) : Delivery :=
  ⟨h, sender, r.archetype, r.action, r.convention, r.payload, r.behavior⟩

/-- Resolution context for absent / `"default"` handler (steps 2–4). -/
def autoCtx (s : St) (r : Request) (compat : List Candidate) : ResolveCtx :=
  { authorized := fun _ => false
    userChoice := none
    userDefault := (s.defaultFor r.archetype).filter fun d => compat.any (·.id == d)
    recommendation := if s.cfg.hints then r.hint.bind hintId else none
    recommendationUsable := fun x => compat.any (·.id == x)
    fallback := match compat with
      | [c] => some c.id
      | _ => none }

/-- Resolution context once the user answered a prompt. -/
def replyCtx (compat : List Candidate) (allowed : Bool) (choice : Option String) : ResolveCtx :=
  let pick := if allowed then choice.filter fun x => compat.any (·.id == x) else none
  { authorized := fun x => allowed && compat.any (·.id == x)
    userChoice := pick
    userDefault := none
    recommendation := none
    recommendationUsable := fun _ => false
    fallback := pick }

/-- A live endpoint of handler `h` able to receive `intent.deliver`. -/
def target? (w : World) (h : String) : Option Ctx :=
  w.live.find? fun c => c.catalogId == h && c.exposed.contains .intent

def launchArgs (d : Delivery) : Json :=
  Json.mkObj [("handler", some (.str d.handler)), ("behavior", d.behavior.map behaviorJson)]

/-- Deliver now, or retain and ask the host to launch the handler. -/
def place (w : World) (s : St) (d : Delivery) : St × List Eff :=
  match target? w d.handler with
  | some c =>
    (s, .send c.port (deliverJson d) ::
      (if d.behavior.bind (·.focus) == some true then
        [.effect (.nap .intent "focus" (.obj [("window", Json.nat c.window)]))] else []))
  | none =>
    ({ s with queue := s.queue ++ [d] },
     if s.queue.any (·.handler == d.handler) then []
     else [.effect (.nap .intent "launch" (launchArgs d))])

/-- Accept: the result goes to the source first, then the delivery. -/
def accept (w : World) (s : St) (port : PortId) (id : String) (d : Delivery) : St × List Eff :=
  let r := place w s d
  (r.1, .send port (okJson id d) :: r.2)

def promptDetails (sender : String) (r : Request) (extra : List (String × Json)) : Json :=
  .obj ([("sender", .str sender), ("archetype", .str r.archetype), ("action", .str r.action),
         ("convention", .str r.convention)] ++ extra)

def ask (s : St) (cx : Ctx) (id : String) (r : Request) (sel : Selection) (kind : String)
    (details : Json) : St × List Eff :=
  ({ s with pending := s.pending ++ [⟨s.next, cx.port, id, cx.catalogId, r, sel⟩], next := s.next + 1 },
   [.call ⟨.intent, s.next⟩ (.prompt .intent kind details)])

def chooseDetails (sender : String) (r : Request) (compat : List Candidate) : Json :=
  promptDetails sender r [("candidates", .arr (compat.map candidateJson))]

def invoke (w : World) (cx : Ctx) (s : St) (id : String) (r : Request) : St × List Eff :=
  if convOk r = false then (s, [.send cx.port (invokeErr id "invalid convention")])
  else if (candidates s r.archetype).isEmpty then (s, [.send cx.port (invokeErr id "no handler")])
  else if (compatible s r).isEmpty then (s, [.send cx.port (invokeErr id "unsupported convention")])
  else
    match selection r with
    | .explicit h =>
      if (compatible s r).any (·.id == h) then
        ask s cx id r (.explicit h) "authorize" (promptDetails cx.catalogId r [("handler", .str h)])
      else (s, [.send cx.port (invokeErr id "invoke rejected")])
    | .choose => ask s cx id r .choose "choose" (chooseDetails cx.catalogId r (compatible s r))
    | .auto =>
      match resolve (autoCtx s r (compatible s r)) .auto with
      | some h => accept w s cx.port id (mkDelivery cx.catalogId r h)
      | none => ask s cx id r .auto "choose" (chooseDetails cx.catalogId r (compatible s r))

def handle (_h : Host) (w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .invoke id r => invoke w cx s id r
  | .available id a => (s, [.send cx.port (availResult id (availJson s a))])
  | .handlers id => (s, [.send cx.port (handlersResult id ((roles s).map (availJson s)))])

def failReason (sel : Selection) (allowed : Bool) (choice : Option String) : String :=
  match sel with
  | .explicit _ => "invoke rejected"
  | _ => if allowed && choice.isSome then "invoke rejected" else "user cancelled"

/-- A prompt reply as (allowed, choice); anything but `decision` is a refusal. -/
def answer : Reply → Bool × Option String
  | .decision a c => (a, c)
  | _ => (false, none)

def onReply (_h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.pending.find? (·.n == n) with
  | none => (s, [])
  | some p =>
    match resolve (replyCtx (compatible s p.req) (answer rep).1 (answer rep).2) p.sel with
    | some h =>
      accept w { s with pending := s.pending.filter (·.n != n) } p.port p.id (mkDelivery p.sender p.req h)
    | none =>
      ({ s with pending := s.pending.filter (·.n != n) },
       [.send p.port (invokeErr p.id (failReason p.sel (answer rep).1 (answer rep).2))])

/-! ### Host events -/

def entryOf? (j : Json) : Option Entry := do
  some { id := ← j.getStr? "id", title := ← optField j "title" Json.asStr?,
         roles := ← (j.get? "z").bind Json.asStrs?, intents := ← (j.get? "i").bind Json.asTags? }

def catalogOf? (j : Json) : Option (List Entry) :=
  ((j.get? "entries").bind Json.asArr?).bind (·.mapM entryOf?)

def setDefault (ds : List (String × String)) (a : String) : Option String → List (String × String)
  | some h => (a, h) :: ds.filter (·.1 != a)
  | none => ds.filter (·.1 != a)

/-- `intent.changed` for every listed role whose availability changed, to every
endpoint with `intent` exposed. -/
def pushChanged (w : World) (old new : St) (rs : List String) : List Eff :=
  (rs.filter fun r => availJson old r != availJson new r).flatMap fun r =>
    (w.live.filter (·.exposed.contains .intent)).map fun c => .send c.port (changedJson (availJson new r))

def onEvent (_h : Host) (w : World) (s : St) : HostEvent → St × List Eff
  | .nap .intent "catalog" args =>
    match catalogOf? args with
    | some cat =>
      let s' := { s with catalog := cat }
      (s', pushChanged w s s' (dedupStr (roles s ++ roles s')))
    | none => (s, [])
  | .nap .intent "default" args =>
    match args.getStr? "archetype" with
    | some a =>
      let s' := { s with defaults := setDefault s.defaults a (args.getStr? "handler") }
      (s', pushChanged w s s' [a])
    | none => (s, [])
  | .nap .intent "launchFailed" args =>
    match args.getStr? "handler" with
    | some h => ({ s with queue := s.queue.filter (·.handler != h) }, [])
    | none => (s, [])
  | _ => (s, [])

/-- Deliver retained deliveries whose target is now live, in acceptance order. -/
def flush (_h : Host) (w : World) (s : St) : St × List Eff :=
  ({ s with queue := s.queue.filter fun d => (target? w d.handler).isNone },
   s.queue.filterMap fun d => (target? w d.handler).map fun c => .send c.port (deliverJson d))

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with pending := s.pending.filter (·.port != p) },
   (s.pending.filter (·.port == p)).map fun x => .effect (.cancel ⟨.intent, x.n⟩))

def mentions (s : St) (p : PortId) : Bool := s.pending.any (·.port == p)

/-! ### Required properties -/

theorem behaviorOf?_behaviorJson (b : Behavior) : behaviorOf? (behaviorJson b) = some b := by
  obtain ⟨f, r⟩ := b
  cases f <;> cases r <;> simp [behaviorOf?, behaviorJson, Json.mkObj, Json.isObj, optField,
    Json.get?, Json.lookup, Json.asBool?]

theorem hintOf?_hintJson (h : Hint) : hintOf? (hintJson h) = some h := by
  obtain ⟨a, r⟩ := h
  cases r <;> simp [hintOf?, hintJson, Json.mkObj, optField, Json.getStr?, Json.get?, Json.lookup]

theorem requestOf?_requestJson (r : Request) : requestOf? (requestJson r) = some r := by
  obtain ⟨a, ac, c, pl, h, hi, b⟩ := r
  cases pl <;> cases h <;> cases hi <;> cases b <;>
    simp [requestOf?, requestJson, Json.mkObj, optField, Json.getStr?, Json.get?, Json.lookup,
      hintOf?_hintJson, behaviorOf?_behaviorJson, Json.asStr?]

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup,
    reqId?, requestOf?_requestJson]

theorem accept_pending (w : World) (s : St) (port : PortId) (id : String) (d : Delivery) :
    (accept w s port id d).1.pending = s.pending := by
  simp only [accept, place]
  split <;> rfl

theorem invoke_pending (w : World) (cx : Ctx) (s : St) (id : String) (r : Request) :
    (invoke w cx s id r).1.pending = s.pending ∨
    ∃ x, (invoke w cx s id r).1.pending = s.pending ++ [x] ∧ x.port = cx.port := by
  unfold invoke
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · split
      · exact .inl rfl
      · split
        · split
          · exact .inr ⟨_, rfl, rfl⟩
          · exact .inl rfl
        · exact .inr ⟨_, rfl, rfl⟩
        · split
          · exact .inl (accept_pending ..)
          · exact .inr ⟨_, rfl, rfl⟩

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp only [drop, mentions, List.any_eq_true, List.mem_filter] at h ⊢
  obtain ⟨x, ⟨hx, -⟩, hq⟩ := h
  exact ⟨x, hx, hq⟩

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  cases r with
  | available => exact .inl hm
  | handlers => exact .inl hm
  | invoke id r =>
    simp only [handle, mentions] at hm
    rcases invoke_pending w cx s id r with he | ⟨x, he, hx⟩
    · rw [he] at hm; exact .inl hm
    · rw [he, List.any_append] at hm
      simp only [Bool.or_eq_true, List.any_cons, List.any_nil, Bool.or_false, beq_iff_eq] at hm
      rcases hm with hm | hm
      · exact .inl hm
      · exact .inr ⟨cx, hcx, hx ▸ hm⟩

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  unfold onReply at hm
  split at hm
  · exact hm
  · have key : ∀ t : St, t.pending = s.pending.filter (·.n != n) → mentions t q = true →
        mentions s q = true := by
      intro t ht hq
      simp only [mentions, ht, List.any_eq_true, List.mem_filter] at hq ⊢
      obtain ⟨x, ⟨hx, -⟩, h⟩ := hq
      exact ⟨x, hx, h⟩
    split at hm
    · exact key _ (by rw [accept_pending]) hm
    · exact key _ rfl hm

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  unfold onEvent at hm
  split at hm <;> (try split at hm) <;> exact hm

/-- `flush` obeys the same mentions shape (it never adds per-endpoint state). -/
theorem flush_mentions (h : Host) (w : World) (s : St) (q : PortId)
    (hm : mentions (flush h w s).1 q = true) : mentions s q = true ∨ w.bound q := .inl hm

/-! ### NAP-INTENT properties at the component level -/

/-- A napplet request never changes the catalog or the user's defaults
("A napplet cannot set or change it"). -/
theorem handle_prefs_unchanged (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    (handle h w cx s r).1.catalog = s.catalog ∧ (handle h w cx s r).1.defaults = s.defaults := by
  cases r with
  | available => exact ⟨rfl, rfl⟩
  | handlers => exact ⟨rfl, rfl⟩
  | invoke id r =>
    simp only [handle]
    unfold invoke
    repeat' split
    all_goals first
      | exact ⟨rfl, rfl⟩
      | (simp only [accept, place]; split <;> exact ⟨rfl, rfl⟩)

theorem target?_spec {w : World} {hd : String} {c : Ctx} (ht : target? w hd = some c) :
    c ∈ w.live ∧ c.catalogId = hd ∧ Domain.intent ∈ c.exposed := by
  have hm := List.mem_of_find?_eq_some ht
  have hp := List.find?_some ht
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hp
  exact ⟨hm, hp.1, hp.2⟩

/-- What `place` sends: only `intent.deliver` of that delivery, to a live endpoint of
the handler that has `intent` exposed. -/
theorem place_sends (w : World) (s : St) (d : Delivery) (p : PortId) (m : Json)
    (hm : Eff.send p m ∈ (place w s d).2) :
    ∃ c ∈ w.live, c.port = p ∧ c.catalogId = d.handler ∧ Domain.intent ∈ c.exposed ∧
      m = deliverJson d := by
  unfold place at hm
  split at hm
  · rename_i c hc
    obtain ⟨h1, h2, h3⟩ := target?_spec hc
    simp only [List.mem_cons] at hm
    rcases hm with hm | hm
    · simp only [Eff.send.injEq] at hm
      exact ⟨c, h1, hm.1.symm, h2, h3, hm.2⟩
    · split at hm <;> simp at hm
  · split at hm <;> simp at hm

/-- Every message `handle` sends goes either back to the requesting endpoint or, as
an `intent.deliver` stamped with the requester's catalog id, to a live endpoint of
the resolved handler (no payload or sender leaks to any other napplet). -/
theorem handle_sends (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (p : PortId) (m : Json)
    (hm : Eff.send p m ∈ (handle h w cx s r).2) :
    p = cx.port ∨ ∃ c ∈ w.live, c.port = p ∧ ∃ d : Delivery, m = deliverJson d ∧
      c.catalogId = d.handler ∧ d.sender = cx.catalogId := by
  cases r with
  | available => simp [handle] at hm; exact .inl hm.1
  | handlers => simp [handle] at hm; exact .inl hm.1
  | invoke id r =>
    simp only [handle] at hm
    unfold invoke at hm
    repeat' split at hm
    all_goals first
      | (simp at hm; exact .inl hm.1)
      | (simp [ask] at hm)
      | (simp only [accept, List.mem_cons, Eff.send.injEq] at hm
         rcases hm with hm | hm
         · exact .inl hm.1
         · obtain ⟨c, h1, h2, h3, -, h5⟩ := place_sends _ _ _ _ _ hm
           exact .inr ⟨c, h1, h2, _, h5, h3, rfl⟩)

/-- Replies to prompts: messages go to the waiting source, or deliver to a live
endpoint of the resolved handler with the sender recorded at invocation. -/
theorem onReply_sends (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (p : PortId) (m : Json)
    (hm : Eff.send p m ∈ (onReply h w s n rep).2) :
    ∃ x ∈ s.pending, x.n = n ∧ (p = x.port ∨ ∃ c ∈ w.live, c.port = p ∧ ∃ d : Delivery,
      m = deliverJson d ∧ c.catalogId = d.handler ∧ d.sender = x.sender) := by
  unfold onReply at hm
  split at hm
  · simp at hm
  · rename_i x hx
    have hxm := List.mem_of_find?_eq_some hx
    have hxn := List.find?_some hx
    simp only [beq_iff_eq] at hxn
    refine ⟨x, hxm, hxn, ?_⟩
    split at hm
    · simp only [accept, List.mem_cons, Eff.send.injEq] at hm
      rcases hm with hm | hm
      · exact .inl hm.1
      · obtain ⟨c, h1, h2, h3, -, h5⟩ := place_sends _ _ _ _ _ hm
        exact .inr ⟨c, h1, h2, _, h5, h3, rfl⟩
    · simp at hm; exact .inl hm.1

/-- An explicit selection never falls back: any delivery accepted for it targets the
named handler (lifts `NapIntent.explicit_no_fallback`). -/
theorem explicit_reply_target (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (x : Pending)
    (hx : s.pending.find? (·.n == n) = some x)
    (hsel : ∃ t, x.sel = .explicit t) (p : PortId) (m : Json)
    (hm : Eff.send p m ∈ (onReply h w s n rep).2) (hp : p ≠ x.port) :
    ∃ t d, x.sel = .explicit t ∧ m = deliverJson d ∧ d.handler = t := by
  obtain ⟨t, ht⟩ := hsel
  simp only [onReply, hx] at hm
  split at hm
  · rename_i hh hres
    rw [ht] at hres
    have := explicit_no_fallback _ _ _ hres
    simp only [accept, List.mem_cons, Eff.send.injEq] at hm
    rcases hm with hm | hm
    · exact absurd hm.1 hp
    · obtain ⟨c, -, -, -, -, h5⟩ := place_sends _ _ _ _ _ hm
      exact ⟨t, _, ht, h5, by simp [mkDelivery, this]⟩
  · simp at hm; exact absurd hm.1 hp

/-- The user's applicable default wins (lifts `NapIntent.default_wins`): with no
explicit handler, a valid convention and a compatible default `d`, the invocation is
accepted for `d` at once, result first. -/
theorem default_accepted (h : Host) (w : World) (cx : Ctx) (s : St) (id : String) (r : Request)
    (d : String) (hc : convOk r = true) (hsel : selection r = .auto)
    (hd : s.defaultFor r.archetype = some d) (hcompat : (compatible s r).any (·.id == d) = true) :
    handle h w cx s (.invoke id r) = accept w s cx.port id (mkDelivery cx.catalogId r d) := by
  have hne : (compatible s r).isEmpty = false := by
    cases hcs : compatible s r with
    | nil => rw [hcs] at hcompat; simp at hcompat
    | cons => rfl
  have hne2 : (candidates s r.archetype).isEmpty = false := by
    cases hcs : candidates s r.archetype with
    | nil => simp [compatible, hcs] at hne
    | cons => rfl
  have hres : resolve (autoCtx s r (compatible s r)) .auto = some d := by
    apply default_wins
    simp [autoCtx, hd, hcompat]
  simp only [handle, invoke, hc, hne2, hne, hsel, hres]
  simp

/-- `flush` sends only `intent.deliver` of retained deliveries, each to a live endpoint
of its handler with `intent` exposed, and retains exactly the rest. -/
theorem flush_sends (h : Host) (w : World) (s : St) (e : Eff) (he : e ∈ (flush h w s).2) :
    ∃ d ∈ s.queue, ∃ c ∈ w.live, c.catalogId = d.handler ∧ Domain.intent ∈ c.exposed ∧
      e = .send c.port (deliverJson d) := by
  simp only [flush, List.mem_filterMap, Option.map_eq_some_iff] at he
  obtain ⟨d, hd, c, hc, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := target?_spec hc
  exact ⟨d, hd, c, h1, h2, h3, rfl⟩

/-- A delivery is retained until delivered or terminally failed: `flush` keeps every
delivery whose handler has no live target. -/
theorem flush_retains (h : Host) (w : World) (s : St) (d : Delivery) (hd : d ∈ s.queue)
    (hn : target? w d.handler = none) : d ∈ (flush h w s).1.queue := by
  simp [flush, hd, hn]

/-- Teardown of a source cancels its prompts and leaves accepted deliveries in place
("delivery MUST NOT depend on the source remaining alive"). -/
theorem drop_keeps_queue (s : St) (p : PortId) : (drop s p).1.queue = s.queue := rfl

/-! ### Vectors (upstream examples) -/

section vectors

private def ctxFeed : Ctx :=
  { port := 1, window := 10,
    identity := { dTag := some "social-feed", artifactHash := "h1", publisher := "pk" },
    exposed := [.intent], inst := 0 }
private def ctxViewer : Ctx :=
  { port := 2, window := 20,
    identity := { dTag := some "profile-viewer", artifactHash := "h2", publisher := "pk" },
    exposed := [.intent], inst := 0 }
private def hst : Host :=
  { crypto := { sha256 := fun _ => "", verifySig := fun _ => true }, verifyEvent := fun _ => true,
    sniff := fun _ => "", rasterize := fun _ => none, looksCiphertext := fun _ => false,
    encryptedWith := fun _ => none, transform := id }
private def wFeed : World := { now := 0, live := [ctxFeed], user := "" }
private def wBoth : World := { now := 0, live := [ctxFeed, ctxViewer], user := "" }

private def isOk (d : Decoded Req) (r : Req) : Bool :=
  match d with
  | .ok x => x == r
  | _ => false

private def sendsSame (es : List Eff) (exp : List (PortId × String)) : Bool :=
  es.length == exp.length &&
  (es.zip exp).all fun (e, p, t) => match e with
    | .send q m => q == p && Json.same m (Json.parse! t)
    | _ => false

-- Catalog: the upstream example's installed manifest, then the user's default.
private def catEv : HostEvent := .nap .intent "catalog" (Json.parse!
  "{\"entries\":[{\"id\":\"catalog-profile-viewer\",\"title\":\"Profile Viewer\",\"z\":[\"profile\"],\"i\":[[\"napplet:profile/open\",\"pubkey\"]]}]}")
private def defEv : HostEvent := .nap .intent "default" (Json.parse!
  "{\"archetype\":\"profile\",\"handler\":\"catalog-profile-viewer\"}")
private def sCat : St := (onEvent hst wFeed (onEvent hst wFeed .init catEv).1 defEv).1

#guard sendsSame (onEvent hst wFeed .init catEv).2
  [(1, "{\"type\":\"intent.changed\",\"availability\":{\"archetype\":\"profile\",\"available\":true,\"candidates\":[{\"id\":\"catalog-profile-viewer\",\"title\":\"Profile Viewer\",\"actions\":[\"open\"],\"conventions\":[\"napplet:profile/open\"],\"contracts\":[{\"convention\":\"napplet:profile/open\",\"params\":[\"pubkey\"]}]}],\"hasDefault\":false}}")]

-- decode: upstream requests
#guard isOk (decode (Json.parse! "{ \"type\": \"intent.available\", \"id\": \"a1\", \"archetype\": \"profile\" }"))
  (.available "a1" "profile")
#guard isOk (decode (Json.parse! "{ \"type\": \"intent.invoke\", \"id\": \"i1\", \"request\": { \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } } }"))
  (.invoke "i1" { archetype := "profile", action := "open", convention := "napplet:profile/open",
                  payload := some (Json.parse! "{ \"pubkey\": \"abc123...\" }") })
#guard isOk (decode (Json.parse! "{ \"type\": \"intent.invoke\", \"id\": \"i2\", \"request\": { \"archetype\": \"emoji-list\", \"action\": \"open\", \"convention\": \"napplet:emoji-list/open\" } }"))
  (.invoke "i2" { archetype := "emoji-list", action := "open", convention := "napplet:emoji-list/open" })
#guard isOk (decode (Json.parse! "{ \"type\": \"intent.handlers\", \"id\": \"h1\" }")) (.handlers "h1")
#guard decode (Json.parse! "{ \"type\": \"intent.open\", \"id\": \"h1\" }") matches .unknown
#guard match decode (Json.parse! "{ \"type\": \"intent.invoke\", \"id\": \"i3\", \"request\": { \"archetype\": 3 } }") with
  | .reject [m] => Json.same m (Json.parse! "{ \"type\": \"intent.invoke.result\", \"id\": \"i3\", \"result\": { \"ok\": false, \"error\": \"invalid convention\" } }")
  | _ => false

-- intent.available: the upstream example response verbatim
#guard sendsSame (handle hst wFeed ctxFeed sCat (.available "a1" "profile")).2
  [(1, "{
     \"type\": \"intent.available.result\",
     \"id\": \"a1\",
     \"availability\": {
       \"archetype\": \"profile\",
       \"available\": true,
       \"candidates\": [{
         \"id\": \"catalog-profile-viewer\",
         \"title\": \"Profile Viewer\",
         \"actions\": [\"open\"],
         \"conventions\": [\"napplet:profile/open\"],
         \"contracts\": [{
           \"convention\": \"napplet:profile/open\",
           \"params\": [\"pubkey\"]
         }],
         \"isDefault\": true
       }],
       \"hasDefault\": true
     }
   }")]

-- intent.invoke: upstream result verbatim; no live target, so retained + launch
private def invI1 : Req := .invoke "i1"
  { archetype := "profile", action := "open", convention := "napplet:profile/open",
    payload := some (Json.parse! "{ \"pubkey\": \"abc123...\" }") }
#guard sendsSame ((handle hst wFeed ctxFeed sCat invI1).2.take 1)
  [(1, "{
     \"type\": \"intent.invoke.result\",
     \"id\": \"i1\",
     \"result\": {
       \"ok\": true,
       \"archetype\": \"profile\",
       \"action\": \"open\",
       \"convention\": \"napplet:profile/open\",
       \"handler\": \"catalog-profile-viewer\"
     }
   }")]
#guard (handle hst wFeed ctxFeed sCat invI1).2.drop 1 ==
  [.effect (.nap .intent "launch" (Json.parse! "{\"handler\":\"catalog-profile-viewer\"}"))]
#guard (handle hst wFeed ctxFeed sCat invI1).1.queue.length == 1

-- no handler: upstream verbatim
#guard sendsSame (handle hst wFeed ctxFeed sCat (.invoke "i2"
    { archetype := "emoji-list", action := "open", convention := "napplet:emoji-list/open" })).2
  [(1, "{ \"type\": \"intent.invoke.result\", \"id\": \"i2\", \"result\": { \"ok\": false, \"error\": \"no handler\" } }")]

-- delivery builder: upstream verbatim
#guard Json.same (deliverJson ⟨"catalog-profile-viewer", "catalog-social-feed", "profile", "open",
    "napplet:profile/open", some (Json.parse! "{ \"pubkey\": \"abc123...\" }"), none⟩)
  (Json.parse! "{
     \"type\": \"intent.deliver\",
     \"delivery\": {
       \"sender\": \"catalog-social-feed\",
       \"archetype\": \"profile\",
       \"action\": \"open\",
       \"convention\": \"napplet:profile/open\",
       \"payload\": { \"pubkey\": \"abc123...\" }
     }
   }")

-- end to end with runtime catalog ids: retained, then flushed once the viewer is live
private def viewerId : String := ctxViewer.catalogId
private def sLive : St := (onEvent hst wFeed .init (.nap .intent "catalog" (Json.mkObj
  [("entries", some (.arr [Json.mkObj [("id", some (.str viewerId)), ("z", some (Json.strs ["profile"])),
     ("i", some (Json.tags [["napplet:profile/open", "pubkey"]]))]]))]))).1
private def sQ : St := (handle hst wFeed ctxFeed sLive invI1).1
#guard sQ.queue.length == 1
#guard (flush hst wFeed sQ).2 == []
#guard sendsSame (flush hst wBoth sQ).2
  [(2, "{ \"type\": \"intent.deliver\", \"delivery\": { \"sender\": \"nip5d:35129:pk:social-feed\", \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } } }")]
#guard (flush hst wBoth sQ).1.queue == []
-- live target: result first, then delivery
#guard sendsSame (handle hst wBoth ctxFeed sLive invI1).2
  [(1, "{ \"type\": \"intent.invoke.result\", \"id\": \"i1\", \"result\": { \"ok\": true, \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"handler\": \"nip5d:35129:pk:profile-viewer\" } }"),
   (2, "{ \"type\": \"intent.deliver\", \"delivery\": { \"sender\": \"nip5d:35129:pk:social-feed\", \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } } }")]

-- choose: prompt, then the user's pick
private def invChoose : Req := .invoke "i4"
  { archetype := "profile", action := "open", convention := "napplet:profile/open", handler := some "choose" }
#guard match (handle hst wBoth ctxFeed sLive invChoose).2 with
  | [.call ⟨.intent, 0⟩ (.prompt .intent "choose" _)] => true
  | _ => false
#guard sendsSame (onReply hst wBoth (handle hst wBoth ctxFeed sLive invChoose).1 0 (.decision false none)).2
  [(1, "{ \"type\": \"intent.invoke.result\", \"id\": \"i4\", \"result\": { \"ok\": false, \"error\": \"user cancelled\" } }")]
#guard (onReply hst wBoth (handle hst wBoth ctxFeed sLive invChoose).1 0 (.decision true (some viewerId))).2.length == 2
#guard (drop (handle hst wBoth ctxFeed sLive invChoose).1 1).2 == [.effect (.cancel ⟨.intent, 0⟩)]

-- invalid convention, unsupported convention
#guard sendsSame (handle hst wFeed ctxFeed sCat (.invoke "i5"
    { archetype := "profile", action := "open", convention := "napplet:profile/edit" })).2
  [(1, "{ \"type\": \"intent.invoke.result\", \"id\": \"i5\", \"result\": { \"ok\": false, \"error\": \"invalid convention\" } }")]
#guard sendsSame (handle hst wFeed ctxFeed sCat (.invoke "i6"
    { archetype := "profile", action := "edit", convention := "napplet:profile/edit" })).2
  [(1, "{ \"type\": \"intent.invoke.result\", \"id\": \"i6\", \"result\": { \"ok\": false, \"error\": \"unsupported convention\" } }")]

-- handlers
#guard sendsSame (handle hst wFeed ctxFeed sLive (.handlers "h1")).2
  [(1, "{\"type\":\"intent.handlers.result\",\"id\":\"h1\",\"handlers\":[{\"archetype\":\"profile\",\"available\":true,\"candidates\":[{\"id\":\"nip5d:35129:pk:profile-viewer\",\"actions\":[\"open\"],\"conventions\":[\"napplet:profile/open\"],\"contracts\":[{\"convention\":\"napplet:profile/open\",\"params\":[\"pubkey\"]}]}],\"hasDefault\":false}]}")]

-- an `i` tag whose role has no `z` tag is not a contract
#guard (candidates { St.init with catalog := [⟨"x", none, [], [["napplet:profile/open"]]⟩] } "profile").isEmpty

end vectors

end Napplet.Run.Intent
