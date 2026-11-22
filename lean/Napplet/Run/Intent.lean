/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Intent

/-!
# NAP-INTENT runtime component

Upstream: `napplet/naps` `master`, `naps/NAP-INTENT.md` at `377bf939`, with PR #148
(`nap-intent-launch` at `9e25e676`: explicit launch) and PR #128 (`nap-intent-history`
at `74f9bf85`: delivery to a selected instance).

Wire (napplet → runtime): `intent.invoke {id, request}`, `intent.available {id, archetype}`,
`intent.handlers {id}`. Wire (runtime → napplet): `intent.invoke.result {id, result}`,
`intent.available.result {id, availability, error?}`, `intent.handlers.result {id, handlers, error?}`,
pushes `intent.changed {availability}` and `intent.deliver {delivery}` (no `id`).
PR #148 adds `intent.launch {id, target: {address, relays?}, behavior?}` →
`intent.launch.result {id, result: {ok, handler?, error?}}`.

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
  its `params` are the tag's remaining values; tag order is irrelevant; every valid
  `i` tag yields its own contract, even when two share a convention;
* a candidate for `r` is a dispatchable entry (`Entry.dispatchable`) with at least one
  such contract; its `conventions` and `actions` are derived from its contracts without
  duplicates;
* `handlers()` covers every role that has a candidate.

User defaults (one per archetype) are shell state fed by `HostEvent.nap .intent
"default"`. No napplet request changes the catalog or the defaults
(`handle_prefs_unchanged`).

## Invocation

1. `request` fields of the wrong JSON type: `{ok: false, error: "invalid convention"}`.
   `convention` must be exactly `napplet:<archetype>/<action>` with valid name
   segments, and a `handlerHint`, if present, must name a kind-35129 address
   `35129:<64 lowercase hex>:<non-empty d>` (`addressOk`), else `"invalid convention"`.
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

## Explicit launch (PR #148)

`intent.launch` names one napplet by its manifest coordinate. A `target` that is not an
object with a text `address` and optional list of text `relays`, or a malformed
`behavior`, is `"invalid target"`, as is an address that is not `35129:<64 lowercase
hex>:<non-empty d>` or `15129:<64 lowercase hex>:` (`launchId?`). The handler is the
catalog id of exactly that coordinate (`nip5d:<address>`, or `nip5d:15129:<pubkey>`):
no default, recommendation, chooser or substitute is consulted. A target in the catalog
is installed. An absent target is rejected with `"not installed"` or, under
`Cfg.absent = .rejected`, `"launch rejected"`, unless `Cfg.absent = .offerInstall`.
With `Cfg.confirmLaunch` (default) the user is asked first (`Call.prompt .intent
"launch"`; refusal → `"user cancelled"`). Acceptance sends `{ok: true, handler}`, then
asks the host to open the installed napplet (`Effect.nap .intent "open"`) or to run its
install review (`Effect.nap .intent "install"`). Neither effect names the source. Launch
carries no payload, produces no `intent.deliver`, and changes neither the catalog nor
the defaults.

## Delivery to a selected instance (PR #128)

The shell, never a napplet, may replay an invocation to one running instance
(`HostEvent.nap .intent "replay"`). The runtime delivers to the endpoint in exactly that
window if it is live, has `intent` exposed, and its own catalog entry has an eligible
contract with exactly that convention; the delivery's `sender` is that instance's own
catalog id and its fields are passed through unchanged. Otherwise the replay fails
(`Effect.nap .intent "replayFailed"`) without a chooser, default, launch, retention or
other endpoint. Members of an `intent.invoke` request that the schema does not define
(an instance selector, a `sender`) are ignored, so a napplet cannot select an instance.

Malformed `intent.available` (non-string `archetype`) with a string `id` gets
`{id, availability: {archetype: "", available: false, candidates: [], hasDefault: false},
error: "invalid request"}` (the result requires `availability`). Any malformed message
without a string `id` is dropped.
-/

/-! ## Host operations

* `HostEvent.nap .intent "catalog" {"entries": [Entry]}` where
  `Entry = {"id": text, "title"?: text, "z": [text], "i": [[text, ...]], "dispatchable"?: bool}`. The complete
  installed catalog, replacing the previous one. Contract: one entry per verified
  installed NIP-5D napplet manifest (kinds 5129, 15129, 35129; signature and artifact
  verified per NIP-5D); `id` is that manifest's catalog id exactly as
  `Identity.catalogId` computes it (`nip5d:35129:<pubkey>:<d>`, `nip5d:15129:<pubkey>`,
  `nip5d:5129:<event id>`), so it equals `Ctx.catalogId` of the running napplet;
  `title` is the manifest's title, if any; `z` lists the values of its `z` tags and `i`
  the full value lists (after the tag name) of its `i` tags, in tag order.
  `dispatchable` (default `true`) is `false` when the shell would not admit the
  manifest as a delivery target: its `R` set (capability requirements) cannot be met,
  or shell policy would load it without `intent` exposed (NAP-INTENT: "The runtime
  MUST apply the manifest capability requirements and its own policy before accepting
  delivery"). Such an entry is never a candidate, so no invocation is accepted for
  it. The host
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

* `Call.prompt .intent "launch" {"sender": text, "handler": text, "address": text,
  "installed": bool, "relays"?: [text]}` → `Reply.decision allowed _` (PR #148, with
  `Cfg.confirmLaunch`). Ask the user whether to open (or, when `installed` is false, to
  review installing) the napplet `handler` that the source `sender` named ("opening
  SHOULD require a user gesture or confirmation under policy"). The host may answer from
  a recent user gesture or a rule the user configured, and SHOULD refuse launches beyond
  a rate limit ("The runtime SHOULD rate-limit launches"). `allowed = false` yields
  `"user cancelled"`.
* `Effect.nap .intent "open" {"handler": text, "behavior"?: {"focus"?, "reuse"?}}` (PR
  #148): open or focus the installed napplet whose catalog id is `handler`, through the
  ordinary NIP-5D load when it is not running, honouring `behavior` as hints. It gets
  only its own manifest's capabilities under shell policy and nothing about the source
  ("`launch` grants nothing"). A failure is post-acceptance and not reported.
* `Effect.nap .intent "install" {"handler": text, "address": text, "relays"?: [text],
  "behavior"?: {...}}` (PR #148, `Cfg.absent = .offerInstall`): resolve the signed
  manifest for `address` from relays (the hints are untrusted and MUST NOT bypass the
  shell's network policy), verify its signature and that its coordinate is exactly
  `address`, apply the ordinary installation, artifact verification and execution rules,
  and install only after the user confirms in the install review; then it MAY open the
  napplet. A declined or failed installation is not reported to the source. The
  installed manifest reaches the catalog through the ordinary `catalog` event.
* `HostEvent.nap .intent "replay" {"window": number, "archetype": text, "action": text,
  "convention": text, "payload"?: any}` (PR #128): replay to the instance in `window`
  an invocation that instance itself produced (for example a location it reported under
  another domain's contract, as in the NAP-NAVIGATION proposal). Contract: only user
  action or shell policy causes it; the content is that target's own, never authored by
  the shell; `window` is the shell's own selection, not a catalog id.
* `Effect.nap .intent "replayFailed" {"window": number}` (PR #128): the selected
  instance is gone, does not have `intent` exposed, or does not advertise the
  convention; nothing was delivered and no other instance will be tried.

A prompt reply other than `decision` counts as a refusal / cancellation. Prompts of a
torn-down source are cancelled with `Effect.cancel`.
-/

namespace Napplet.Run.Intent

open NapIntent

/-- How `intent.launch` treats a target that is not installed (PR #148). -/
inductive Absent where
  /-- Accept and run the install review ("The runtime MAY offer installation"). -/
  | offerInstall
  /-- Reject with `"not installed"`. -/
  | notInstalled
  /-- Reject with `"launch rejected"` ("under its privacy policy"). -/
  | rejected
  deriving DecidableEq, Repr

/-- Shell intent policy. -/
structure Cfg where
  /-- Consider `handlerHint` recommendations (resolution step 3). -/
  hints : Bool := true
  /-- Ask the user before accepting a launch (PR #148: "opening SHOULD require a user
  gesture or confirmation under policy"). -/
  confirmLaunch : Bool := true
  absent : Absent := .notInstalled

/-! ### Catalog -/

/-- One installed manifest as the host reports it. -/
structure Entry where
  id : String
  title : Option String
  /-- `z` tag values. -/
  roles : List String
  /-- `i` tag values: convention followed by advertised parameter names. -/
  intents : List (List String)
  /-- The shell would admit this manifest as a delivery target (its `R` set is met
  and policy exposes `intent`). Host-set; only dispatchable entries are candidates. -/
  dispatchable : Bool := true
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

/-- Eligible contracts of an entry for role `r`: one per valid `i` tag, in tag order. -/
def Entry.contracts (e : Entry) (r : String) : List Contract :=
  if r ∈ e.roles then
    e.intents.filterMap fun t =>
      match t with
      | c :: ps =>
        match parseConv c with
        | some (a, _) => if a = r then some (Contract.mk c ps) else none
        | none => none
      | [] => none
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

/-- A launch waiting on the user's confirmation (PR #148). -/
structure LaunchPending where
  n : Nat
  port : PortId
  id : String
  handler : String
  installed : Bool
  target : Hint
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
  /-- Launches waiting on the user (PR #148). -/
  launching : List LaunchPending := []

def St.init (cfg : Cfg := {}) : St := ⟨cfg, [], [], [], [], 0, []⟩

def St.defaultFor (s : St) (r : String) : Option String :=
  (s.defaults.find? (·.1 == r)).map (·.2)

def candidates (s : St) (r : String) : List Candidate :=
  s.catalog.filterMap fun e =>
    let cs := e.contracts r
    if !e.dispatchable || cs.isEmpty then none else some ⟨e.id, e.title, cs, s.defaultFor r == some e.id⟩

/-- Every role with at least one candidate. -/
def roles (s : St) : List String :=
  dedupStr (s.catalog.flatMap fun e =>
    if e.dispatchable then e.roles.filter fun r => !(e.contracts r).isEmpty else [])

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

def launchErr (id err : String) : Json :=
  Json.msg "intent.launch.result"
    [("id", some (.str id)), ("result", some (.obj [("ok", .bool false), ("error", .str err)]))]

def launchOk (id handler : String) : Json :=
  Json.msg "intent.launch.result"
    [("id", some (.str id)), ("result", some (.obj [("ok", .bool true), ("handler", .str handler)]))]

/-! ### Codec -/

inductive Req where
  | invoke (id : String) (r : Request)
  | available (id : String) (archetype : String)
  | handlers (id : String)
  | launch (id : String) (target : Hint) (behavior : Option Behavior)
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
  | some "intent.launch" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match (j.get? "target").bind hintOf?, optField j "behavior" behaviorOf? with
      | some t, some b => .ok (.launch id t b)
      | _, _ => .reject [launchErr id "invalid target"]
  | _ => .unknown

def encodeReq : Req → Json
  | .invoke id r => Json.msg "intent.invoke" [("id", some (.str id)), ("request", some (requestJson r))]
  | .available id a => Json.msg "intent.available" [("id", some (.str id)), ("archetype", some (.str a))]
  | .handlers id => Json.msg "intent.handlers" [("id", some (.str id))]
  | .launch id t b => Json.msg "intent.launch"
      [("id", some (.str id)), ("target", some (hintJson t)), ("behavior", b.map behaviorJson)]

/-! ### Component -/

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

/-- NAP-INTENT §Convention URI normalization: `convention` is exactly
`napplet:<archetype>/<action>` with valid segments (`NapIntent.conventionOk` + `validIdent`),
and a `handlerHint`, if present, names a kind-35129 address (`IntentHandlerHint`
"accepts kind `35129` only"; an invalid hint makes the request invalid). -/
def convOk (r : Request) : Bool :=
  r.convention == "napplet:" ++ r.archetype ++ "/" ++ r.action && validIdent r.convention.toList &&
    r.hint.all (addressOk ·.address)

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

/-! ### Explicit launch (PR #148) -/

/-- `15129:<64 lowercase hex>:` (empty `d`). -/
def rootAddressOk (a : String) : Bool :=
  let l := a.toList
  l.take 6 == "15129:".toList &&
    let rest := l.drop 6
    rest.length == 65 && (rest.take 64).all isLowerHex && rest.drop 64 == [':']

/-- The catalog id of a valid `IntentTarget.address` (`Identity.catalogId`'s encoding):
"kind `35129` with a non-empty `d`, or kind `15129` with an empty `d`"; "A snapshot
(`5129`) has no stable coordinate and cannot be a target". -/
def launchId? (a : String) : Option String :=
  if addressOk a then some ("nip5d:" ++ a)
  else if rootAddressOk a then some ("nip5d:" ++ String.ofList (a.toList.dropLast))
  else none

def openArgs (h : String) (b : Option Behavior) : Json :=
  Json.mkObj [("handler", some (.str h)), ("behavior", b.map behaviorJson)]

def installArgs (h : String) (t : Hint) (b : Option Behavior) : Json :=
  Json.mkObj [("handler", some (.str h)), ("address", some (.str t.address)),
    ("relays", t.relays.map Json.strs), ("behavior", b.map behaviorJson)]

/-- Accept: the result to the source, then open or install. Neither effect names the
source. -/
def acceptLaunch (port : PortId) (id h : String) (installed : Bool) (t : Hint)
    (b : Option Behavior) : List Eff :=
  [.send port (launchOk id h),
   .effect (.nap .intent (if installed then "open" else "install")
     (if installed then openArgs h b else installArgs h t b))]

def launchDetails (sender h : String) (installed : Bool) (t : Hint) : Json :=
  Json.mkObj [("sender", some (.str sender)), ("handler", some (.str h)),
    ("address", some (.str t.address)), ("installed", some (.bool installed)),
    ("relays", t.relays.map Json.strs)]

/-- The target is installed: the verified catalog has exactly that catalog id. -/
def installed (s : St) (h : String) : Bool := s.catalog.any (·.id == h)

def launch (cx : Ctx) (s : St) (id : String) (t : Hint) (b : Option Behavior) : St × List Eff :=
  match launchId? t.address with
  | none => (s, [.send cx.port (launchErr id "invalid target")])
  | some h =>
    if !installed s h && s.cfg.absent == .notInstalled then
      (s, [.send cx.port (launchErr id "not installed")])
    else if !installed s h && s.cfg.absent == .rejected then
      (s, [.send cx.port (launchErr id "launch rejected")])
    else if s.cfg.confirmLaunch then
      ({ s with launching := s.launching ++ [⟨s.next, cx.port, id, h, installed s h, t, b⟩],
                next := s.next + 1 },
       [.call ⟨.intent, s.next⟩ (.prompt .intent "launch" (launchDetails cx.catalogId h (installed s h) t))])
    else (s, acceptLaunch cx.port id h (installed s h) t b)

def handle (_h : Host) (w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .invoke id r => invoke w cx s id r
  | .available id a => (s, [.send cx.port (availResult id (availJson s a))])
  | .handlers id => (s, [.send cx.port (handlersResult id ((roles s).map (availJson s)))])
  | .launch id t b => launch cx s id t b

def failReason (sel : Selection) (allowed : Bool) (choice : Option String) : String :=
  match sel with
  | .explicit _ => "invoke rejected"
  | _ => if allowed && choice.isSome then "invoke rejected" else "user cancelled"

/-- A prompt reply as (allowed, choice); anything but `decision` is a refusal. -/
def answer : Reply → Bool × Option String
  | .decision a c => (a, c)
  | _ => (false, none)

/-- The user's answer to a launch prompt. -/
def onLaunchReply (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.launching.find? (·.n == n) with
  | none => (s, [])
  | some l =>
    ({ s with launching := s.launching.filter (·.n != n) },
     if (answer rep).1 then acceptLaunch l.port l.id l.handler l.installed l.target l.behavior
     else [.send l.port (launchErr l.id "user cancelled")])

def onReply (_h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.pending.find? (·.n == n) with
  | none => onLaunchReply s n rep
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
         roles := ← (j.get? "z").bind Json.asStrs?, intents := ← (j.get? "i").bind Json.asTags?,
         dispatchable := (← optField j "dispatchable" Json.asBool?).getD true }

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

/-! ### Delivery to a selected instance (PR #128) -/

/-- A replayed invocation as the shell reports it. -/
structure Replay where
  window : WindowId
  archetype : String
  action : String
  convention : String
  payload : Option Json
  deriving DecidableEq, Repr

def replayOf? (j : Json) : Option Replay := do
  some { window := ← (j.get? "window").bind Json.asNat?, archetype := ← j.getStr? "archetype",
         action := ← j.getStr? "action", convention := ← j.getStr? "convention",
         payload := j.get? "payload" }

/-- The selected endpoint, if it can take this replay: live in that window, `intent`
exposed, and its own verified catalog entry has an eligible contract with exactly this
convention ("the eligible-contract and exact-identity rules of ordinary delivery"). -/
def replayTarget? (w : World) (s : St) (r : Replay) : Option Ctx :=
  (w.live.find? (·.window == r.window)).filter fun c =>
    c.exposed.contains .intent &&
    r.convention == "napplet:" ++ r.archetype ++ "/" ++ r.action && validIdent r.convention.toList &&
    s.catalog.any fun e => e.id == c.catalogId && (e.contracts r.archetype).any (·.convention == r.convention)

/-- The replay as an ordinary delivery: `sender` is the target's own catalog id and the
fields are unchanged. -/
def replayDelivery (c : Ctx) (r : Replay) : Delivery :=
  ⟨c.catalogId, c.catalogId, r.archetype, r.action, r.convention, r.payload, none⟩

def replay (w : World) (s : St) (r : Replay) : List Eff :=
  match replayTarget? w s r with
  | some c => [.send c.port (deliverJson (replayDelivery c r))]
  | none => [.effect (.nap .intent "replayFailed" (.obj [("window", Json.nat r.window)]))]

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
  | .nap .intent "replay" args =>
    match replayOf? args with
    | some r => (s, replay w s r)
    | none => (s, [])
  | _ => (s, [])

/-- Deliver retained deliveries whose target is now live, in acceptance order. -/
def flush (_h : Host) (w : World) (s : St) : St × List Eff :=
  ({ s with queue := s.queue.filter fun d => (target? w d.handler).isNone },
   s.queue.filterMap fun d => (target? w d.handler).map fun c => .send c.port (deliverJson d))

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with pending := s.pending.filter (·.port != p), launching := s.launching.filter (·.port != p) },
   (s.pending.filter (·.port == p)).map (fun x => .effect (.cancel ⟨.intent, x.n⟩)) ++
   (s.launching.filter (·.port == p)).map (fun x => .effect (.cancel ⟨.intent, x.n⟩)))

def mentions (s : St) (p : PortId) : Bool := s.pending.any (·.port == p) || s.launching.any (·.port == p)

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
  cases r with
  | launch id t b =>
    cases b <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup,
      reqId?, hintOf?_hintJson, behaviorOf?_behaviorJson, optField]
  | _ => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup,
    reqId?, requestOf?_requestJson]

theorem mentions_iff (s : St) (q : PortId) :
    mentions s q = true ↔ (∃ x ∈ s.pending, x.port = q) ∨ (∃ x ∈ s.launching, x.port = q) := by
  simp [mentions, List.any_eq_true]

theorem accept_pending (w : World) (s : St) (port : PortId) (id : String) (d : Delivery) :
    (accept w s port id d).1.pending = s.pending := by
  simp only [accept, place]
  split <;> rfl

theorem accept_launching (w : World) (s : St) (port : PortId) (id : String) (d : Delivery) :
    (accept w s port id d).1.launching = s.launching := by
  simp only [accept, place]
  split <;> rfl

theorem invoke_launching (w : World) (cx : Ctx) (s : St) (id : String) (r : Request) :
    (invoke w cx s id r).1.launching = s.launching := by
  unfold invoke
  repeat' split
  all_goals first | rfl | exact accept_launching ..

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

theorem launch_state (cx : Ctx) (s : St) (id : String) (t : Hint) (b : Option Behavior) :
    (launch cx s id t b).1.pending = s.pending ∧
    ((launch cx s id t b).1.launching = s.launching ∨
      ∃ x, (launch cx s id t b).1.launching = s.launching ++ [x] ∧ x.port = cx.port) := by
  unfold launch
  repeat' split
  all_goals first | exact ⟨rfl, .inl rfl⟩ | exact ⟨rfl, .inr ⟨_, rfl, rfl⟩⟩

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  rw [mentions_iff] at h ⊢
  simp only [drop, List.mem_filter] at h
  rcases h with ⟨x, ⟨hx, -⟩, hq⟩ | ⟨x, ⟨hx, -⟩, hq⟩
  · exact .inl ⟨x, hx, hq⟩
  · exact .inr ⟨x, hx, hq⟩

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  have hb : w.bound cx.port := ⟨cx, hcx, rfl⟩
  cases r with
  | available => exact .inl hm
  | handlers => exact .inl hm
  | invoke id r =>
    simp only [handle] at hm
    rw [mentions_iff, invoke_launching] at hm
    rcases invoke_pending w cx s id r with he | ⟨x, he, hx⟩
    · rw [he] at hm; exact .inl ((mentions_iff s q).mpr hm)
    · rw [he] at hm
      rcases hm with ⟨y, hy, hq⟩ | hl
      · rcases List.mem_append.mp hy with hy | hy
        · exact .inl ((mentions_iff s q).mpr (.inl ⟨y, hy, hq⟩))
        · simp only [List.mem_singleton] at hy; subst hy; exact .inr (by rw [← hq, hx]; exact hb)
      · exact .inl ((mentions_iff s q).mpr (.inr hl))
  | launch id t b =>
    simp only [handle] at hm
    rw [mentions_iff, (launch_state cx s id t b).1] at hm
    rcases (launch_state cx s id t b).2 with he | ⟨x, he, hx⟩
    · rw [he] at hm; exact .inl ((mentions_iff s q).mpr hm)
    · rw [he] at hm
      rcases hm with hp | ⟨y, hy, hq⟩
      · exact .inl ((mentions_iff s q).mpr (.inl hp))
      · rcases List.mem_append.mp hy with hy | hy
        · exact .inl ((mentions_iff s q).mpr (.inr ⟨y, hy, hq⟩))
        · simp only [List.mem_singleton] at hy; subst hy; exact .inr (by rw [← hq, hx]; exact hb)

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  rw [mentions_iff] at hm ⊢
  unfold onReply at hm
  split at hm
  · unfold onLaunchReply at hm
    split at hm
    · exact hm
    · simp only [List.mem_filter] at hm
      rcases hm with hp | ⟨x, ⟨hx, -⟩, hq⟩
      · exact .inl hp
      · exact .inr ⟨x, hx, hq⟩
  · have key : ∀ t : St, ((∃ x ∈ t.pending, x.port = q) ∨ (∃ x ∈ t.launching, x.port = q)) →
        t.pending = s.pending.filter (·.n != n) → t.launching = s.launching →
        (∃ x ∈ s.pending, x.port = q) ∨ (∃ x ∈ s.launching, x.port = q) := by
      intro t hq ht hl
      rw [ht, hl] at hq
      simp only [List.mem_filter] at hq
      rcases hq with ⟨x, ⟨hx, -⟩, h⟩ | h
      · exact .inl ⟨x, hx, h⟩
      · exact .inr h
    split at hm
    · exact key _ hm (by rw [accept_pending]) (by rw [accept_launching])
    · exact key _ hm rfl rfl

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
  | launch id t b =>
    simp only [handle]
    unfold launch
    repeat' split
    all_goals exact ⟨rfl, rfl⟩
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
  | launch id t b =>
    simp only [handle] at hm
    unfold launch at hm
    repeat' split at hm
    all_goals (simp [acceptLaunch] at hm <;> exact .inl hm.1)
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
    (∃ x ∈ s.pending, x.n = n ∧ (p = x.port ∨ ∃ c ∈ w.live, c.port = p ∧ ∃ d : Delivery,
      m = deliverJson d ∧ c.catalogId = d.handler ∧ d.sender = x.sender)) ∨
    (∃ l ∈ s.launching, l.n = n ∧ p = l.port) := by
  unfold onReply at hm
  split at hm
  · apply Or.inr
    unfold onLaunchReply at hm
    split at hm
    · simp at hm
    · rename_i l hl
      refine ⟨l, List.mem_of_find?_eq_some hl, by simpa using List.find?_some hl, ?_⟩
      split at hm <;> simp [acceptLaunch] at hm <;> exact hm.1
  · apply Or.inl
    rename_i x hx
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

/-! ### Explicit launch properties (PR #148) -/

/-- "The runtime MUST validate `target` and reject an invalid one with `"invalid target"`". -/
theorem launch_invalid (cx : Ctx) (s : St) (id : String) (t : Hint) (b : Option Behavior)
    (hv : launchId? t.address = none) :
    launch cx s id t b = (s, [.send cx.port (launchErr id "invalid target")]) := by
  simp [launch, hv]

/-- "MUST resolve only the napplet whose verified manifest has exactly `target.address`
... MUST NOT apply user defaults, recommendations, or a chooser, and MUST NOT substitute
another napplet": a launch rejects, asks the user about exactly that handler, or accepts
exactly that handler. -/
theorem launch_outputs (cx : Ctx) (s : St) (id : String) (t : Hint) (b : Option Behavior) (h : String)
    (hv : launchId? t.address = some h) :
    (launch cx s id t b).2 = [.send cx.port (launchErr id "not installed")] ∨
    (launch cx s id t b).2 = [.send cx.port (launchErr id "launch rejected")] ∨
    (launch cx s id t b).2 =
      [.call ⟨.intent, s.next⟩ (.prompt .intent "launch" (launchDetails cx.catalogId h (installed s h) t))] ∨
    (launch cx s id t b).2 = acceptLaunch cx.port id h (installed s h) t b := by
  simp only [launch, hv]
  repeat' split
  all_goals simp

/-- A launch waiting on the user holds exactly the named handler and target. -/
theorem launch_pending_target (cx : Ctx) (s : St) (id : String) (t : Hint) (b : Option Behavior) (h : String)
    (hv : launchId? t.address = some h) (x : LaunchPending) (hx : x ∈ (launch cx s id t b).1.launching) :
    x ∈ s.launching ∨ (x.handler = h ∧ x.target = t ∧ x.port = cx.port) := by
  simp only [launch, hv] at hx
  repeat' split at hx
  all_goals first
    | exact .inl hx
    | (rcases List.mem_append.mp hx with hx | hx
       · exact .inl hx
       · simp only [List.mem_singleton] at hx; subst hx; exact .inr ⟨rfl, rfl, rfl⟩)

/-- An absent target is never accepted unless the shell offers installation. -/
theorem launch_absent_rejected (cx : Ctx) (s : St) (id : String) (t : Hint) (b : Option Behavior) (h : String)
    (hv : launchId? t.address = some h) (hi : installed s h = false) (ha : s.cfg.absent ≠ .offerInstall) :
    launch cx s id t b = (s, [.send cx.port (launchErr id "not installed")]) ∨
    launch cx s id t b = (s, [.send cx.port (launchErr id "launch rejected")]) := by
  cases hab : s.cfg.absent with
  | offerInstall => exact absurd hab ha
  | notInstalled => exact .inl (by simp [launch, hv, hi, hab])
  | rejected => exact .inr (by simp [launch, hv, hi, hab])

/-- "`launch` carries no payload and produces no `IntentDelivery`": it never touches the
delivery queue. -/
theorem launch_queue (cx : Ctx) (s : St) (id : String) (t : Hint) (b : Option Behavior) :
    (launch cx s id t b).1.queue = s.queue := by
  unfold launch; repeat' split
  all_goals rfl

/-- "`launch` grants nothing. The target ... learns nothing about the source": the open
or install request is the same whoever launched. -/
theorem acceptLaunch_anonymous (p p' : PortId) (id id' h : String) (i : Bool) (t : Hint) (b : Option Behavior) :
    (acceptLaunch p id h i t b).tail = (acceptLaunch p' id' h i t b).tail := rfl

/-- Refusing the confirmation prompt is `"user cancelled"`, and nothing is opened. -/
theorem launch_refused (s : St) (n : Nat) (l : LaunchPending) (hl : s.launching.find? (·.n == n) = some l)
    (rep : Reply) (hr : (answer rep).1 = false) :
    (onLaunchReply s n rep).2 = [.send l.port (launchErr l.id "user cancelled")] := by
  simp [onLaunchReply, hl, hr]

/-! ### Selected-instance delivery properties (PR #128) -/

theorem replayTarget?_spec {w : World} {s : St} {r : Replay} {c : Ctx} (h : replayTarget? w s r = some c) :
    c ∈ w.live ∧ c.window = r.window ∧ Domain.intent ∈ c.exposed ∧
    ∃ e ∈ s.catalog, e.id = c.catalogId ∧ ∃ k ∈ e.contracts r.archetype, k.convention = r.convention := by
  simp only [replayTarget?, Option.filter_eq_some_iff] at h
  obtain ⟨hf, hp⟩ := h
  have hm := List.mem_of_find?_eq_some hf
  have hw := List.find?_some hf
  simp only [beq_iff_eq] at hw
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.any_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨hi, -⟩, -⟩, e, he, hid, k, hk, hc⟩ := hp
  exact ⟨hm, hw, hi, e, he, hid, k, hk, hc⟩

/-- "Deliver only to the selected endpoint"; "Ordinary `IntentDelivery`; `sender` is the
target's catalog identifier"; fields unchanged; otherwise fail. Never a chooser, a
default, a launch, retention, or another endpoint. -/
theorem replay_effects (w : World) (s : St) (r : Replay) :
    (∃ c, replayTarget? w s r = some c ∧ c.window = r.window ∧
      replay w s r = [.send c.port (deliverJson (replayDelivery c r))] ∧
      (replayDelivery c r).sender = c.catalogId ∧ (replayDelivery c r).payload = r.payload ∧
      (replayDelivery c r).convention = r.convention) ∨
    replay w s r = [.effect (.nap .intent "replayFailed" (.obj [("window", Json.nat r.window)]))] := by
  unfold replay
  split
  · rename_i c hc
    exact .inl ⟨c, hc, (replayTarget?_spec hc).2.1, rfl, rfl, rfl, rfl⟩
  · exact .inr rfl

/-- "User default changes after selection: keep the selected endpoint": the replay never
reads the defaults (nor the delivery queue or prompts). -/
theorem replay_ignores_defaults (w : World) (s : St) (r : Replay) (ds : List (String × String)) :
    replay w { s with defaults := ds } r = replay w s r := rfl

/-- A replay changes no runtime state. -/
theorem onEvent_replay_state (h : Host) (w : World) (s : St) (j : Json) :
    (onEvent h w s (.nap .intent "replay" j)).1 = s := by
  simp only [onEvent]; split <;> rfl

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
-- an invalid `handlerHint` address rejects the request instead of being ignored
#guard sendsSame (handle hst wFeed ctxFeed sCat (.invoke "i7"
    { archetype := "profile", action := "open", convention := "napplet:profile/open",
      hint := some { address := "30023:abc:x" } })).2
  [(1, "{ \"type\": \"intent.invoke.result\", \"id\": \"i7\", \"result\": { \"ok\": false, \"error\": \"invalid convention\" } }")]
private def goodHint : Hint := { address := "35129:" ++ String.ofList (List.replicate 64 'a') ++ ":d" }
private def reqGoodHint : Request :=
  { archetype := "profile", action := "open", convention := "napplet:profile/open", hint := some goodHint }
#guard convOk reqGoodHint
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
#guard (candidates { St.init with catalog := [⟨"x", none, [], [["napplet:profile/open"]], true⟩] } "profile").isEmpty

-- one contract per valid `i` tag, even with a repeated convention; actions/conventions deduplicated
private def eDup : Entry :=
  { id := "x", title := none, roles := ["profile"],
    intents := [["napplet:profile/open", "pubkey"], ["napplet:profile/open", "npub"]] }
#guard (eDup.contracts "profile").length == 2
#guard match candidates { St.init with catalog := [eDup] } "profile" with
  | [c] => c.conventions == ["napplet:profile/open"] && c.actions == ["open"] &&
      c.contracts.map (·.params) == [["pubkey"], ["npub"]]
  | _ => false

-- a non-dispatchable entry (R set unmet, or `intent` not exposed by policy) is no candidate
private def sNoDispatch : St := (onEvent hst wFeed .init (.nap .intent "catalog" (Json.parse!
  "{\"entries\":[{\"id\":\"v\",\"z\":[\"profile\"],\"i\":[[\"napplet:profile/open\"]],\"dispatchable\":false}]}"))).1
#guard sNoDispatch.catalog.map (·.dispatchable) == [false]
#guard (candidates sNoDispatch "profile").isEmpty && (roles sNoDispatch).isEmpty
#guard sendsSame (handle hst wFeed ctxFeed sNoDispatch invI1).2
  [(1, "{ \"type\": \"intent.invoke.result\", \"id\": \"i1\", \"result\": { \"ok\": false, \"error\": \"no handler\" } }")]
#guard (catalogOf? (Json.parse! "{\"entries\":[{\"id\":\"v\",\"z\":[],\"i\":[]}]}")).map (·.map (·.dispatchable)) == some [true]

-- explicit launch (PR #148)
private def pkA : String := String.ofList (List.replicate 64 'a')
private def ctxCat : Ctx :=
  { port := 3, window := 30,
    identity := { dTag := some "catalog", artifactHash := "h3", publisher := pkA },
    exposed := [.intent], inst := 0 }
private def ctxChess : Ctx :=
  { port := 4, window := 40,
    identity := { dTag := some "chess", artifactHash := "h4", publisher := pkA },
    exposed := [.intent], inst := 0 }
private def chessId : String := ctxChess.catalogId
private def sInst (cfg : Cfg) : St :=
  { (onEvent hst wFeed (St.init cfg) (.nap .intent "catalog" (Json.mkObj
    [("entries", some (.arr [Json.mkObj [("id", some (.str chessId)), ("z", some (Json.strs ["game"])),
       ("i", some (Json.tags [["napplet:game/open"]]))]]))]))).1 with }
private def tChess : Hint := { address := "35129:" ++ pkA ++ ":chess" }
private def tAbsent : Hint := { address := "35129:" ++ pkA ++ ":go", relays := some ["wss://relay.example.com"] }

#guard launchId? tChess.address == some chessId
#guard launchId? ("15129:" ++ pkA ++ ":") == some ("nip5d:15129:" ++ pkA)
#guard launchId? ("15129:" ++ pkA ++ ":") == some ({ dTag := none, artifactHash := "", publisher := pkA, kind := .root : Identity }.catalogId)
#guard launchId? ("15129:" ++ pkA ++ ":x") == none
#guard launchId? ("35129:" ++ pkA ++ ":") == none
#guard launchId? ("5129:" ++ pkA ++ ":") == none
#guard launchId? ("35129:" ++ String.ofList (List.replicate 64 'A') ++ ":chess") == none
#guard launchId? "35129:<pubkey>:profiles" == none

-- decode: the upstream requests; malformed target or behavior
#guard isOk (decode (Json.parse! "{ \"type\": \"intent.launch\", \"id\": \"l1\", \"target\": { \"address\": \"35129:<pubkey>:profiles\" } }"))
  (.launch "l1" { address := "35129:<pubkey>:profiles" } none)
#guard isOk (decode (Json.parse! "{ \"type\": \"intent.launch\", \"id\": \"l2\", \"target\": { \"address\": \"35129:<pubkey>:chess\", \"relays\": [\"wss://relay.example.com\"] } }"))
  (.launch "l2" { address := "35129:<pubkey>:chess", relays := some ["wss://relay.example.com"] } none)
#guard match decode (Json.parse! "{ \"type\": \"intent.launch\", \"id\": \"l4\", \"target\": \"naddr1x\" }") with
  | .reject [m] => Json.same m (Json.parse! "{ \"type\": \"intent.launch.result\", \"id\": \"l4\", \"result\": { \"ok\": false, \"error\": \"invalid target\" } }")
  | _ => false
#guard match decode (Json.parse! "{ \"type\": \"intent.launch\", \"id\": \"l4\", \"target\": { \"address\": \"a\" }, \"behavior\": 1 }") with
  | .reject [_] => true
  | _ => false
#guard decode (Json.parse! "{ \"type\": \"intent.launch\", \"target\": { \"address\": \"a\" } }") matches .reject []

-- upstream result examples, verbatim
#guard Json.same (launchOk "l1" "catalog-profile-viewer") (Json.parse! "{
     \"type\": \"intent.launch.result\",
     \"id\": \"l1\",
     \"result\": { \"ok\": true, \"handler\": \"catalog-profile-viewer\" }
   }")
#guard Json.same (launchOk "l2" "catalog-chess") (Json.parse! "{
     \"type\": \"intent.launch.result\",
     \"id\": \"l2\",
     \"result\": { \"ok\": true, \"handler\": \"catalog-chess\" }
   }")
#guard Json.same (launchErr "l3" "not installed") (Json.parse! "{
     \"type\": \"intent.launch.result\",
     \"id\": \"l3\",
     \"result\": { \"ok\": false, \"error\": \"not installed\" }
   }")

-- installed, confirmation on: prompt, then accept and open (no sender in the effect)
#guard match (handle hst wFeed ctxCat (sInst {}) (.launch "l1" tChess none)).2 with
  | [.call ⟨.intent, 0⟩ (.prompt .intent "launch" d)] =>
      Json.same d (Json.mkObj [("sender", some (.str ctxCat.catalogId)), ("handler", some (.str chessId)),
        ("address", some (.str tChess.address)), ("installed", some (.bool true))])
  | _ => false
private def sL1 : St := (handle hst wFeed ctxCat (sInst {}) (.launch "l1" tChess none)).1
#guard (onReply hst wFeed sL1 0 (.decision true none)).2 ==
  [.send 3 (launchOk "l1" chessId), .effect (.nap .intent "open" (Json.mkObj [("handler", some (.str chessId))]))]
#guard (onReply hst wFeed sL1 0 (.decision true none)).1.launching == []
#guard (onReply hst wFeed sL1 0 (.decision false none)).2 == [.send 3 (launchErr "l1" "user cancelled")]
#guard (drop sL1 3).2 == [.effect (.cancel ⟨.intent, 0⟩)] && !mentions (drop sL1 3).1 3
-- installed, confirmation off: accepted at once; defaults and catalog untouched, no delivery
#guard (handle hst wFeed ctxCat (sInst { confirmLaunch := false }) (.launch "l1" tChess (some { focus := some true }))).2 ==
  [.send 3 (launchOk "l1" chessId),
   .effect (.nap .intent "open" (Json.parse! ("{\"handler\":\"" ++ chessId ++ "\",\"behavior\":{\"focus\":true}}")))]
-- a user default for the role never redirects a launch
#guard (handle hst wFeed ctxCat ({ sInst { confirmLaunch := false } with defaults := [("game", "other")] })
    (.launch "l1" tChess none)).2.head? == some (.send 3 (launchOk "l1" chessId))
-- absent: not installed (default), launch rejected (privacy), or offered for installation
#guard (handle hst wFeed ctxCat (sInst {}) (.launch "l3" tAbsent none)).2 == [.send 3 (launchErr "l3" "not installed")]
#guard (handle hst wFeed ctxCat (sInst { absent := .rejected }) (.launch "l3" tAbsent none)).2 ==
  [.send 3 (launchErr "l3" "launch rejected")]
#guard (handle hst wFeed ctxCat (sInst { absent := .offerInstall, confirmLaunch := false }) (.launch "l2" tAbsent none)).2 ==
  [.send 3 (launchOk "l2" ("nip5d:35129:" ++ pkA ++ ":go")),
   .effect (.nap .intent "install" (Json.mkObj [("handler", some (.str ("nip5d:35129:" ++ pkA ++ ":go"))),
     ("address", some (.str tAbsent.address)), ("relays", some (Json.strs ["wss://relay.example.com"]))]))]
-- invalid targets
#guard (handle hst wFeed ctxCat (sInst {}) (.launch "l5" { address := "5129:" ++ pkA ++ ":" } none)).2 ==
  [.send 3 (launchErr "l5" "invalid target")]

-- selected-instance delivery (PR #128): two instances of the same manifest
private def ctxChess2 : Ctx := { ctxChess with port := 5, window := 50 }
private def wTwo : World := { now := 0, live := [ctxCat, ctxChess, ctxChess2], user := "" }
private def replayEv (win : Nat) (conv : String) : HostEvent := .nap .intent "replay" (Json.mkObj
  [("window", some (Json.nat win)), ("archetype", some (.str "game")), ("action", some (.str "open")),
   ("convention", some (.str conv)), ("payload", some (Json.parse! "{ \"move\": \"e4\" }"))])
#guard sendsSame (onEvent hst wTwo (sInst {}) (replayEv 50 "napplet:game/open")).2
  [(5, "{ \"type\": \"intent.deliver\", \"delivery\": { \"sender\": \"" ++ chessId ++ "\", \"archetype\": \"game\", \"action\": \"open\", \"convention\": \"napplet:game/open\", \"payload\": { \"move\": \"e4\" } } }")]
-- not advertised by the selected instance, a dead window, or an instance without `intent`: fail
#guard (onEvent hst wTwo (sInst {}) (replayEv 50 "napplet:game/edit")).2 ==
  [.effect (.nap .intent "replayFailed" (.obj [("window", Json.nat 50)]))]
#guard (onEvent hst wTwo (sInst {}) (replayEv 60 "napplet:game/open")).2 ==
  [.effect (.nap .intent "replayFailed" (.obj [("window", Json.nat 60)]))]
#guard (onEvent hst { wTwo with live := [{ ctxChess2 with exposed := [] }] } (sInst {}) (replayEv 50 "napplet:game/open")).2 ==
  [.effect (.nap .intent "replayFailed" (.obj [("window", Json.nat 50)]))]
-- the catalog entry of another napplet does not make an instance eligible
#guard (onEvent hst wTwo (sInst {}) (replayEv 30 "napplet:game/open")).2 ==
  [.effect (.nap .intent "replayFailed" (.obj [("window", Json.nat 30)]))]
-- a napplet-supplied instance selector or sender is ignored by `intent.invoke`
#guard isOk (decode (Json.parse! "{ \"type\": \"intent.invoke\", \"id\": \"i9\", \"request\": { \"archetype\": \"game\", \"action\": \"open\", \"convention\": \"napplet:game/open\", \"sender\": \"x\", \"instance\": 50, \"window\": 50 } }"))
  (.invoke "i9" { archetype := "game", action := "open", convention := "napplet:game/open" })

end vectors

end Napplet.Run.Intent
