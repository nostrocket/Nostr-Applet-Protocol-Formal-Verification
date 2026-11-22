/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Outbox
import Napplet.Net

/-!
# NAP-OUTBOX runtime component

Upstream: `napplet/naps` PR #32 (branch `nap-outbox`), `naps/NAP-OUTBOX.md` at `8865f73d`.

Wire (napplet → shell):
`outbox.getEvent {id, eventId, options?}`, `outbox.query {id, filters, options?}`,
`outbox.subscribe {id, subId, filters, options?}`, `outbox.close {id, subId}`,
`outbox.publish {id, event, options?}`, `outbox.resolveRelays {id, target}`.

Wire (shell → napplet):
`outbox.getEvent.result {id, result?, incomplete?, error?}`,
`outbox.query.result {id, events, incomplete?, error?}`, `outbox.event {subId, result}`,
`outbox.closed {subId, reason?}`, `outbox.publish.result {id, ok, event?, eventId?, relays?,
error?}`, `outbox.resolveRelays.result {id, plan, error?}`. There is no `outbox.eose`.

`result`/`events[i]` are NAP-RELAY `RelayEventResult`s `{event, sidecar?: {relayHints?}}`;
`plan` is `{relays, source, missingAuthors?}`; `relays` in a publish result maps relay URL
to `bool`.

`filters` is one NIP-01 filter object or a non-empty array of them (carried opaquely; the
model always re-encodes an array). Options are decoded field by field; a present field of
the wrong JSON type makes the request malformed.

## Routing (NIP-65 outbox model)

Every operation first resolves NIP-65 relay lists with `Call.relayList`, one call per
distinct pubkey, in parallel; when all have answered it continues:

* **Reads** (`getEvent`, `query`, `subscribe`): authors are `options.author` (getEvent),
  or every filter's `authors` plus `options.authors`. The read set is the authors'
  NIP-65 *write* relays that pass `Cfg.allowed`; if that is empty, `Cfg.fallback`
  (allowed); then allowed `options.relays` hints are added; deduplicated. Authors without
  a usable list are missing and make the answer `incomplete: true`. An empty set means the
  shell's pool (`Call.subscribe … none`). `getEvent` queries `{"ids": [eventId]}` (plus
  `"authors": [author]` when hinted).
* **Publish**: lookups for the user (unless `toOutbox: false`) and every `toInboxes`
  author, then `NapOutbox.plan` (own write set or fallback, every resolved inbox *read*
  relay, validated `options.relays`; all filtered by `Cfg.allowed`; deduplicated). An
  empty plan fails with `"relay list unavailable"`. Otherwise the template is stamped
  with the user's key and the shell clock and signed once (`Call.sign`), and that one
  event is published to the plan (`Call.publish ev (some plan)`). Unresolved inbox authors
  are reported with `error: "relay list unavailable"` while the resolved relays are still
  used (modelling decision 14).
* **resolveRelays**: `direction` `read` (default) uses the authors' write relays (where
  their events are), `write` their read relays (their inboxes); `source` is `nip65` when
  any NIP-65 relay survived policy, else `fallback` with `Cfg.fallback`.

Read results are verified: an `event` reply failing `h.verifyEvent` has no effect at all.
`getEvent` returns only an event whose id is `eventId`; `query` deduplicates by id
(merging relay hints) and applies `options.limit`; a subscription delivers each id once.
EOSE ends `getEvent`/`query` (the host subscription is stopped); it is not forwarded for
subscriptions. A pool `closed` ends any read: partial results with `incomplete: true` and
`error` (the pool's reason, else `"relay timeout"`), or `outbox.closed {subId, reason?}`.

`timeoutMs` is carried but not interpreted: the host's relay layer enforces timeouts by
ending the stream (`closed`), as `Host` requires.

ACL: `Cfg.canRead` gates reads and relay discovery (`"policy denied"`), `Cfg.canWrite`
gates publishing (`"publish denied"`); no user gives `"no signer configured"`. Content that
looks like napplet ciphertext is never signed (`"blocked: ciphertext from napplet"`,
NIP-5D §Security 7). A template whose raw `event` carries a string `pubkey` other
than the shell user's is refused with `"publish denied"` instead of being re-stamped
(NAP-POW: a mined event is signed verbatim or rejected; the template codec drops
`pubkey`, so it is read from the raw JSON as `Req.publish … pk`). `outbox.close` is
answered with `outbox.closed {subId}` (kehto does the same); an `outbox.subscribe` that
reuses a live `subId` stops the earlier subscription silently, with no `outbox.closed`.

Relay URLs (NIP-65 lists, `options.relays` hints, fallbacks) pass `Cfg.allowed`, by
default `Net.relayAllowed`: `wss://`, no localhost/`.local`/`.home.arpa` or dotless
names, no private or reserved IP literals (NAP-OUTBOX: napplets MUST NOT force
connections to private network relays). DNS names that resolve to private addresses are
refused by the host (`Napplet.Host`).

Malformed requests: bad `filters`/`eventId` → `"invalid filter"` (upstream error string),
anything else → `"invalid request"`, in the request's result envelope (`events: []` for
query, `ok: false` for publish, an empty `plan {relays: [], source: "policy"}` for
resolveRelays since `plan` is required); `outbox.subscribe` with a string `subId` →
`outbox.closed {subId, reason}`; `outbox.close` or no usable id → nothing.

## Host operations

Only core host calls; no `Call.nap`, `Effect.nap`, `HostEvent.nap` or `Call.prompt`.

* `Call.relayList pubkey` → `relayList (some entries)` / `relayList none` (NIP-65 kind
  10002, from cache or relays).
* `Call.subscribe filters relays` → stream `event ev relay`, `eose`, `closed reason?`;
  stopped with `Effect.unsubscribe`.
* `Call.sign unsigned` → `signed (some ev)` / `signed none` (refused: `"publish denied"`).
* `Call.publish ev (some relays)` → `published acks` (one `(relay, accepted)` per relay;
  becomes the `relays` map; `ok` iff some relay accepted, else `"publish failed"`).
* `Effect.unsubscribe`, `Effect.cancel` on EOSE, close, replacement and teardown.
-/

namespace Napplet.Run.Outbox

open NapOutbox (dedup)

/-- Shell policy for the outbox domain. -/
structure Cfg where
  canRead : Identity → Bool := fun _ => true
  canWrite : Identity → Bool := fun _ => true
  /-- Relay URL policy (valid, allowed, not a private host). -/
  allowed : String → Bool := Net.relayAllowed
  /-- Configured fallback relays (reads and the user's own write set only). -/
  fallback : List String := []
  /-- Attach `sidecar.relayHints` with the observed relay. -/
  relayHints : Bool := true

structure EventOpts where
  author : Option String := none
  relays : Option (List String) := none
  timeoutMs : Option Nat := none
  deriving DecidableEq, Repr

/-- `OutboxQueryOptions` and `OutboxSubscribeOptions` (same fields). -/
structure ReadOpts where
  authors : Option (List String) := none
  relays : Option (List String) := none
  limit : Option Nat := none
  timeoutMs : Option Nat := none
  deriving DecidableEq, Repr

structure PubOpts where
  relays : Option (List String) := none
  toOutbox : Option Bool := none
  toInboxes : Option (List String) := none
  deriving DecidableEq, Repr

inductive Direction where
  | read
  | write
  deriving DecidableEq, Repr

structure Target where
  authors : Option (List String) := none
  pubkey : Option String := none
  direction : Option Direction := none
  deriving DecidableEq, Repr

inductive Req where
  | getEvent (id eventId : String) (o : Option EventOpts)
  | query (id : String) (filters : List Json) (o : Option ReadOpts)
  | subscribe (id subId : String) (filters : List Json) (o : Option ReadOpts)
  | close (id subId : String)
  /-- `pk`: the string `pubkey` member of the raw `event`, if any. -/
  | publish (id : String) (t : EventTemplate) (o : Option PubOpts) (pk : Option String)
  | resolveRelays (id : String) (t : Target)
  deriving DecidableEq, Repr

/-- Well-formed request: filter lists are non-empty lists of objects. -/
def Req.WF : Req → Prop
  | .query _ fs _ => fs ≠ [] ∧ fs.all Json.isObj = true
  | .subscribe _ _ fs _ => fs ≠ [] ∧ fs.all Json.isObj = true
  | _ => True

/-! ### Codec -/

def optField {α : Type} (j : Json) (k : String) (f : Json → Option α) : Option (Option α) :=
  match j.get? k with
  | none => some none
  | some v => (f v).map some

def EventOpts.ofJson? (j : Json) : Option EventOpts := do
  guard j.isObj
  some { author := ← optField j "author" Json.asStr?, relays := ← optField j "relays" Json.asStrs?,
         timeoutMs := ← optField j "timeoutMs" Json.asNat? }

def EventOpts.toJson (o : EventOpts) : Json :=
  Json.mkObj [("author", o.author.map .str), ("relays", o.relays.map Json.strs),
              ("timeoutMs", o.timeoutMs.map Json.nat)]

def ReadOpts.ofJson? (j : Json) : Option ReadOpts := do
  guard j.isObj
  some { authors := ← optField j "authors" Json.asStrs?, relays := ← optField j "relays" Json.asStrs?,
         limit := ← optField j "limit" Json.asNat?, timeoutMs := ← optField j "timeoutMs" Json.asNat? }

def ReadOpts.toJson (o : ReadOpts) : Json :=
  Json.mkObj [("authors", o.authors.map Json.strs), ("relays", o.relays.map Json.strs),
              ("limit", o.limit.map Json.nat), ("timeoutMs", o.timeoutMs.map Json.nat)]

def PubOpts.ofJson? (j : Json) : Option PubOpts := do
  guard j.isObj
  some { relays := ← optField j "relays" Json.asStrs?, toOutbox := ← optField j "toOutbox" Json.asBool?,
         toInboxes := ← optField j "toInboxes" Json.asStrs? }

def PubOpts.toJson (o : PubOpts) : Json :=
  Json.mkObj [("relays", o.relays.map Json.strs), ("toOutbox", o.toOutbox.map .bool),
              ("toInboxes", o.toInboxes.map Json.strs)]

def Direction.ofJson? : Json → Option Direction
  | .str "read" => some .read
  | .str "write" => some .write
  | _ => none

def Direction.toJson : Direction → Json
  | .read => .str "read"
  | .write => .str "write"

def Target.ofJson? (j : Json) : Option Target := do
  guard j.isObj
  some { authors := ← optField j "authors" Json.asStrs?, pubkey := ← optField j "pubkey" Json.asStr?,
         direction := ← optField j "direction" Direction.ofJson? }

def Target.toJson (t : Target) : Json :=
  Json.mkObj [("authors", t.authors.map Json.strs), ("pubkey", t.pubkey.map .str),
              ("direction", t.direction.map Direction.toJson)]

/-- One filter object or a non-empty array of filter objects. -/
def filtersOf? (j : Json) : Option (List Json) :=
  match j.get? "filters" with
  | some (.arr fs) => if fs ≠ [] ∧ fs.all Json.isObj then some fs else none
  | some (.obj kvs) => some [.obj kvs]
  | _ => none

def templateOf? (j : Json) : Option EventTemplate := (j.get? "event").bind EventTemplate.ofJson?

def resultJson (ev : NostrEvent) (hints : List String) : Json :=
  Json.mkObj [("event", some ev.toJson),
              ("sidecar", if hints.isEmpty then none else some (.obj [("relayHints", Json.strs hints)]))]

def incJson (inc : Bool) : Option Json := if inc then some (.bool true) else none

/-- Relays of a NIP-65 list that the entry marks for writing / reading. -/
def writeOf (es : List RelayEntry) : List String := (es.filter (·.write)).map (·.url)
def readOf (es : List RelayEntry) : List String := (es.filter (·.read)).map (·.url)

/-- Pick the `getEvent` answer: the first collected event with the requested id whose
signature verifies (`NapOutbox.getEvent`). -/
def pick (h : Host) (eid : String) (acc : List (NostrEvent × List String)) :
    Option (NostrEvent × List String) :=
  acc.find? fun x => x.1.id == eid && h.verifyEvent x.1

/-- Keep one event per id (`NapOutbox.dedupById`). -/
def dedupById : List (NostrEvent × List String) → List (NostrEvent × List String)
  | [] => []
  | x :: xs => if (dedupById xs).any (·.1.id == x.1.id) then dedupById xs else x :: dedupById xs

/-- `outbox.query` results: verified, deduplicated by id, at most `limit`. -/
def queryEvents (h : Host) (lim : Option Nat) (acc : List (NostrEvent × List String)) :
    List (NostrEvent × List String) :=
  let es := dedupById (acc.filter fun x => h.verifyEvent x.1)
  match lim with
  | some l => es.take l
  | none => es

def getEventMsg (h : Host) (id eid : String) (acc : List (NostrEvent × List String)) (inc : Bool)
    (err : Option String) : Json :=
  match pick h eid acc with
  | some x => Json.msg "outbox.getEvent.result"
      [("id", some (.str id)), ("result", some (resultJson x.1 x.2)), ("incomplete", incJson inc),
       ("error", err.map .str)]
  | none => Json.msg "outbox.getEvent.result"
      [("id", some (.str id)), ("incomplete", incJson inc),
       ("error", some (.str (err.getD "not found")))]

def getEventErr (id err : String) : Json :=
  Json.msg "outbox.getEvent.result" [("id", some (.str id)), ("error", some (.str err))]

def queryMsg (h : Host) (id : String) (lim : Option Nat) (acc : List (NostrEvent × List String))
    (inc : Bool) (err : Option String) : Json :=
  Json.msg "outbox.query.result"
    [("id", some (.str id)), ("events", some (.arr ((queryEvents h lim acc).map fun x => resultJson x.1 x.2))),
     ("incomplete", incJson inc), ("error", err.map .str)]

def queryErr (id err : String) : Json :=
  Json.msg "outbox.query.result" [("id", some (.str id)), ("events", some (.arr [])), ("error", some (.str err))]

def eventMsg (sid : String) (ev : NostrEvent) (hints : List String) : Json :=
  Json.msg "outbox.event" [("subId", some (.str sid)), ("result", some (resultJson ev hints))]

def closedMsg (sid : String) (reason : Option String) : Json :=
  Json.msg "outbox.closed" [("subId", some (.str sid)), ("reason", reason.map .str)]

def pubMsg (id : String) (ok : Bool) (ev : Option NostrEvent) (acks : Option (List (String × Bool)))
    (err : Option String) : Json :=
  Json.msg "outbox.publish.result"
    [("id", some (.str id)), ("ok", some (.bool ok)), ("event", ev.map NostrEvent.toJson),
     ("eventId", ev.map fun e => .str e.id),
     ("relays", acks.map fun a => .obj (a.map fun x => (x.1, .bool x.2))), ("error", err.map .str)]

def planMsg (id : String) (relays : List String) (source : String) (missing : List String)
    (err : Option String) : Json :=
  Json.msg "outbox.resolveRelays.result"
    [("id", some (.str id)),
     ("plan", some (Json.mkObj [("relays", some (Json.strs relays)), ("source", some (.str source)),
        ("missingAuthors", if missing.isEmpty then none else some (Json.strs missing))])),
     ("error", err.map .str)]

def requestTypes : List String :=
  ["outbox.getEvent", "outbox.query", "outbox.subscribe", "outbox.close", "outbox.publish",
   "outbox.resolveRelays"]

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | none => .unknown
  | some t =>
    if t ∉ requestTypes then .unknown else
    if t = "outbox.subscribe" then
      match j.getStr? "subId" with
      | none => .reject []
      | some sid =>
        match reqId? j, filtersOf? j, optField j "options" ReadOpts.ofJson? with
        | some id, some fs, some o => .ok (.subscribe id sid fs o)
        | some _, none, _ => .reject [closedMsg sid (some "invalid filter")]
        | _, _, _ => .reject [closedMsg sid (some "invalid request")]
    else if t = "outbox.close" then
      match reqId? j, j.getStr? "subId" with
      | some id, some sid => .ok (.close id sid)
      | _, _ => .reject []
    else
    match reqId? j with
    | none => .reject []
    | some id =>
      if t = "outbox.getEvent" then
        match j.getStr? "eventId", optField j "options" EventOpts.ofJson? with
        | some eid, some o => .ok (.getEvent id eid o)
        | none, _ => .reject [getEventErr id "invalid filter"]
        | _, none => .reject [getEventErr id "invalid request"]
      else if t = "outbox.query" then
        match filtersOf? j, optField j "options" ReadOpts.ofJson? with
        | some fs, some o => .ok (.query id fs o)
        | none, _ => .reject [queryErr id "invalid filter"]
        | _, none => .reject [queryErr id "invalid request"]
      else if t = "outbox.publish" then
        match templateOf? j, optField j "options" PubOpts.ofJson? with
        | some tp, some o => .ok (.publish id tp o ((j.get? "event").bind Net.claimedPubkey?))
        | _, _ => .reject [pubMsg id false none none (some "invalid request")]
      else
        match (j.get? "target").bind Target.ofJson? with
        | some tg => .ok (.resolveRelays id tg)
        | none => .reject [planMsg id [] "policy" [] (some "invalid request")]

def encodeReq : Req → Json
  | .getEvent id eid o => Json.msg "outbox.getEvent"
      [("id", some (.str id)), ("eventId", some (.str eid)), ("options", o.map EventOpts.toJson)]
  | .query id fs o => Json.msg "outbox.query"
      [("id", some (.str id)), ("filters", some (.arr fs)), ("options", o.map ReadOpts.toJson)]
  | .subscribe id sid fs o => Json.msg "outbox.subscribe"
      [("id", some (.str id)), ("subId", some (.str sid)), ("filters", some (.arr fs)),
       ("options", o.map ReadOpts.toJson)]
  | .close id sid => Json.msg "outbox.close" [("id", some (.str id)), ("subId", some (.str sid))]
  | .publish id t o pk => Json.msg "outbox.publish"
      [("id", some (.str id)), ("event", some (Net.withPubkey t.toJson pk)),
       ("options", o.map PubOpts.toJson)]
  | .resolveRelays id tg => Json.msg "outbox.resolveRelays"
      [("id", some (.str id)), ("target", some tg.toJson)]

/-! ### State -/

abbrev Lists := List (Pubkey × Option (List RelayEntry))

inductive Kind where
  | getEvent (id eventId : String)
  | query (id : String) (limit : Option Nat)
  | sub (subId : String)
  deriving DecidableEq, Repr

/-- What a request does once its relay lists are known. -/
inductive Goal where
  | read (k : Kind) (filters : List Json) (authors : List Pubkey) (hints : List String)
  | publish (id : String) (t : EventTemplate) (o : NapOutbox.PublishOptions) (user : Pubkey)
  | resolve (id : String) (dir : Direction) (authors : List Pubkey)
  deriving DecidableEq, Repr

inductive Job where
  /-- Waiting for the relay-list lookups whose `parent` is this entry. -/
  | plan (g : Goal) (lists : Lists)
  | lookup (parent : Nat) (author : Pubkey)
  /-- A live host subscription; `acc` holds collected (or, for `sub`, delivered) events. -/
  | read (k : Kind) (incomplete : Bool) (acc : List (NostrEvent × List String))
  | sign (id : String) (o : NapOutbox.PublishOptions) (user : Pubkey) (lists : Lists)
  | publish (id : String) (ev : NostrEvent) (missing : List Pubkey)
  deriving DecidableEq, Repr

structure Entry where
  n : Nat
  job : Job
  deriving DecidableEq, Repr

abbrev Bucket := List Entry

structure St where
  cfg : Cfg
  buckets : List (PortId × Bucket)
  next : Nat

def St.init (cfg : Cfg := {}) : St := { cfg, buckets := [], next := 0 }

def St.bucket (s : St) (p : PortId) : Bucket :=
  ((s.buckets.find? (·.1 == p)).map (·.2)).getD []

def St.put (s : St) (p : PortId) (b : Bucket) : List (PortId × Bucket) :=
  if b.isEmpty then s.buckets.filter (·.1 != p)
  else if s.buckets.any (·.1 == p) then s.buckets.map fun x => (x.1, if x.1 == p then b else x.2)
  else (p, b) :: s.buckets

def tag (n : Nat) : CallTag := ⟨.outbox, n⟩

/-! ### Planning -/

def listOf (ls : Lists) (a : Pubkey) : Option (List RelayEntry) := (ls.find? (·.1 == a)).bind (·.2)

/-- The `NapOutbox` environment for a publish: resolved lists, fallback and policy.
(`sign`/`verify` are not used by `NapOutbox.plan`.) -/
def envOf (cfg : Cfg) (user : Pubkey) (ls : Lists) : NapOutbox.OutboxEnv where
  userWrite := ((listOf ls user).map writeOf).getD []
  readRelays a := match listOf ls a with
    | some es => if readOf es = [] then none else some (readOf es)
    | none => none
  fallback := cfg.fallback
  allowed := cfg.allowed
  sign t := ⟨"", "", t.kind, t.content, ""⟩
  verify _ := true

def pubOptsOf (o : Option PubOpts) : NapOutbox.PublishOptions :=
  { relays := (o.bind (·.relays)).getD [], toOutbox := (o.bind (·.toOutbox)).getD true,
    toInboxes := dedup ((o.bind (·.toInboxes)).getD []) }

/-- Read routing: authors' write relays, else fallback, plus hints; all allowed. -/
def readPlan (cfg : Cfg) (authors : List Pubkey) (ls : Lists) (hints : List String) :
    List String × List Pubkey :=
  let rel (a : Pubkey) := ((listOf ls a).map writeOf).getD []
  let found := (authors.flatMap rel).filter cfg.allowed
  let base := if found.isEmpty then cfg.fallback.filter cfg.allowed else found
  (dedup (base ++ hints.filter cfg.allowed), authors.filter fun a => (rel a).isEmpty)

def resolvePlan (cfg : Cfg) (dir : Direction) (authors : List Pubkey) (ls : Lists) :
    List String × String × List Pubkey :=
  let rel (a : Pubkey) := ((listOf ls a).map fun es => match dir with
    | .read => writeOf es | .write => readOf es).getD []
  let found := dedup ((authors.flatMap rel).filter cfg.allowed)
  (if found.isEmpty then dedup (cfg.fallback.filter cfg.allowed) else found,
   if found.isEmpty then "fallback" else "nip65",
   authors.filter fun a => (rel a).isEmpty)

def filterAuthors (fs : List Json) : List String :=
  fs.flatMap fun f => ((f.get? "authors").bind Json.asStrs?).getD []

def hintsOf (cfg : Cfg) (relay : String) : List String :=
  if cfg.relayHints && relay != "" then [relay] else []

def merge (acc : List (NostrEvent × List String)) (ev : NostrEvent) (hs : List String) :
    List (NostrEvent × List String) :=
  if acc.any (·.1.id == ev.id) then
    acc.map fun x => if x.1.id == ev.id then (x.1, x.2 ++ hs.filter (· ∉ x.2)) else x
  else acc ++ [(ev, hs)]

/-- All lookups answered: continue the goal for entry `n` (`none`: entry finished). -/
def complete (h : Host) (cfg : Cfg) (now : Nat) (port : PortId) (n : Nat) (g : Goal) (ls : Lists) :
    Option Job × List Eff :=
  match g with
  | .read k fs authors hints =>
    let p := readPlan cfg authors ls hints
    (some (.read k (!p.2.isEmpty) []),
     [.call (tag n) (.subscribe fs (if p.1.isEmpty then none else some p.1))])
  | .publish id t o user =>
    if h.looksCiphertext t.content then
      (none, [.send port (pubMsg id false none none (some "blocked: ciphertext from napplet"))])
    else if (NapOutbox.plan (envOf cfg user ls) o).isEmpty then
      (none, [.send port (pubMsg id false none none (some "relay list unavailable"))])
    else (some (.sign id o user ls), [.call (tag n) (.sign (t.stamp user now))])
  | .resolve id dir authors =>
    let p := resolvePlan cfg dir authors ls
    (none, [.send port (planMsg id p.1 p.2.1 p.2.2 none)])

def lookups (parent start : Nat) : List Pubkey → Bucket × List Eff
  | [] => ([], [])
  | a :: as =>
    let r := lookups parent (start + 1) as
    (⟨start, .lookup parent a⟩ :: r.1, .call (tag start) (.relayList a) :: r.2)

/-- Start a goal: issue the lookups, or complete at once when there are none. -/
def startPlan (h : Host) (cfg : Cfg) (now : Nat) (port : PortId) (nx : Nat) (b : Bucket)
    (g : Goal) (want : List Pubkey) : Bucket × List Eff × Nat :=
  if want.isEmpty then
    let c := complete h cfg now port nx g []
    ((c.1.map fun j => [⟨nx, j⟩]).getD [] ++ b, c.2, nx + 1)
  else
    let l := lookups nx (nx + 1) want
    (⟨nx, .plan g []⟩ :: l.1 ++ b, l.2, nx + 1 + want.length)

/-! ### Bucket operations -/

def isSubOf (sid : String) (e : Entry) : Bool :=
  match e.job with
  | .read (.sub s) _ _ => s == sid
  | .plan (.read (.sub s) _ _ _) _ => s == sid
  | _ => false

def lookupOf (n : Nat) (e : Entry) : Bool :=
  match e.job with
  | .lookup p _ => p == n
  | _ => false

def setJob (b : Bucket) (n : Nat) (j : Job) : Bucket :=
  b.map fun e => if e.n == n then ⟨e.n, j⟩ else e

/-- Stop one entry: a live subscription is unsubscribed, any other call cancelled; a plan
has no call of its own. -/
def stopEff (e : Entry) : Option Eff :=
  match e.job with
  | .read .. => some (.effect (.unsubscribe (tag e.n)))
  | .plan .. => none
  | _ => some (.effect (.cancel (tag e.n)))

/-- Remove the caller's subscription `sid` (at any stage) and its lookups. -/
def stopSub (b : Bucket) (sid : String) : Bucket × List Eff :=
  let subs := b.filter (isSubOf sid)
  let gone (e : Entry) : Bool := isSubOf sid e || subs.any fun s => lookupOf s.n e
  (b.filter (fun e => !gone e), (b.filter gone).filterMap stopEff)

/-! ### Requests -/

def stepReq (h : Host) (w : World) (cx : Ctx) (cfg : Cfg) (nx : Nat) (b : Bucket) :
    Req → Bucket × List Eff × Nat
  | .getEvent id eid o =>
    if !cfg.canRead cx.identity then (b, [.send cx.port (getEventErr id "policy denied")], nx) else
    let author := o.bind (·.author)
    let filter := Json.mkObj [("ids", some (Json.strs [eid])), ("authors", author.map fun a => Json.strs [a])]
    startPlan h cfg w.now cx.port nx b
      (.read (.getEvent id eid) [filter] author.toList ((o.bind (·.relays)).getD [])) author.toList
  | .query id fs o =>
    if !cfg.canRead cx.identity then (b, [.send cx.port (queryErr id "policy denied")], nx) else
    let authors := dedup (filterAuthors fs ++ (o.bind (·.authors)).getD [])
    startPlan h cfg w.now cx.port nx b
      (.read (.query id (o.bind (·.limit))) fs authors ((o.bind (·.relays)).getD [])) authors
  | .subscribe _ sid fs o =>
    if !cfg.canRead cx.identity then (b, [.send cx.port (closedMsg sid (some "policy denied"))], nx) else
    let st := stopSub b sid
    let authors := dedup (filterAuthors fs ++ (o.bind (·.authors)).getD [])
    let r := startPlan h cfg w.now cx.port nx st.1
      (.read (.sub sid) fs authors ((o.bind (·.relays)).getD [])) authors
    (r.1, st.2 ++ r.2.1, r.2.2)
  | .close _ sid =>
    let st := stopSub b sid
    (st.1, st.2 ++ [.send cx.port (closedMsg sid none)], nx)
  | .publish id t o pk =>
    if !cfg.canWrite cx.identity || !Net.pubkeyOk w.user pk then
      (b, [.send cx.port (pubMsg id false none none (some "publish denied"))], nx)
    else if w.user = "" then
      (b, [.send cx.port (pubMsg id false none none (some "no signer configured"))], nx)
    else if h.looksCiphertext t.content then
      (b, [.send cx.port (pubMsg id false none none (some "blocked: ciphertext from napplet"))], nx)
    else
      let po := pubOptsOf o
      startPlan h cfg w.now cx.port nx b (.publish id t po w.user)
        (dedup ((if po.toOutbox then [w.user] else []) ++ po.toInboxes))
  | .resolveRelays id tg =>
    if !cfg.canRead cx.identity then
      (b, [.send cx.port (planMsg id [] "policy" [] (some "policy denied"))], nx) else
    let authors := dedup (tg.authors.getD [] ++ tg.pubkey.toList)
    startPlan h cfg w.now cx.port nx b (.resolve id (tg.direction.getD .read) authors) authors

/-! ### Replies -/

/-- A relay-list lookup for plan `parent` answered (`l = none`: unavailable). -/
def onLookup (h : Host) (cfg : Cfg) (now : Nat) (port : PortId) (rest : Bucket) (parent : Nat)
    (a : Pubkey) (l : Option (List RelayEntry)) : Bucket × List Eff :=
  match rest.find? (·.n == parent) with
  | some ⟨_, .plan g ls⟩ =>
    let ls' := ls ++ [(a, l)]
    if rest.any (lookupOf parent) then (setJob rest parent (.plan g ls'), [])
    else
      let c := complete h cfg now port parent g ls'
      (match c.1 with
       | some j => setJob rest parent j
       | none => rest.filter (·.n != parent), c.2)
  | _ => (rest, [])

def stepReply (h : Host) (w : World) (cfg : Cfg) (nx : Nat) (port : PortId) (b : Bucket)
    (n : Nat) (rep : Reply) : Bucket × List Eff × Nat :=
  match b.find? (·.n == n) with
  | none => (b, [], nx)
  | some e =>
    let rest := b.filter (·.n != n)
    match e.job, rep with
    | .lookup parent a, rep =>
      let o := onLookup h cfg w.now port rest parent a (match rep with | .relayList r => r | _ => none)
      (o.1, o.2, nx)
    | .read k inc acc, .event ev r =>
      let hs := hintsOf cfg r
      match k with
      | .getEvent _ eid =>
        if ev.id == eid then (setJob b n (.read k inc (merge acc ev hs)), [], nx) else (b, [], nx)
      | .query .. => (setJob b n (.read k inc (merge acc ev hs)), [], nx)
      | .sub sid =>
        if acc.any (·.1.id == ev.id) then (b, [], nx)
        else (setJob b n (.read k inc (acc ++ [(ev, [])])), [.send port (eventMsg sid ev hs)], nx)
    | .read k inc acc, .eose =>
      match k with
      | .getEvent id eid =>
        (rest, [.effect (.unsubscribe (tag n)), .send port (getEventMsg h id eid acc inc none)], nx)
      | .query id lim =>
        (rest, [.effect (.unsubscribe (tag n)), .send port (queryMsg h id lim acc inc none)], nx)
      | .sub _ => (b, [], nx)
    | .read k _ acc, .closed reason =>
      match k with
      | .getEvent id eid =>
        (rest, [.send port (getEventMsg h id eid acc true (some (reason.getD "relay timeout")))], nx)
      | .query id lim =>
        (rest, [.send port (queryMsg h id lim acc true (some (reason.getD "relay timeout")))], nx)
      | .sub sid => (rest, [.send port (closedMsg sid reason)], nx)
    | .sign id o user ls, .signed (some ev) =>
      let env := envOf cfg user ls
      (⟨nx, .publish id ev (NapOutbox.missingInboxes env o)⟩ :: rest,
       [.call (tag nx) (.publish ev (some (NapOutbox.plan env o)))], nx + 1)
    | .sign id _ _ _, _ => (rest, [.send port (pubMsg id false none none (some "publish denied"))], nx)
    | .publish id ev missing, .published acks =>
      let ok := acks.any (·.2)
      (rest, [.send port (pubMsg id ok (some ev) (some acks)
        (if !missing.isEmpty then some "relay list unavailable"
         else if ok then none else some "publish failed"))], nx)
    | .publish id ev _, _ =>
      (rest, [.send port (pubMsg id false (some ev) none (some "publish failed"))], nx)
    | _, _ => (b, [], nx)

/-! ### Component -/

def handle (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) : St × List Eff :=
  let o := stepReq h w cx s.cfg s.next (s.bucket cx.port) r
  ({ s with buckets := s.put cx.port o.1, next := o.2.2 }, o.2.1)

/-- Does this reply carry an event that fails signature verification? -/
def unverified (h : Host) : Reply → Bool
  | .event ev _ => !h.verifyEvent ev
  | _ => false

def onReply (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  if unverified h rep then (s, []) else
  match s.buckets.find? (fun x => x.2.any (·.n == n)) with
  | none => (s, [])
  | some x =>
    let o := stepReply h w s.cfg s.next x.1 x.2 n rep
    ({ s with buckets := s.put x.1 o.1, next := o.2.2 }, o.2.1)

def onEvent (_h : Host) (_w : World) (s : St) (_e : HostEvent) : St × List Eff := (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with buckets := s.buckets.filter (·.1 != p) }, (s.bucket p).filterMap stopEff)

def mentions (s : St) (p : PortId) : Bool := s.buckets.any (·.1 == p)


/-! ### Codec round trip -/

theorem EventOpts.ofJson?_toJson (o : EventOpts) : EventOpts.ofJson? o.toJson = some o := by
  obtain ⟨a, r, t⟩ := o
  cases a <;> cases r <;> cases t <;> simp [EventOpts.ofJson?, EventOpts.toJson, Json.mkObj,
    optField, Json.get?, Json.lookup, Json.isObj] <;> rfl

theorem ReadOpts.ofJson?_toJson (o : ReadOpts) : ReadOpts.ofJson? o.toJson = some o := by
  obtain ⟨a, r, l, t⟩ := o
  cases a <;> cases r <;> cases l <;> cases t <;> simp [ReadOpts.ofJson?, ReadOpts.toJson,
    Json.mkObj, optField, Json.get?, Json.lookup, Json.isObj] <;> rfl

theorem PubOpts.ofJson?_toJson (o : PubOpts) : PubOpts.ofJson? o.toJson = some o := by
  obtain ⟨r, t, i⟩ := o
  cases r <;> cases t <;> cases i <;> simp [PubOpts.ofJson?, PubOpts.toJson, Json.mkObj,
    optField, Json.get?, Json.lookup, Json.isObj] <;> rfl

theorem Target.ofJson?_toJson (t : Target) : Target.ofJson? t.toJson = some t := by
  obtain ⟨a, p, d⟩ := t
  cases a <;> cases p <;> (try rcases d with _ | ⟨_ | _⟩) <;> simp [Target.ofJson?, Target.toJson,
    Json.mkObj, optField, Json.get?, Json.lookup, Json.isObj, Direction.ofJson?,
    Direction.toJson] <;> rfl

theorem decode_encodeReq (r : Req) (hr : r.WF) : decode (encodeReq r) = .ok r := by
  cases r with
  | getEvent id eid o =>
    cases o <;> simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?,
      Json.get?, Json.lookup, reqId?, optField, EventOpts.ofJson?_toJson]
  | query id fs o =>
    obtain ⟨hne, hall⟩ := hr
    cases o <;> simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?,
      Json.get?, Json.lookup, reqId?, optField, filtersOf?, hne, hall, ReadOpts.ofJson?_toJson]
  | subscribe id sid fs o =>
    obtain ⟨hne, hall⟩ := hr
    cases o <;> simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?,
      Json.get?, Json.lookup, reqId?, optField, filtersOf?, hne, hall, ReadOpts.ofJson?_toJson]
  | close id sid =>
    simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
      Json.lookup, reqId?]
  | publish id t o pk =>
    cases o <;> simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?,
      Json.get?, Json.lookup, reqId?, optField, templateOf?, PubOpts.ofJson?_toJson,
      Net.ofJson?_withPubkey, Net.claimedPubkey?_withPubkey]
  | resolveRelays id tg =>
    simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
      Json.lookup, reqId?, Target.ofJson?_toJson]


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
  · split at hm
    · exact hm
    · rename_i x hx
      rcases mentions_put hm with hm | rfl
      · exact hm
      · exact List.any_eq_true.mpr ⟨x, List.mem_of_find?_eq_some hx, by simp⟩

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q :=
  .inl hm

/-! ### Properties (lifted from `Napplet.NapOutbox`) -/

/-- Events that fail signature verification have no effect at all. -/
theorem onReply_unverified (h : Host) (w : World) (s : St) (n : Nat) (ev : NostrEvent)
    (r : String) (hv : h.verifyEvent ev = false) : onReply h w s n (.event ev r) = (s, []) := by
  simp [onReply, unverified, hv]

def isPublish : Eff → Bool
  | .call _ (.publish ..) => true
  | _ => false

theorem complete_no_publish {h : Host} {cfg : Cfg} {now : Nat} {port : PortId} {n : Nat}
    {g : Goal} {ls : Lists} : ∀ x ∈ (complete h cfg now port n g ls).2, isPublish x = false := by
  intro x hx
  unfold complete at hx
  repeat' (split at hx)
  all_goals (simp at hx <;> subst hx <;> rfl)

theorem lookups_no_publish (parent start : Nat) (as : List Pubkey) :
    ∀ x ∈ (lookups parent start as).2, isPublish x = false := by
  induction as generalizing start with
  | nil => simp [lookups]
  | cons a as ih =>
    intro x hx
    simp only [lookups, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact ih _ x hx

theorem startPlan_no_publish {h : Host} {cfg : Cfg} {now : Nat} {port : PortId} {nx : Nat}
    {b : Bucket} {g : Goal} {want : List Pubkey} :
    ∀ x ∈ (startPlan h cfg now port nx b g want).2.1, isPublish x = false := by
  intro x hx
  unfold startPlan at hx
  split at hx
  · exact complete_no_publish x hx
  · exact lookups_no_publish _ _ _ x hx

theorem stopSub_no_publish (b : Bucket) (sid : String) :
    ∀ x ∈ (stopSub b sid).2, isPublish x = false := by
  intro x hx
  simp only [stopSub, List.mem_filterMap] at hx
  obtain ⟨e, -, he⟩ := hx
  unfold stopEff at he
  split at he <;> simp at he <;> subst he <;> rfl

/-- Requests never publish: publishing happens only after the signer answered. -/
theorem handle_no_publish (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    ∀ x ∈ (handle h w cx s r).2, isPublish x = false := by
  intro x hx
  cases r <;> simp only [handle, stepReq] at hx <;> (repeat' split at hx) <;>
    first
    | (simp at hx; subst hx; rfl)
    | exact startPlan_no_publish x hx
    | (simp only [List.mem_append] at hx
       rcases hx with hx | hx
       · exact stopSub_no_publish _ _ x hx
       · first | exact startPlan_no_publish x hx | (simp at hx; subst hx; rfl))

theorem onLookup_no_publish {h : Host} {cfg : Cfg} {now : Nat} {port : PortId} {rest : Bucket}
    {parent : Nat} {a : Pubkey} {l : Option (List RelayEntry)} :
    ∀ x ∈ (onLookup h cfg now port rest parent a l).2, isPublish x = false := by
  intro x hx
  unfold onLookup at hx
  split at hx
  · split at hx
    · simp at hx
    · exact complete_no_publish x hx
  · simp at hx

theorem onLookup_count {h : Host} {cfg : Cfg} {now : Nat} {port : PortId} {rest : Bucket}
    {parent : Nat} {a : Pubkey} {l : Option (List RelayEntry)} :
    ((onLookup h cfg now port rest parent a l).2.filter isPublish).length = 0 := by
  rw [List.filter_eq_nil_iff.mpr (fun x hx => by simp [onLookup_no_publish x hx])]; rfl

theorem stepReply_publish_mem {h : Host} {w : World} {cfg : Cfg} {nx : Nat} {port : PortId}
    {b : Bucket} {n : Nat} {rep : Reply} {t : CallTag} {ev : NostrEvent}
    {rs : Option (List String)}
    (hm : Eff.call t (.publish ev rs) ∈ (stepReply h w cfg nx port b n rep).2.1) :
    rep = .signed (some ev) ∧ ∃ user ls o, rs = some (NapOutbox.plan (envOf cfg user ls) o) := by
  unfold stepReply at hm
  split at hm
  · simp at hm
  · split at hm <;> (repeat' split at hm) <;> simp at hm
    all_goals first
      | (have := onLookup_no_publish _ hm; simp [isPublish] at this)
      | (obtain ⟨-, rfl, rfl⟩ := hm; exact ⟨rfl, _, _, _, rfl⟩)
      | skip

theorem stepReply_publish_count {h : Host} {w : World} {cfg : Cfg} {nx : Nat} {port : PortId}
    {b : Bucket} {n : Nat} {rep : Reply} :
    ((stepReply h w cfg nx port b n rep).2.1.filter isPublish).length ≤ 1 := by
  unfold stepReply
  split
  · simp
  · split <;> (repeat' split) <;> simp [isPublish, List.filter, onLookup_count]

/-- At most one signed event is published per reply step, and it is the signer's output,
sent to exactly `NapOutbox.plan` of the resolved lists. -/
theorem onReply_publish {h : Host} {w : World} {s : St} {n : Nat} {rep : Reply} {t : CallTag}
    {ev : NostrEvent} {rs : Option (List String)}
    (hm : Eff.call t (.publish ev rs) ∈ (onReply h w s n rep).2) :
    rep = .signed (some ev) ∧ ∃ user ls o, rs = some (NapOutbox.plan (envOf s.cfg user ls) o) := by
  simp only [onReply] at hm
  split at hm
  · simp at hm
  · split at hm
    · simp at hm
    · exact stepReply_publish_mem hm

theorem onReply_single_publish (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) :
    ((onReply h w s n rep).2.filter isPublish).length ≤ 1 := by
  simp only [onReply]
  split
  · simp
  · split
    · simp
    · exact stepReply_publish_count

/-- Publish fanout is deduplicated and every relay passed relay policy, so napplet-supplied
`options.relays` cannot force a private or disallowed host (`NapOutbox.plan_allowed`,
`plan_nodup`); fallback relays never stand in for an inbox (`NapOutbox.fallback_not_for_inboxes`
applies to the same plan). -/
theorem onReply_publish_relays {h : Host} {w : World} {s : St} {n : Nat} {rep : Reply}
    {t : CallTag} {ev : NostrEvent} {rs : List String}
    (hm : Eff.call t (.publish ev (some rs)) ∈ (onReply h w s n rep).2) :
    rs.Nodup ∧ ∀ u ∈ rs, s.cfg.allowed u = true := by
  obtain ⟨-, user, ls, o, he⟩ := onReply_publish hm
  simp only [Option.some.injEq] at he
  subst he
  exact ⟨NapOutbox.plan_nodup _ _, fun u hu => NapOutbox.plan_allowed hu⟩

/-! #### Never sign napplet ciphertext -/

def NoBadSign (h : Host) (l : List Eff) : Prop :=
  ∀ t u, Eff.call t (.sign u) ∈ l → h.looksCiphertext u.content = false

theorem complete_sign {h : Host} {cfg : Cfg} {now : Nat} {port : PortId} {n : Nat} {g : Goal}
    {ls : Lists} : NoBadSign h (complete h cfg now port n g ls).2 := by
  intro t u hm
  unfold complete at hm
  repeat' (split at hm)
  all_goals (simp at hm)
  rename_i hc _
  obtain ⟨-, rfl⟩ := hm
  simpa [EventTemplate.stamp] using hc

theorem lookups_sign (parent start : Nat) (as : List Pubkey) (h : Host) :
    NoBadSign h (lookups parent start as).2 := by
  induction as generalizing start with
  | nil => simp [NoBadSign, lookups]
  | cons a as ih =>
    intro t u hm
    simp only [lookups, List.mem_cons] at hm
    rcases hm with hm | hm
    · cases hm
    · exact ih _ t u hm

theorem stopSub_sign (b : Bucket) (sid : String) (h : Host) : NoBadSign h (stopSub b sid).2 := by
  intro t u hm
  simp only [stopSub, List.mem_filterMap] at hm
  obtain ⟨e, -, he⟩ := hm
  unfold stopEff at he
  split at he <;> simp at he

theorem startPlan_sign {h : Host} {cfg : Cfg} {now : Nat} {port : PortId} {nx : Nat}
    {b : Bucket} {g : Goal} {want : List Pubkey} :
    NoBadSign h (startPlan h cfg now port nx b g want).2.1 := by
  intro t u hm
  unfold startPlan at hm
  split at hm
  · exact complete_sign t u hm
  · exact lookups_sign _ _ _ h t u hm

/-- No request ever leads to signing content that looks like napplet ciphertext
(NIP-5D §Security 7). -/
theorem handle_sign (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    NoBadSign h (handle h w cx s r).2 := by
  intro t u hm
  cases r <;> simp only [handle, stepReq] at hm <;> (repeat' split at hm) <;>
    first
    | (simp at hm; done)
    | exact startPlan_sign t u hm
    | (simp only [List.mem_append] at hm
       rcases hm with hm | hm
       · exact stopSub_sign _ _ h t u hm
       · first | exact startPlan_sign t u hm | (simp at hm; done))

theorem onLookup_sign {h : Host} {cfg : Cfg} {now : Nat} {port : PortId} {rest : Bucket}
    {parent : Nat} {a : Pubkey} {l : Option (List RelayEntry)} :
    NoBadSign h (onLookup h cfg now port rest parent a l).2 := by
  intro t u hm
  unfold onLookup at hm
  split at hm
  · split at hm
    · simp at hm
    · exact complete_sign t u hm
  · simp at hm

theorem onReply_sign (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) :
    NoBadSign h (onReply h w s n rep).2 := by
  intro t u hm
  simp only [onReply] at hm
  split at hm
  · simp at hm
  · split at hm
    · simp at hm
    · unfold stepReply at hm
      split at hm
      · simp at hm
      · split at hm <;> (repeat' split at hm) <;> first | exact onLookup_sign t u hm | simp at hm

/-! #### Reads -/

def Req.isRead : Req → Bool
  | .getEvent .. | .query .. | .subscribe .. | .resolveRelays .. => true
  | _ => false

/-- Without relay read access a read or relay-discovery request only gets its error reply:
no lookup, no subscription, no state. -/
theorem handle_read_denied (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req)
    (hr : r.isRead = true) (hd : s.cfg.canRead cx.identity = false) :
    ∀ x ∈ (handle h w cx s r).2, ∃ m, x = .send cx.port m := by
  intro x hx
  cases r <;> simp [Req.isRead] at hr <;> simp [handle, stepReq, hd] at hx <;> exact ⟨_, hx⟩

/-- The event carried in a result's `result.event`. -/
def evOf (m : Json) : Option NostrEvent :=
  ((m.get? "result").bind (·.get? "event")).bind NostrEvent.ofJson?

theorem pick_sound {h : Host} {eid : String} {acc : List (NostrEvent × List String)}
    {x : NostrEvent × List String} (hp : pick h eid acc = some x) :
    x.1.id = eid ∧ h.verifyEvent x.1 = true ∧ x ∈ acc := by
  have := List.find?_some hp
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1, this.2, List.mem_of_find?_eq_some hp⟩

/-- `outbox.getEvent.result` returns only the requested event, and only if its signature
verifies (`NapOutbox.getEvent_matches`). -/
theorem getEventMsg_sound {h : Host} {id eid : String} {acc : List (NostrEvent × List String)}
    {inc : Bool} {err : Option String} {e : NostrEvent}
    (he : evOf (getEventMsg h id eid acc inc err) = some e) :
    e.id = eid ∧ h.verifyEvent e = true := by
  unfold getEventMsg at he
  split at he
  · rename_i x hx
    have : evOf (Json.msg "outbox.getEvent.result"
      [("id", some (.str id)), ("result", some (resultJson x.1 x.2)), ("incomplete", incJson inc),
       ("error", err.map .str)]) = some x.1 := by
      unfold resultJson incJson
      split <;> split <;> cases err <;> simp [evOf, Json.msg, Json.mkObj, Json.get?, Json.lookup]
    rw [this] at he
    cases he
    exact ⟨(pick_sound hx).1, (pick_sound hx).2.1⟩
  · unfold incJson at he
    split at he <;> simp [evOf, Json.msg, Json.mkObj, Json.get?, Json.lookup] at he

theorem mem_dedupById {x : NostrEvent × List String} {l : List (NostrEvent × List String)}
    (h : x ∈ dedupById l) : x ∈ l := by
  induction l with
  | nil => simp [dedupById] at h
  | cons y ys ih =>
    simp only [dedupById] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

theorem dedupById_nodup (l : List (NostrEvent × List String)) :
    ((dedupById l).map (·.1.id)).Nodup := by
  induction l with
  | nil => simp [dedupById]
  | cons x xs ih =>
    simp only [dedupById]
    split
    · exact ih
    · rename_i hx
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at hx
      simp only [List.mem_map, not_exists, not_and]
      intro e he heq
      exact hx e he heq

/-- `outbox.query.result` events are deduplicated by id (`NapOutbox.query_nodup`). -/
theorem queryEvents_nodup (h : Host) (lim : Option Nat) (acc : List (NostrEvent × List String)) :
    ((queryEvents h lim acc).map (·.1.id)).Nodup := by
  unfold queryEvents
  split
  · rw [List.map_take]; exact (dedupById_nodup _).sublist (List.take_sublist _ _)
  · exact dedupById_nodup _

/-- `outbox.query.result` events are collected events whose signatures verify
(`NapOutbox.query_sound`). -/
theorem queryEvents_sound {h : Host} {lim : Option Nat} {acc : List (NostrEvent × List String)}
    {x : NostrEvent × List String} (hx : x ∈ queryEvents h lim acc) :
    x ∈ acc ∧ h.verifyEvent x.1 = true := by
  unfold queryEvents at hx
  have : x ∈ dedupById (acc.filter fun x => h.verifyEvent x.1) := by
    split at hx
    · exact List.mem_of_mem_take hx
    · exact hx
  simpa using mem_dedupById this

/-- Subscription deliveries (and every collected read result) come only from verified
events: an unverified event produces no output. -/
theorem onReply_unverified_silent (h : Host) (w : World) (s : St) (n : Nat) (ev : NostrEvent)
    (r : String) (hv : h.verifyEvent ev = false) : (onReply h w s n (.event ev r)).2 = [] := by
  rw [onReply_unverified h w s n ev r hv]


/-! ### Vectors (upstream examples, NAP-OUTBOX @ 8865f73d) -/

section Vectors

def vHost : Host where
  crypto := { sha256 := fun _ => "", verifySig := fun _ => true }
  verifyEvent := fun e => e.sig != "bad"
  sniff := fun _ => "application/octet-stream"
  rasterize := fun _ => none
  looksCiphertext := fun c => (c.splitOn "?iv=").length > 1
  encryptedWith := fun _ => none
  transform := id

def vCtx : Ctx :=
  { port := 7, window := 1, identity := { dTag := some "feed", artifactHash := "h" },
    exposed := [.outbox], inst := 0 }

def vWorld : World := { now := 1700000000, live := [vCtx], user := "user..." }

def sends (effs : List Eff) : List Json := effs.filterMap fun | .send _ m => some m | _ => none

def run (s : St) (j : Json) (replies : List (Nat × Reply)) : St × List Eff :=
  match decode j with
  | .ok r =>
    let (s1, e1) := handle vHost vWorld vCtx s r
    replies.foldl (fun (acc : St × List Eff) (nr : Nat × Reply) =>
      let (s2, e2) := onReply vHost vWorld acc.1 nr.1 nr.2
      (s2, acc.2 ++ e2)) (s1, e1)
  | _ => (s, [])

def oneSend (effs : List Eff) (expected : String) : Bool :=
  match sends effs with
  | [m] => Json.same m (Json.parse! expected)
  | _ => false

def evJ (text : String) : NostrEvent := (NostrEvent.ofJson? (Json.parse! text)).getD default

def relayEx : String := "wss://relay.example.com"
def both (u : String) : List RelayEntry := [⟨u, true, true⟩]

def ev1 : NostrEvent :=
  evJ "{ \"id\": \"ev1...\", \"pubkey\": \"ab12...\", \"kind\": 1, \"content\": \"hello\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }"

-- getEvent with an author hint: NIP-65 lookup, subscription on the author's write relays,
-- EOSE, result with relay hint.
def getReq : String :=
  "{ \"type\": \"outbox.getEvent\", \"id\": \"e1\", \"eventId\": \"ev1...\", \"options\": { \"author\": \"ab12...\", \"timeoutMs\": 3000 } }"
#guard decode (Json.parse! getReq) matches .ok (.getEvent "e1" "ev1..." (some ⟨some "ab12...", none, some 3000⟩))
#guard (run (St.init) (Json.parse! getReq) []).2 == [.call (tag 1) (.relayList "ab12...")]
#guard (run (St.init) (Json.parse! getReq) [(1, .relayList (some (both relayEx)))]).2.getLast? ==
  some (.call (tag 0) (.subscribe [Json.parse! "{\"ids\": [\"ev1...\"], \"authors\": [\"ab12...\"]}"] (some [relayEx])))
#guard oneSend (run (St.init) (Json.parse! getReq)
    [(1, .relayList (some (both relayEx))), (0, .event ev1 relayEx), (0, .eose)]).2
  "{ \"type\": \"outbox.getEvent.result\", \"id\": \"e1\", \"result\": { \"event\": { \"id\": \"ev1...\", \"pubkey\": \"ab12...\", \"kind\": 1, \"content\": \"hello\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }, \"sidecar\": { \"relayHints\": [\"wss://relay.example.com\"] } } }"
-- An event with a bad signature is ignored; the lookup then reports "not found".
#guard oneSend (run (St.init) (Json.parse! getReq)
    [(1, .relayList (some (both relayEx))), (0, .event { ev1 with sig := "bad" } relayEx), (0, .eose)]).2
  "{ \"type\": \"outbox.getEvent.result\", \"id\": \"e1\", \"error\": \"not found\" }"

-- query, deduplicated by id with merged relay hints.
def qReq : String :=
  "{ \"type\": \"outbox.query\", \"id\": \"q1\", \"filters\": [{ \"authors\": [\"ab12...\"], \"kinds\": [1], \"limit\": 20 }], \"options\": { \"timeoutMs\": 3000 } }"
#guard oneSend (run (St.init) (Json.parse! qReq)
    [(1, .relayList (some (both relayEx))), (0, .event ev1 relayEx), (0, .event ev1 relayEx), (0, .eose)]).2
  "{ \"type\": \"outbox.query.result\", \"id\": \"q1\", \"events\": [ { \"event\": { \"id\": \"ev1...\", \"pubkey\": \"ab12...\", \"kind\": 1, \"content\": \"hello\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }, \"sidecar\": { \"relayHints\": [\"wss://relay.example.com\"] } } ] }"
-- Missing relay list: fallback-free plan uses the pool and the answer is incomplete.
#guard oneSend (run (St.init) (Json.parse! qReq) [(1, .relayList none), (0, .eose)]).2
  "{ \"type\": \"outbox.query.result\", \"id\": \"q1\", \"events\": [], \"incomplete\": true }"

-- Live subscription: one `outbox.event` per id; EOSE is not forwarded.
def sReq : String :=
  "{ \"type\": \"outbox.subscribe\", \"id\": \"s1\", \"subId\": \"sub-1\", \"filters\": [{ \"authors\": [\"ab12...\"], \"kinds\": [1], \"limit\": 50 }], \"options\": { \"timeoutMs\": 3000 } }"
#guard oneSend (run (St.init) (Json.parse! sReq)
    [(1, .relayList (some (both relayEx))), (0, .event ev1 relayEx), (0, .eose), (0, .event ev1 "wss://other")]).2
  "{ \"type\": \"outbox.event\", \"subId\": \"sub-1\", \"result\": { \"event\": { \"id\": \"ev1...\", \"pubkey\": \"ab12...\", \"kind\": 1, \"content\": \"hello\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }, \"sidecar\": { \"relayHints\": [\"wss://relay.example.com\"] } } }"
-- Close stops it and confirms with `outbox.closed`.
#guard
  let s1 := (run (St.init) (Json.parse! sReq) [(1, .relayList (some (both relayEx)))]).1
  let (s2, effs) := run s1 (Json.parse! "{ \"type\": \"outbox.close\", \"id\": \"c1\", \"subId\": \"sub-1\" }") []
  effs.head? == some (.effect (.unsubscribe (tag 0))) &&
  oneSend effs "{ \"type\": \"outbox.closed\", \"subId\": \"sub-1\" }" && !mentions s2 7

-- Publish to the user's outbox and the referenced inbox: lookups, one signature, one publish.
def p1Req : String :=
  "{ \"type\": \"outbox.publish\", \"id\": \"p1\", \"event\": { \"kind\": 1111, \"content\": \"reply from a napplet\", \"tags\": [[\"p\", \"ab12...\"]], \"created_at\": 1234567890 }, \"options\": { \"toInboxes\": [\"ab12...\"] } }"
def ev2 : NostrEvent :=
  evJ "{ \"id\": \"ev2...\", \"pubkey\": \"user...\", \"kind\": 1111, \"content\": \"reply from a napplet\", \"tags\": [[\"p\", \"ab12...\"]], \"created_at\": 1234567890, \"sig\": \"...\" }"
#guard (run (St.init) (Json.parse! p1Req) []).2 ==
  [.call (tag 1) (.relayList "user..."), .call (tag 2) (.relayList "ab12...")]
#guard (run (St.init) (Json.parse! p1Req)
    [(1, .relayList (some [⟨relayEx, false, true⟩])), (2, .relayList (some [⟨relayEx, true, false⟩]))]).2.getLast? ==
  some (.call (tag 0) (.sign { pubkey := "user...", createdAt := 1234567890, kind := 1111, tags := [["p", "ab12..."]], content := "reply from a napplet" }))
#guard (run (St.init) (Json.parse! p1Req)
    [(1, .relayList (some [⟨relayEx, false, true⟩])), (2, .relayList (some [⟨relayEx, true, false⟩])),
     (0, .signed (some ev2))]).2.getLast? ==
  some (.call (tag 3) (.publish ev2 (some [relayEx])))
#guard oneSend (run (St.init) (Json.parse! p1Req)
    [(1, .relayList (some [⟨relayEx, false, true⟩])), (2, .relayList (some [⟨relayEx, true, false⟩])),
     (0, .signed (some ev2)), (3, .published [(relayEx, true)])]).2
  "{ \"type\": \"outbox.publish.result\", \"id\": \"p1\", \"ok\": true, \"event\": { \"id\": \"ev2...\", \"pubkey\": \"user...\", \"kind\": 1111, \"content\": \"reply from a napplet\", \"tags\": [[\"p\", \"ab12...\"]], \"created_at\": 1234567890, \"sig\": \"...\" }, \"eventId\": \"ev2...\", \"relays\": { \"wss://relay.example.com\": true } }"

-- Publish to explicit relays without the user's outbox: no lookups, sign at once.
def p2Req : String :=
  "{ \"type\": \"outbox.publish\", \"id\": \"p2\", \"event\": { \"kind\": 1059, \"content\": \"...\", \"tags\": [[\"p\", \"ab12...\"]], \"created_at\": 1234567890 }, \"options\": { \"toOutbox\": false, \"relays\": [\"wss://dm.example.com\"] } }"
def ev3 : NostrEvent :=
  evJ "{ \"id\": \"ev3...\", \"pubkey\": \"user...\", \"kind\": 1059, \"content\": \"...\", \"tags\": [[\"p\", \"ab12...\"]], \"created_at\": 1234567890, \"sig\": \"...\" }"
#guard (run (St.init) (Json.parse! p2Req) []).2 ==
  [.call (tag 0) (.sign { pubkey := "user...", createdAt := 1234567890, kind := 1059, tags := [["p", "ab12..."]], content := "..." })]
#guard oneSend (run (St.init) (Json.parse! p2Req)
    [(0, .signed (some ev3)), (1, .published [("wss://dm.example.com", true)])]).2
  "{ \"type\": \"outbox.publish.result\", \"id\": \"p2\", \"ok\": true, \"event\": { \"id\": \"ev3...\", \"pubkey\": \"user...\", \"kind\": 1059, \"content\": \"...\", \"tags\": [[\"p\", \"ab12...\"]], \"created_at\": 1234567890, \"sig\": \"...\" }, \"eventId\": \"ev3...\", \"relays\": { \"wss://dm.example.com\": true } }"
-- A disallowed explicit relay is dropped by policy; nothing left to publish to.
#guard oneSend (run (St.init) (Json.parse! "{ \"type\": \"outbox.publish\", \"id\": \"p3\", \"event\": { \"kind\": 1 }, \"options\": { \"toOutbox\": false, \"relays\": [\"ws://192.168.0.1\"] } }") []).2
  "{ \"type\": \"outbox.publish.result\", \"id\": \"p3\", \"ok\": false, \"error\": \"relay list unavailable\" }"
-- An unresolvable inbox is reported; resolved relays are still used (decision 14).
#guard oneSend (run (St.init) (Json.parse! p1Req)
    [(1, .relayList (some [⟨relayEx, false, true⟩])), (2, .relayList none),
     (0, .signed (some ev2)), (3, .published [(relayEx, true)])]).2
  "{ \"type\": \"outbox.publish.result\", \"id\": \"p1\", \"ok\": true, \"event\": { \"id\": \"ev2...\", \"pubkey\": \"user...\", \"kind\": 1111, \"content\": \"reply from a napplet\", \"tags\": [[\"p\", \"ab12...\"]], \"created_at\": 1234567890, \"sig\": \"...\" }, \"eventId\": \"ev2...\", \"relays\": { \"wss://relay.example.com\": true }, \"error\": \"relay list unavailable\" }"

-- resolveRelays (read: the author's write relays).
def rReq : String :=
  "{ \"type\": \"outbox.resolveRelays\", \"id\": \"r1\", \"target\": { \"pubkey\": \"ab12...\", \"direction\": \"read\" } }"
#guard oneSend (run (St.init) (Json.parse! rReq) [(1, .relayList (some [⟨relayEx, false, true⟩]))]).2
  "{ \"type\": \"outbox.resolveRelays.result\", \"id\": \"r1\", \"plan\": { \"relays\": [\"wss://relay.example.com\"], \"source\": \"nip65\" } }"
#guard oneSend (run (St.init { fallback := ["wss://fallback.example"] }) (Json.parse! rReq) [(1, .relayList none)]).2
  "{ \"type\": \"outbox.resolveRelays.result\", \"id\": \"r1\", \"plan\": { \"relays\": [\"wss://fallback.example\"], \"source\": \"fallback\", \"missingAuthors\": [\"ab12...\"] } }"

-- Malformed and unknown requests.
#guard decode (Json.parse! "{ \"type\": \"outbox.eose\", \"subId\": \"x\" }") matches .unknown
#guard match decode (Json.parse! "{ \"type\": \"outbox.query\", \"id\": \"q\", \"filters\": [] }") with
  | .reject [m] => Json.same m (Json.parse! "{ \"type\": \"outbox.query.result\", \"id\": \"q\", \"events\": [], \"error\": \"invalid filter\" }")
  | _ => false
#guard decode (Json.parse! "{ \"type\": \"outbox.query\", \"id\": \"q\", \"filters\": { \"kinds\": [1] } }") matches .ok (.query "q" [_] none)
#guard match decode (Json.parse! "{ \"type\": \"outbox.resolveRelays\", \"id\": \"r\", \"target\": 5 }") with
  | .reject [m] => Json.same m (Json.parse! "{ \"type\": \"outbox.resolveRelays.result\", \"id\": \"r\", \"plan\": { \"relays\": [], \"source\": \"policy\" }, \"error\": \"invalid request\" }")
  | _ => false

-- Teardown: cancel the outstanding lookups, stop subscriptions.
#guard (drop (run (St.init) (Json.parse! p1Req) []).1 7).2 ==
  [.effect (.cancel (tag 1)), .effect (.cancel (tag 2))]


-- A template claiming a pubkey other than the user's is refused, not re-stamped (NAP-POW).
#guard oneSend (run (St.init) (Json.parse! "{ \"type\": \"outbox.publish\", \"id\": \"p4\", \"event\": { \"kind\": 1, \"pubkey\": \"other...\" } }") []).2
  "{ \"type\": \"outbox.publish.result\", \"id\": \"p4\", \"ok\": false, \"error\": \"publish denied\" }"
-- The user's own pubkey is accepted: lookups start as for any publish.
#guard (run (St.init) (Json.parse! "{ \"type\": \"outbox.publish\", \"id\": \"p5\", \"event\": { \"kind\": 1, \"pubkey\": \"user...\" } }") []).2 ==
  [.call (tag 1) (.relayList "user...")]

-- Private, loopback and localhost relays are refused by the default policy (NAP-OUTBOX):
-- as napplet hints ...
#guard ["wss://127.0.0.1", "wss://localhost", "wss://[::1]", "wss://10.0.0.1:443", "wss://router"].all fun u =>
  oneSend (run (St.init) (Json.parse! ("{ \"type\": \"outbox.publish\", \"id\": \"p3\", \"event\": { \"kind\": 1 }, \"options\": { \"toOutbox\": false, \"relays\": [\"" ++ u ++ "\"] } }")) []).2
    "{ \"type\": \"outbox.publish.result\", \"id\": \"p3\", \"ok\": false, \"error\": \"relay list unavailable\" }"
-- ... and in an author's NIP-65 list.
#guard oneSend (run (St.init) (Json.parse! "{ \"type\": \"outbox.resolveRelays\", \"id\": \"r\", \"target\": { \"authors\": [\"ab12...\"] } }")
    [(1, .relayList (some (both "wss://192.168.1.1" ++ both "wss://localhost" ++ both relayEx)))]).2
  "{ \"type\": \"outbox.resolveRelays.result\", \"id\": \"r\", \"plan\": { \"relays\": [\"wss://relay.example.com\"], \"source\": \"nip65\" } }"

-- Reusing a live `subId` replaces the subscription silently: no `outbox.closed`.
#guard
  let s1 := (run (St.init) (Json.parse! sReq) [(1, .relayList (some (both relayEx)))]).1
  (run s1 (Json.parse! sReq) []).2 ==
    [.effect (.unsubscribe (tag 0)), .call (tag 3) (.relayList "ab12...")]

end Vectors

end Napplet.Run.Outbox
