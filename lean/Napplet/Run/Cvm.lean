/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Cvm

/-!
# NAP-CVM runtime component

Upstream: `napplet/naps` PR #31, `naps/NAP-CVM.md` at `28cf1bdb`.

Wire (napplet → shell): `cvm.discover {id, query?}`, `cvm.request {id, server,
message, options?}`, `cvm.close {id, server}`, `cvm.registry.list {id, query?}`,
`cvm.registry.has {id, selector, options?}`, `cvm.registry.describe {id, selector,
options?}`, `cvm.registry.call {id, selector, tool, args?, options?}`.
Wire (shell → napplet): `<type>.result {id, <payload>?, error?}` for each, and the
push `cvm.event {server, message}` (no `id`). There are no `cvm.*.error` messages.

Every recognised request gets exactly one result:

* Validation and policy failures answer at once (`invalid message`,
  `invalid request`, `invalid timeout`, `timeout out of policy`, `policy denied`,
  `unsupported kind`, `unsupported method`, `cache policy denied`, `schema mismatch`).
* Work that needs the network is a host call. Together with it the shell starts a
  deadline (`Call.nap .cvm "timer" {ms}`, the accepted `timeoutMs`, default 30000
  ms, checked by `NapCvm.checkTimeout`). Whichever completes first answers; the
  other is cancelled (`Effect.cancel`), and a reply for a released tag is
  ignored, so a late response is never a second result nor a `cvm.event`.
  The deadline covers consent and payment, which are further calls of the same
  operation.
* `close(server)` finishes this endpoint's pending operations on that server (its
  client requests and `registry.call` work pinned to it with `options.server`) with
  `"session closed"` before acknowledging, then tells the host to release the
  session (`Effect.nap .cvm "close"`). Endpoint teardown does the same without
  results.

MCP messages (`cvm.request`) are validated in the shell (MCP basic forms:
request, notification, response; JSON-RPC 2.0; ids are strings or integers).
Client requests get a transport id (the operation key) through `NapCvm.Corr`,
which also rejects an id already outstanding in the same session; the session also
remembers every id used for a client request (`Session.used`), so reuse after
completion is rejected too (`"invalid message"`) until `close(server)` or teardown
ends the session. The caller's id is restored in the response. `notifications/cancelled` must name one of this
endpoint's outstanding requests in that session and is mapped to its transport id.
A response must answer a server request delivered to this endpoint in that session.

Sessions are per endpoint and server. Events from the host are delivered only to
the endpoint whose client key received them (`client` = `Ctx.endpointId`) and only
while it has a session with that server.

Payment gates (CEP-8 `-32042` / `notifications/payment_required`) are reported by
the host as a reply `{payment: offer}`; the shell applies `NapCvm.decidePay` with
the request's `payment` option, a prompt (`Call.prompt .cvm "payment"`) for
`prompt`, and the standing allowances in `Cfg` for `allow` (reserved atomically
when the gate is met). Only then does it tell the host to settle
(`Call.nap .cvm "pay"`). A shell configured without payment support answers
`"payment required"`.

The registry is optional (`Cfg.registry`). Requests are validated first (selector,
`limit`, hash, `cache`, `timeoutMs`), so a malformed one answers its validation
error whether or not the registry exists. Without it, a well-formed
`registry.list`, `registry.describe` or `registry.call` answers
`"unsupported method"` and `registry.has` answers `has: false` (`NapCvm.respond`). With it, `registry.call`
first asks the host for the verified entry and publishes only when the tool's
verified CEP-15 hash matches (`NapCvm.registryCall`).
-/

/-! ## Host operations

`client` is always the requesting endpoint's `Ctx.endpointId`. The host keeps one
ContextVM client signing key per `client` (fresh, ephemeral, never the user's key),
and all session state (initialisation, server-request correlation, CEP-8 payment
mode and paid authorisations) per `client` and server.

| Operation | Args (JSON) | Reply | Contract |
|---|---|---|---|
| `Call.nap .cvm "timer" {ms}` | `ms`: uint | `json {}` | Reply once, `ms` milliseconds after the call. |
| `Call.nap .cvm "discover" {query?}` | `query` = `CvmDiscoverQuery` (`kinds` already checked against `Cfg.kinds`) | `json {servers: [CvmServer]}` or `json {error}` | NAP-CVM §Discovery over CEP-6 announcements (kinds 11316–11320) and CEP-17 relay lists; honour `kinds` and `limit`; `capabilities` are MCP capability names only; `paymentRequired` per CEP-8 pricing (omit when unknown). The shell truncates to `limit` again. |
| `Call.nap .cvm "request" a` | `a` = `{client, server: CvmServerRef, message, initialize?, payment}`; `message` is the validated MCP message, a client request's `id` replaced by the transport id (an integer) | `json {message}` (the MCP response, request form only), `json {published: true}` (notification and response forms, after publication), `json {payment: offer}`, or `json {error}` | ContextVM transport (kind 25910, CEP-4 encryption when supported), signed with the client key; verify the response comes from `server` by pubkey; initialise the MCP session when needed or asked (`initialize`); negotiate CEP-8/CEP-35 `payment_interaction` per session (`payment` is the requested mode name). A CEP-8 payment gate (`-32042` or `notifications/payment_required`) for this request is not answered by the host: it replies `{payment: offer}` where `offer` has `amount` (uint, the offer's unit) and `method` (payment method id), and keeps the request open. `error` strings are NAP-CVM's (`server not found`, `initialization failed`, `payment required`, `provider unavailable`, ...). An invocation that would consume a paid authorisation (an existing CEP-8 session authorisation or a host-held pre-paid allowance) is not executed directly: the host first replies `{payment: offer}` for it so the shell applies the request's `payment` mode, and executes only after the shell's `pay`; with `payment` = `deny` it is never sent. MCP `initialize` advertises only client capabilities the shell services (no `sampling`, `roots` or `elicitation` unless the shell implements them). |
| `Call.nap .cvm "pay" a` | `a` = `{client, server, offer}` | as `request` | Settle exactly this offer once (CEP-8; NWC or another backend), then (transparent mode) await the original response or (explicit gating) retry the same method and params with a fresh internal id, restoring the transport id; reply as `request`. Never settle twice; never replay after an uncertain execution. |
| `Call.prompt .cvm "payment" d` | `d` = `{server, method, amount, paymentMethod, offer}` | `decision` | NAP-CVM: consent for this invocation showing server, operation, amount and payment method. |
| `Call.nap .cvm "registry.list" {query?}` | `CvmRegistryQuery` | `json {entries}` or `json {error}` | NAP-CVM §Registry; CEP-15 hashes computed and verified by the host. |
| `Call.nap .cvm "registry.has" {selector, server?}` | | `json {has: bool}` | Permitted, verified, recently reachable provider satisfies the selector and pin. |
| `Call.nap .cvm "registry.describe" {selector, server?}` | | `json {entry}` or `json {error}` | `entry` = `CvmRegistryEntry` with verified `tools[].schemaHash`; no match: `schema mismatch` (hash) / `family not found` (label). |
| `Call.nap .cvm "registry.call" a` | `a` = `{client, selector, tool, args?, server?, initialize?, payment, cache?}` | `json {result}`, `json {payment: offer}` or `json {error}` | MCP `tools/call` of `tool` on a provider of the verified hash (the pinned `server` only, if given); no substitution after dispatch; remote JSON-RPC errors become `error`; result cache keyed per NAP-CVM. |
| `Effect.nap .cvm "close" {client, server}` | | — | Release this client's session with `server` (subscriptions, initialisation, correlations, authorisations); keep shared transport only if another client uses it. No remote cancellation or refund is promised. |
| `HostEvent.nap .cvm "event" {client, server, message}` | | — | An MCP notification or server request from `server` (pubkey verified) for `client`, or a notification correlated to one of its requests. Payment control messages are not reported. |
| `Effect.cancel ⟨.cvm, n⟩` | | — | Core contract (deadline reached, close, teardown). |
-/

namespace Napplet.Run.Cvm

open NapCvm

/-! ### Wire types -/

structure ServerRef where
  pubkey : String
  relays : Option (List String) := none
  deriving DecidableEq, Repr

structure DiscoverQuery where
  search : Option String := none
  kinds : Option (List Nat) := none
  relays : Option (List String) := none
  limit : Option Nat := none
  deriving DecidableEq, Repr

structure ReqOpts where
  timeoutMs : Option Nat := none
  initMcp : Option Bool := none
  payment : Option PayMode := none
  deriving DecidableEq, Repr

structure RegQuery where
  search : Option String := none
  family : Option String := none
  schemaHash : Option String := none
  category : Option String := none
  limit : Option Nat := none
  deriving DecidableEq, Repr

structure Selector where
  schemaHash : Option String := none
  family : Option String := none
  deriving DecidableEq, Repr

structure CallOpts where
  server : Option ServerRef := none
  timeoutMs : Option Nat := none
  initMcp : Option Bool := none
  payment : Option PayMode := none
  cache : Option String := none
  deriving DecidableEq, Repr

inductive Req where
  | discover (id : String) (q : Option DiscoverQuery)
  | request (id : String) (server : ServerRef) (message : Option Json) (o : ReqOpts)
  | close (id : String) (server : ServerRef)
  | registryList (id : String) (q : Option RegQuery)
  | registryHas (id : String) (sel : Selector) (server : Option ServerRef)
  | registryDescribe (id : String) (sel : Selector) (server : Option ServerRef)
  | registryCall (id : String) (sel : Selector) (tool : String) (args : Option (List (String × Json)))
      (o : CallOpts)
  deriving DecidableEq, Repr

/-! ### Codec -/

def optF {α : Type} (j : Json) (k : String) (f : Json → Option α) : Option (Option α) :=
  match j.get? k with
  | none => some none
  | some v => (f v).map some

def asObj? : Json → Option (List (String × Json))
  | .obj kvs => some kvs
  | _ => none

def asNats? (j : Json) : Option (List Nat) := (j.asArr?).bind (·.mapM Json.asNat?)

theorem asNats?_nats (xs : List Nat) : asNats? (.arr (xs.map Json.nat)) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [asNats?, Json.asArr?, Option.bind_some, List.map_cons, List.mapM_cons] at ih ⊢
    simp [ih]

def _root_.Napplet.NapCvm.PayMode.name : PayMode → String
  | .deny => "deny" | .prompt => "prompt" | .allow => "allow"

def payOf? : Json → Option PayMode
  | .str "deny" => some .deny
  | .str "prompt" => some .prompt
  | .str "allow" => some .allow
  | _ => none

theorem payOf?_name (m : PayMode) : payOf? (.str m.name) = some m := by cases m <;> rfl

def serverJson (r : ServerRef) : Json :=
  Json.mkObj [("pubkey", some (.str r.pubkey)), ("relays", r.relays.map Json.strs)]

def serverOf? (j : Json) : Option ServerRef := do
  some ⟨← j.getStr? "pubkey", ← optF j "relays" Json.asStrs?⟩

def discoverJson (q : DiscoverQuery) : Json :=
  Json.mkObj [("search", q.search.map .str), ("kinds", q.kinds.map fun ks => .arr (ks.map Json.nat)),
    ("relays", q.relays.map Json.strs), ("limit", q.limit.map Json.nat)]

def discoverOf? (j : Json) : Option DiscoverQuery := do
  guard j.isObj
  some ⟨← optF j "search" Json.asStr?, ← optF j "kinds" asNats?, ← optF j "relays" Json.asStrs?,
    ← optF j "limit" Json.asNat?⟩

def regQueryJson (q : RegQuery) : Json :=
  Json.mkObj [("search", q.search.map .str), ("family", q.family.map .str),
    ("schemaHash", q.schemaHash.map .str), ("category", q.category.map .str), ("limit", q.limit.map Json.nat)]

def regQueryOf? (j : Json) : Option RegQuery := do
  guard j.isObj
  some ⟨← optF j "search" Json.asStr?, ← optF j "family" Json.asStr?, ← optF j "schemaHash" Json.asStr?,
    ← optF j "category" Json.asStr?, ← optF j "limit" Json.asNat?⟩

def selectorJson (s : Selector) : Json :=
  Json.mkObj [("schemaHash", s.schemaHash.map .str), ("family", s.family.map .str)]

def selectorOf? (j : Json) : Option Selector := do
  guard j.isObj
  some ⟨← optF j "schemaHash" Json.asStr?, ← optF j "family" Json.asStr?⟩

def reqOptsJson (o : ReqOpts) : Option Json :=
  if o = {} then none
  else some (Json.mkObj [("timeoutMs", o.timeoutMs.map Json.nat), ("initialize", o.initMcp.map .bool),
    ("payment", o.payment.map (.str ·.name))])

def regOptsJson (s : Option ServerRef) : Option Json := s.map fun r => .obj [("server", serverJson r)]

def callOptsJson (o : CallOpts) : Option Json :=
  if o = {} then none
  else some (Json.mkObj [("server", o.server.map serverJson), ("timeoutMs", o.timeoutMs.map Json.nat),
    ("initialize", o.initMcp.map .bool), ("payment", o.payment.map (.str ·.name)),
    ("cache", o.cache.map .str)])

/-- Options: a non-integer or negative `timeoutMs` is `"invalid timeout"`; anything
else malformed is `"invalid request"`. -/
def reqOptsOf? (j : Json) : Except String ReqOpts :=
  match j.get? "options" with
  | none => .ok {}
  | some o =>
    if !o.isObj then .error "invalid request" else
    match optF o "timeoutMs" Json.asNat? with
    | none => .error "invalid timeout"
    | some t =>
      match optF o "initialize" Json.asBool?, optF o "payment" payOf? with
      | some i, some p => .ok ⟨t, i, p⟩
      | _, _ => .error "invalid request"

def regOptsOf? (j : Json) : Option (Option ServerRef) :=
  match j.get? "options" with
  | none => some none
  | some o => do
    guard o.isObj
    optF o "server" serverOf?

def callOptsOf? (j : Json) : Except String CallOpts :=
  match j.get? "options" with
  | none => .ok {}
  | some o =>
    if !o.isObj then .error "invalid request" else
    match optF o "timeoutMs" Json.asNat? with
    | none => .error "invalid timeout"
    | some t =>
      match optF o "server" serverOf?, optF o "initialize" Json.asBool?, optF o "payment" payOf?,
          optF o "cache" Json.asStr? with
      | some s, some i, some p, some c => .ok ⟨s, t, i, p, c⟩
      | _, _, _, _ => .error "invalid request"

def decodeWith (j : Json) (t : String) (f : String → Except String Req) : Decoded Req :=
  match reqId? j with
  | none => .reject []
  | some id =>
    match f id with
    | .ok r => .ok r
    | .error e => .reject (errorReply (resultType t) j e)

def need {α : Type} (o : Option α) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error "invalid request"

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | none => .unknown
  | some t =>
    if t = "cvm.discover" then decodeWith j t fun id => do
      .discover id <$> need (optF j "query" discoverOf?)
    else if t = "cvm.request" then decodeWith j t fun id => do
      let s ← need ((j.get? "server").bind serverOf?)
      let o ← reqOptsOf? j
      .ok (.request id s (j.get? "message") o)
    else if t = "cvm.close" then decodeWith j t fun id => do
      .close id <$> need ((j.get? "server").bind serverOf?)
    else if t = "cvm.registry.list" then decodeWith j t fun id => do
      .registryList id <$> need (optF j "query" regQueryOf?)
    else if t = "cvm.registry.has" then decodeWith j t fun id => do
      let sel ← need ((j.get? "selector").bind selectorOf?)
      .registryHas id sel <$> need (regOptsOf? j)
    else if t = "cvm.registry.describe" then decodeWith j t fun id => do
      let sel ← need ((j.get? "selector").bind selectorOf?)
      .registryDescribe id sel <$> need (regOptsOf? j)
    else if t = "cvm.registry.call" then decodeWith j t fun id => do
      let sel ← need ((j.get? "selector").bind selectorOf?)
      let tool ← need (j.getStr? "tool")
      let args ← need (optF j "args" asObj?)
      .registryCall id sel tool args <$> callOptsOf? j
    else .unknown

def encodeReq : Req → Json
  | .discover id q => Json.msg "cvm.discover" [("id", some (.str id)), ("query", q.map discoverJson)]
  | .request id s m o => Json.msg "cvm.request"
      [("id", some (.str id)), ("server", some (serverJson s)), ("message", m), ("options", reqOptsJson o)]
  | .close id s => Json.msg "cvm.close" [("id", some (.str id)), ("server", some (serverJson s))]
  | .registryList id q => Json.msg "cvm.registry.list" [("id", some (.str id)), ("query", q.map regQueryJson)]
  | .registryHas id sel s => Json.msg "cvm.registry.has"
      [("id", some (.str id)), ("selector", some (selectorJson sel)), ("options", regOptsJson s)]
  | .registryDescribe id sel s => Json.msg "cvm.registry.describe"
      [("id", some (.str id)), ("selector", some (selectorJson sel)), ("options", regOptsJson s)]
  | .registryCall id sel tool args o => Json.msg "cvm.registry.call"
      [("id", some (.str id)), ("selector", some (selectorJson sel)), ("tool", some (.str tool)),
       ("args", args.map .obj), ("options", callOptsJson o)]

/-! ### State -/

/-- A standing payment allowance configured outside the napplet, for one napplet
(catalog id), server, MCP method and payment method. -/
structure Allowance where
  napplet : String
  server : String
  method : String
  payMethod : String
  remaining : Nat
  deriving DecidableEq, Repr

structure Cfg where
  /-- Shell policy maximum for `timeoutMs` (NAP-CVM: at most 300000). -/
  maxTimeout : Nat := maxTimeout
  /-- Supported announcement kinds (CEP-6). -/
  kinds : List Nat := [11316, 11317, 11318, 11319, 11320]
  /-- ACL: may this napplet (catalog id) call this MCP method on this server? -/
  acl : String → String → String → Bool := fun _ _ _ => true
  /-- Is a payment handler available? -/
  payments : Bool := false
  /-- Is the registry implemented? -/
  registry : Bool := false
  /-- Permitted `cache` choices. -/
  cache : List String := ["default", "reload", "no-store"]
  allowances : List Allowance := []

/-- What an operation is waiting for. -/
inductive Wait where
  /-- The operation's host call. -/
  | main
  /-- `registry.call`: the verified entry, before publication. -/
  | describe
  /-- The user's decision on a payment offer. -/
  | consent (offer : Json) (price : Nat) (payMethod : String)
  /-- Settlement and the final response. -/
  | pay
  deriving DecidableEq, Repr

/-- One operation in flight for an endpoint. `key` is the tag of its deadline timer
and its transport id; `call` is the tag of its outstanding host call. -/
structure Pend where
  key : Nat
  call : Nat
  port : PortId
  client : String
  owner : String
  envId : String
  op : Op
  server : String
  method : String
  mode : PayMode
  /-- Client request: the caller's MCP id, restored in the response. -/
  callerId : Option Json
  /-- Request/registry.call: does the result carry a payload? -/
  awaits : Bool
  limit : Option Nat
  /-- `registry.call`: the call arguments for the second stage. -/
  next : Json
  wait : Wait
  deriving DecidableEq, Repr

/-- An open session: endpoint, server pubkey, and the endpoint's client id. -/
structure Session where
  port : PortId
  server : String
  client : String
  /-- MCP ids this endpoint has used for client requests in this session, completed
  or not (NAP-CVM: reusing one answers `"invalid message"`). Cleared with the session. -/
  used : List String := []
  deriving DecidableEq, Repr

structure St where
  cfg : Cfg
  allowances : List Allowance
  pending : List Pend
  corr : Corr
  sessions : List Session
  /-- Server requests delivered to an endpoint and not yet answered: (endpoint, server, MCP id). -/
  inbound : List (PortId × String × Json)
  next : Nat

def St.init (cfg : Cfg := {}) : St := ⟨cfg, cfg.allowances, [], ⟨[], 0⟩, [], [], 0⟩

/-! ### Results -/

def opType : Op → String
  | .discover => "cvm.discover.result" | .request => "cvm.request.result"
  | .close => "cvm.close.result" | .registryList => "cvm.registry.list.result"
  | .registryHas => "cvm.registry.has.result" | .registryDescribe => "cvm.registry.describe.result"
  | .registryCall => "cvm.registry.call.result"

def result (op : Op) (id : String) (fields : List (String × Option Json)) : Json :=
  Json.msg (opType op) (("id", some (.str id)) :: fields)

def errResult (op : Op) (id : String) (e : String) : Json := result op id [("error", some (.str e))]

/-- `NapCvm.respond` rendered: the single answer to an operation the shell does not implement. -/
def outJson (o : CvmOut) (op : Op) : Json :=
  match o with
  | .result _ id none => result op id []
  | .result _ id (some e) => errResult op id e
  | .hasResult _ id b => result .registryHas id [("has", some (.bool b))]

/-! ### Validation -/

def isHex64 (s : String) : Bool :=
  s.length = 64 && s.toList.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

def validId : Json → Bool
  | .str _ => true
  | .num n => n.toInt?.isSome
  | _ => false

inductive Form where
  | request (id : Json) (method : String)
  | notification (method : String)
  | response (id : Json)
  deriving DecidableEq, Repr

/-- MCP basic message forms (NAP-CVM §Message handling). -/
def formOf? (m : Json) : Option Form :=
  match m with
  | .obj _ =>
    if m.get? "jsonrpc" ≠ some (.str "2.0") then none
    else if (["params", "result", "error"].any fun k => match m.get? k with
        | some (.obj _) | none => false | _ => true) then none
    else
      let id := m.get? "id"
      let has (k : String) : Bool := (m.get? k).isSome
      match id with
      | some i => if !validId i then none
        else match m.getStr? "method" with
          | some meth => if has "result" || has "error" then none else some (.request i meth)
          | none => if has "method" || has "params" then none
            else if has "result" != has "error" then some (.response i) else none
      | none => match m.getStr? "method" with
          | some meth => if has "result" || has "error" then none else some (.notification meth)
          | none => none
  | _ => none

def setMember (m : Json) (k : String) (v : Json) : Json :=
  match m with
  | .obj kvs => .obj (kvs.map fun (k', x) => if k' = k then (k', v) else (k', x))
  | x => x

/-! ### Bookkeeping -/

def timerCall (key ms : Nat) : Eff := .call ⟨.cvm, key⟩ (.nap .cvm "timer" (.obj [("ms", .nat ms)]))

def rmPend (s : St) (key : Nat) : St :=
  { s with pending := s.pending.filter (·.key != key), corr := expire s.corr key }

/-- Answer an operation: release it and its deadline, send the one result. -/
def complete (s : St) (p : Pend) (fields : List (String × Option Json)) : St × List Eff :=
  (rmPend s p.key, [.effect (.cancel ⟨.cvm, p.key⟩), .send p.port (result p.op p.envId fields)])

def fail (s : St) (p : Pend) (e : String) : St × List Eff := complete s p [("error", some (.str e))]

/-- Start an operation: a deadline and one host call. -/
def launch (s : St) (cx : Ctx) (id : String) (op : Op) (server method : String) (mode : PayMode)
    (callerId : Option Json) (awaits : Bool) (limit : Option Nat) (nxt : Json) (w : Wait)
    (ms : Nat) (c : Call) : St × List Eff :=
  let p : Pend := ⟨s.next, s.next + 1, cx.port, cx.endpointId, cx.catalogId, id, op, server, method,
    mode, callerId, awaits, limit, nxt, w⟩
  ({ s with pending := p :: s.pending, next := s.next + 2 },
   [timerCall s.next ms, .call ⟨.cvm, s.next + 1⟩ c])

def truncate (limit : Option Nat) (xs : List Json) : List Json :=
  match limit with
  | some l => xs.take l
  | none => xs

def allowanceOf (s : St) (p : Pend) (pm : String) : Option Nat :=
  (s.allowances.find? fun a => a.napplet == p.owner && a.server == p.server && a.method == p.method &&
    a.payMethod == pm).map (·.remaining)

def setAllowance (s : St) (p : Pend) (pm : String) (r : Nat) : St :=
  { s with allowances := s.allowances.map fun a =>
      if a.napplet == p.owner && a.server == p.server && a.method == p.method && a.payMethod == pm then
        { a with remaining := r } else a }

/-- Move an operation to a new call. -/
def rewait (s : St) (p : Pend) (w : Wait) (c : Call) : St × List Eff :=
  ({ s with pending := { p with call := s.next, wait := w } :: s.pending.filter (·.key != p.key),
            next := s.next + 1 },
   [.call ⟨.cvm, s.next⟩ c])

def payArgs (p : Pend) (offer : Json) : Json :=
  .obj [("client", .str p.client), ("server", .str p.server), ("offer", offer)]

/-- A payment gate (NAP-CVM §Payment handling with `NapCvm.decidePay`). -/
def gate (s : St) (p : Pend) (offer : Json) : St × List Eff :=
  if !s.cfg.payments then fail s p "payment required" else
  match (offer.get? "amount").bind Json.asNat?, offer.getStr? "method" with
  | some price, some pm =>
    if p.mode = .prompt ∧ price > 0 then
      rewait s p (.consent offer price pm) (.prompt .cvm "payment"
        (.obj [("server", .str p.server), ("method", .str p.method), ("amount", .nat price),
               ("paymentMethod", .str pm), ("offer", offer)]))
    else
      match decidePay p.mode price false (allowanceOf s p pm) with
      | .ok (some r) =>
        if p.mode = .allow ∧ price > 0 then rewait (setAllowance s p pm r) p .pay (.nap .cvm "pay" (payArgs p offer))
        else rewait s p .pay (.nap .cvm "pay" (payArgs p offer))
      | .ok none => rewait s p .pay (.nap .cvm "pay" (payArgs p offer))
      | .error e => fail s p e
  | _, _ => fail s p "payment required"

/-- The final answer of `request` / `registry.call` from a host reply. -/
def answer (s : St) (p : Pend) (j : Json) (gated : Bool) : St × List Eff :=
  match j.get? "payment" with
  | some offer => if gated then fail s p "payment required" else gate s p offer
  | none =>
    match j.getStr? "error" with
    | some e => fail s p e
    | none =>
      if p.op = .registryCall then
        match j.get? "result" with
        | some r@(.obj _) => complete s p [("result", some r)]
        | _ => fail s p "provider unavailable"
      else if p.awaits then
        match j.get? "message" with
        | some m@(.obj _) => complete s p [("message", some (setMember m "id" (p.callerId.getD .null)))]
        | _ => fail s p "relay timeout"
      else complete s p []

/-! ### Component -/

/-- Operations that belong to this endpoint's session with `server`: its client
requests, and `registry.call` work pinned to that server (`options.server`). -/
def inSession (port : PortId) (server : String) (p : Pend) : Bool :=
  p.port == port && (p.op == .request || p.op == .registryCall) && p.server == server

def sessionOps (s : St) (port : PortId) (server : String) : List Pend :=
  s.pending.filter (inSession port server)

def cancelAll (ps : List Pend) : List Eff :=
  ps.flatMap fun p => [.effect (.cancel ⟨.cvm, p.key⟩), .effect (.cancel ⟨.cvm, p.call⟩)]

def closeEffect (client server : String) : Eff :=
  .effect (.nap .cvm "close" (.obj [("client", .str client), ("server", .str server)]))

def timeoutOf (s : St) (t : Option Nat) : Except String Nat := checkTimeout s.cfg.maxTimeout t

def validSelector (sel : Selector) : Bool :=
  (sel.schemaHash.isSome || sel.family.isSome) &&
  (match sel.schemaHash with | some hsh => isHex64 hsh | none => true) &&
  (match sel.family with | some f => f != "" | none => true)

def positive (l : Option Nat) : Bool := match l with | some 0 => false | _ => true

/-- An unimplemented registry operation's single answer. -/
def unimplemented (cx : Ctx) (id : String) (op : Op) : List Eff :=
  (respond (fun _ => false) none cx.port id op).map fun o => .send cx.port (outJson o op)

/-- An accepted outbound request or notification opens the endpoint's session. -/
def openSession (s : St) (cx : Ctx) (server : String) : St :=
  if s.sessions.any (fun x => x.port == cx.port && x.server == server) then s
  else { s with sessions := ⟨cx.port, server, cx.endpointId, []⟩ :: s.sessions }

/-- Record a client request id in the endpoint's session with `server`, opening the
session if needed. -/
def useId (s : St) (cx : Ctx) (server cid : String) : St :=
  if s.sessions.any (fun x => x.port == cx.port && x.server == server) then
    { s with sessions := s.sessions.map fun x =>
        if x.port == cx.port && x.server == server then { x with used := cid :: x.used } else x }
  else { s with sessions := ⟨cx.port, server, cx.endpointId, [cid]⟩ :: s.sessions }

/-- Has this endpoint used `cid` for a client request in its session with `server`? -/
def idUsed (s : St) (port : PortId) (server cid : String) : Bool :=
  s.sessions.any fun x => x.port == port && x.server == server && x.used.contains cid

def Form.method : Form → String
  | .request _ meth | .notification meth => meth
  | .response _ => ""

/-- The `notifications/cancelled` mapping: its `requestId` must be one of this
endpoint's outstanding requests in the session; it becomes that request's transport id. -/
def mapCancel (s : St) (cx : Ctx) (server : String) (m : Json) : Option Json :=
  match ((m.get? "params").bind (·.get? "requestId")) with
  | some rid =>
    match s.corr.pending.find? (fun q => q.endpoint == cx.port && q.server == server &&
        q.callerId == Json.render rid) with
    | some q => some (setMember m "params" (setMember ((m.get? "params").getD .null) "requestId" (.nat q.tid)))
    | none => none
  | none => none

def requestArgs (cx : Ctx) (srv : ServerRef) (o : ReqOpts) (m : Json) : Json :=
  Json.mkObj [("client", some (.str cx.endpointId)), ("server", some (serverJson srv)), ("message", some m),
    ("initialize", o.initMcp.map .bool), ("payment", some (.str (o.payment.getD .prompt).name))]

/-- Publish a validated MCP message (NAP-CVM §Message handling). -/
def acceptForm (s : St) (cx : Ctx) (id : String) (srv : ServerRef) (o : ReqOpts) (ms : Nat) (m : Json) :
    Form → St × List Eff
  | .request i meth =>
    let server := srv.pubkey
    let cid := Json.render i
    if s.corr.pending.any (fun q => q.endpoint == cx.port && q.server == server && q.callerId == cid) ||
        idUsed s cx.port server cid then
      (s, [.send cx.port (errResult .request id "invalid message")])
    else
      launch (useId { s with corr := (sendReq { s.corr with next := s.next } cx.port server cid).1 } cx server cid)
        cx id .request server meth (o.payment.getD .prompt) (some i) true none .null .main ms
        (.nap .cvm "request" (requestArgs cx srv o (setMember m "id" (.nat s.next))))
  | .notification meth =>
    match (if meth = "notifications/cancelled" then mapCancel s cx srv.pubkey m else some m) with
    | none => (s, [.send cx.port (errResult .request id "invalid message")])
    | some m' => launch (openSession s cx srv.pubkey) cx id .request srv.pubkey meth (o.payment.getD .prompt)
        none false none .null .main ms (.nap .cvm "request" (requestArgs cx srv o m'))
  | .response i =>
    if (cx.port, srv.pubkey, i) ∈ s.inbound then
      launch { s with inbound := s.inbound.erase (cx.port, srv.pubkey, i) } cx id .request srv.pubkey ""
        (o.payment.getD .prompt) none false none .null .main ms (.nap .cvm "request" (requestArgs cx srv o m))
    else (s, [.send cx.port (errResult .request id "invalid message")])

def handleRequest (s : St) (_w : World) (cx : Ctx) (id : String) (srv : ServerRef) (msg : Option Json)
    (o : ReqOpts) : St × List Eff :=
  if !isHex64 srv.pubkey then (s, [.send cx.port (errResult .request id "invalid request")]) else
  match timeoutOf s o.timeoutMs with
  | .error e => (s, [.send cx.port (errResult .request id e)])
  | .ok ms =>
    match msg.bind formOf? with
    | none => (s, [.send cx.port (errResult .request id "invalid message")])
    | some f =>
      if !s.cfg.acl cx.catalogId srv.pubkey f.method then
        (s, [.send cx.port (errResult .request id "policy denied")])
      else acceptForm s cx id srv o ms (msg.getD .null) f

def handle (_h : Host) (w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .discover id q =>
    let bad (e : String) := (s, [Eff.send cx.port (errResult .discover id e)])
    let q' := q.getD {}
    if !positive q'.limit then bad "invalid request"
    else if (q'.kinds.getD []).any (· ∉ s.cfg.kinds) then bad "unsupported kind"
    else if q'.kinds = some [] then (s, [.send cx.port (result .discover id [("servers", some (.arr []))])])
    else
      launch s cx id .discover "" "" .deny none true q'.limit .null .main defaultTimeout
        (.nap .cvm "discover" (Json.mkObj [("query", q.map discoverJson)]))
  | .request id srv msg o => handleRequest s w cx id srv msg o
  | .close id srv =>
    if !isHex64 srv.pubkey then (s, [.send cx.port (errResult .close id "invalid request")]) else
    let ops := sessionOps s cx.port srv.pubkey
    let s1 : St := { s with
      pending := s.pending.filter (fun p => !inSession cx.port srv.pubkey p),
      corr := { s.corr with pending := s.corr.pending.filter fun q => !(q.endpoint == cx.port && q.server == srv.pubkey) },
      sessions := s.sessions.filter (fun x => !(x.port == cx.port && x.server == srv.pubkey)),
      inbound := s.inbound.filter fun x => !(x.1 == cx.port && x.2.1 == srv.pubkey) }
    (s1, cancelAll ops ++ ops.map (fun p => .send p.port (errResult p.op p.envId "session closed")) ++
      [closeEffect cx.endpointId srv.pubkey, .send cx.port (result .close id [])])
  | .registryList id q =>
    let q' := q.getD {}
    if !positive q'.limit || !(match q'.schemaHash with | some hsh => isHex64 hsh | none => true) ||
        q'.family == some "" then
      (s, [.send cx.port (errResult .registryList id "invalid request")])
    else if !s.cfg.registry then (s, unimplemented cx id .registryList)
    else launch s cx id .registryList "" "" .deny none true q'.limit .null .main defaultTimeout
      (.nap .cvm "registry.list" (Json.mkObj [("query", q.map regQueryJson)]))
  | .registryHas id sel srv =>
    if !validSelector sel || !(match srv with | some r => isHex64 r.pubkey | none => true) then
      (s, [.send cx.port (errResult .registryHas id "invalid request")])
    else if !s.cfg.registry then (s, unimplemented cx id .registryHas)
    else launch s cx id .registryHas "" "" .deny none true none .null .main defaultTimeout
      (.nap .cvm "registry.has" (Json.mkObj [("selector", some (selectorJson sel)), ("server", srv.map serverJson)]))
  | .registryDescribe id sel srv =>
    if !validSelector sel || !(match srv with | some r => isHex64 r.pubkey | none => true) then
      (s, [.send cx.port (errResult .registryDescribe id "invalid request")])
    else if !s.cfg.registry then (s, unimplemented cx id .registryDescribe)
    else launch s cx id .registryDescribe "" "" .deny none true none .null .main defaultTimeout
      (.nap .cvm "registry.describe" (Json.mkObj [("selector", some (selectorJson sel)), ("server", srv.map serverJson)]))
  | .registryCall id sel tool args o =>
    let bad (e : String) := (s, [Eff.send cx.port (errResult .registryCall id e)])
    if !validSelector sel || !(match o.server with | some r => isHex64 r.pubkey | none => true) then
      bad "invalid request" else
    match o.cache with
    | some c => if c ∉ ["default", "reload", "no-store"] then bad "invalid request"
        else if c ∉ s.cfg.cache then bad "cache policy denied" else
        match timeoutOf s o.timeoutMs with
        | .error e => bad e
        | .ok ms =>
          if !s.cfg.registry then (s, unimplemented cx id .registryCall) else
          let server := (o.server.map (·.pubkey)).getD ""
          if !s.cfg.acl cx.catalogId server "tools/call" then bad "policy denied" else
          launch s cx id .registryCall server "tools/call" (o.payment.getD .prompt) none true none
            (Json.mkObj [("client", some (.str cx.endpointId)), ("selector", some (selectorJson sel)),
              ("tool", some (.str tool)), ("args", args.map .obj), ("server", o.server.map serverJson),
              ("initialize", o.initMcp.map .bool), ("payment", some (.str (o.payment.getD .prompt).name)),
              ("cache", o.cache.map .str)])
            .describe ms (.nap .cvm "registry.describe"
              (Json.mkObj [("selector", some (selectorJson sel)), ("server", o.server.map serverJson)]))
    | none =>
      match timeoutOf s o.timeoutMs with
      | .error e => bad e
      | .ok ms =>
        if !s.cfg.registry then (s, unimplemented cx id .registryCall) else
        let server := (o.server.map (·.pubkey)).getD ""
        if !s.cfg.acl cx.catalogId server "tools/call" then bad "policy denied" else
        launch s cx id .registryCall server "tools/call" (o.payment.getD .prompt) none true none
          (Json.mkObj [("client", some (.str cx.endpointId)), ("selector", some (selectorJson sel)),
            ("tool", some (.str tool)), ("args", args.map .obj), ("server", o.server.map serverJson),
            ("initialize", o.initMcp.map .bool), ("payment", some (.str (o.payment.getD .prompt).name))])
          .describe ms (.nap .cvm "registry.describe"
            (Json.mkObj [("selector", some (selectorJson sel)), ("server", o.server.map serverJson)]))

/-- Verified CEP-15 hash of a tool in a described entry. -/
def verifiedHash (entry : Json) (tool : String) : Option Hash :=
  match (entry.get? "tools").bind Json.asArr? with
  | some ts => (ts.find? fun t => t.getStr? "name" == some tool).bind (·.getStr? "schemaHash")
  | none => none

/-- `registry.call`: the requested tool's verified hash must match a hash selector
(`NapCvm.registryCall`); a family selector needs the tool in the verified entry. -/
def hashOk (entry : Json) (next : Json) : Bool :=
  let tool := (next.getStr? "tool").getD ""
  match ((next.get? "selector").getD .null).getStr? "schemaHash" with
  | some hsh => match registryCall (verifiedHash entry) hsh tool with
    | .ok _ => true
    | .error _ => false
  | none => (verifiedHash entry tool).isSome

def onReply (_h : Host) (_w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.pending.find? (·.key == n) with
  | some p =>
    -- deadline reached first
    let (s1, e) := fail s p "relay timeout"
    (s1, .effect (.cancel ⟨.cvm, p.call⟩) :: e)
  | none =>
  match s.pending.find? (·.call == n) with
  | none => (s, [])
  | some p =>
    let j := match rep with | .json j => j | _ => .obj []
    match p.wait, rep with
    | .consent offer price pm, .decision true _ =>
      match decidePay p.mode price true (allowanceOf s p pm) with
      | .ok _ => rewait s p .pay (.nap .cvm "pay" (payArgs p offer))
      | .error e => fail s p e
    | .consent .., _ => fail s p "payment denied"
    | .pay, _ => answer s p j true
    | .describe, _ =>
      match j.get? "entry" with
      | none => fail s p ((j.getStr? "error").getD "schema mismatch")
      | some entry =>
        if !hashOk entry p.next then fail s p "schema mismatch"
        else rewait s p .main (.nap .cvm "registry.call" p.next)
    | .main, _ =>
      match p.op with
      | .request | .registryCall => answer s p j false
      | .discover =>
        match (j.get? "servers").bind Json.asArr? with
        | some xs => complete s p [("servers", some (.arr (truncate p.limit xs)))]
        | none => fail s p ((j.getStr? "error").getD "relay timeout")
      | .registryList =>
        match (j.get? "entries").bind Json.asArr? with
        | some xs => complete s p [("entries", some (.arr (truncate p.limit xs)))]
        | none => fail s p ((j.getStr? "error").getD "relay timeout")
      | .registryHas =>
        match (j.get? "has").bind Json.asBool? with
        | some b => complete s p [("has", some (.bool b))]
        | none => complete s p [("has", some (.bool false))]
      | .registryDescribe =>
        match j.get? "entry" with
        | some e@(.obj _) => complete s p [("entry", some e)]
        | _ => fail s p ((j.getStr? "error").getD "schema mismatch")
      | .close => fail s p "relay timeout"

def onEvent (_h : Host) (w : World) (s : St) : HostEvent → St × List Eff
  | .nap .cvm "event" a =>
    match a.getStr? "client", a.getStr? "server", a.get? "message" with
    | some client, some server, some m =>
      match w.byEndpointId? client with
      | none => (s, [])
      | some cx =>
        if !s.sessions.any (fun x => x.port == cx.port && x.server == server) then (s, []) else
        match formOf? m with
        | some (.request i meth) =>
          if meth = "notifications/payment_required" then (s, []) else
          ({ s with inbound := (cx.port, server, i) :: s.inbound },
           [.send cx.port (Json.msg "cvm.event" [("server", some (.obj [("pubkey", .str server)])), ("message", some m)])])
        | some (.notification meth) =>
          if meth = "notifications/payment_required" then (s, []) else
          (s, [.send cx.port (Json.msg "cvm.event" [("server", some (.obj [("pubkey", .str server)])), ("message", some m)])])
        | _ => (s, [])
    | _, _, _ => (s, [])
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  let mine := s.pending.filter (·.port == p)
  let gone := s.sessions.filter (·.port == p)
  ({ s with pending := s.pending.filter (·.port != p),
            corr := { s.corr with pending := s.corr.pending.filter (·.endpoint != p) },
            sessions := s.sessions.filter (·.port != p),
            inbound := s.inbound.filter (·.1 != p) },
   cancelAll mine ++ gone.map fun x => closeEffect x.client x.server)

def mentions (s : St) (p : PortId) : Bool :=
  s.pending.any (·.port == p) || s.corr.pending.any (·.endpoint == p) ||
  s.sessions.any (·.port == p) || s.inbound.any (·.1 == p)

/-! ### Codec properties -/

theorem serverOf?_serverJson (r : ServerRef) : serverOf? (serverJson r) = some r := by
  obtain ⟨pk, rs⟩ := r
  cases rs <;> simp [serverOf?, serverJson, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, optF]

theorem discoverOf?_discoverJson (q : DiscoverQuery) : discoverOf? (discoverJson q) = some q := by
  obtain ⟨a, b, c, d⟩ := q
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [discoverOf?, discoverJson, Json.mkObj, Json.get?, Json.lookup, optF, Json.isObj, guard,
      asNats?_nats]

theorem regQueryOf?_regQueryJson (q : RegQuery) : regQueryOf? (regQueryJson q) = some q := by
  obtain ⟨a, b, c, d, e⟩ := q
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    simp [regQueryOf?, regQueryJson, Json.mkObj, Json.get?, Json.lookup, optF, Json.isObj, guard]

theorem selectorOf?_selectorJson (q : Selector) : selectorOf? (selectorJson q) = some q := by
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;>
    simp [selectorOf?, selectorJson, Json.mkObj, Json.get?, Json.lookup, optF, Json.isObj, guard]

theorem reqOptsOf?_of (j : Json) (o : ReqOpts) (hj : j.get? "options" = reqOptsJson o) :
    reqOptsOf? j = .ok o := by
  unfold reqOptsOf?
  rw [hj]
  by_cases h0 : o = {}
  · simp [reqOptsJson, h0]
  · obtain ⟨a, b, c⟩ := o
    simp only [reqOptsJson, h0, ↓reduceIte]
    cases a <;> cases b <;> cases c <;>
      simp [Json.mkObj, Json.get?, Json.lookup, optF, Json.isObj, payOf?_name]

theorem regOptsOf?_of (j : Json) (o : Option ServerRef) (hj : j.get? "options" = regOptsJson o) :
    regOptsOf? j = some o := by
  unfold regOptsOf?
  rw [hj]
  cases o <;> simp [regOptsJson, Json.get?, Json.lookup, optF, Json.isObj, guard, serverOf?_serverJson]

theorem callOptsOf?_of (j : Json) (o : CallOpts) (hj : j.get? "options" = callOptsJson o) :
    callOptsOf? j = .ok o := by
  unfold callOptsOf?
  rw [hj]
  by_cases h0 : o = {}
  · simp [callOptsJson, h0]
  · obtain ⟨a, b, c, d, e⟩ := o
    simp only [callOptsJson, h0, ↓reduceIte]
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
      simp [Json.mkObj, Json.get?, Json.lookup, optF, Json.isObj, payOf?_name, serverOf?_serverJson]

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r with
  | discover id q =>
    cases q <;> simp [decode, decodeWith, encodeReq, need, Json.msg, Json.mkObj, Json.getStr?,
      Json.get?, Json.lookup, reqId?, optF, discoverOf?_discoverJson, Functor.map, Except.map]
  | request id srv m o =>
    have ho : reqOptsOf? (encodeReq (.request id srv m o)) = .ok o := by
      apply reqOptsOf?_of
      cases hx : reqOptsJson o <;> cases m <;> simp [encodeReq, Json.msg, Json.mkObj, Json.get?, Json.lookup, hx]
    simp only [encodeReq] at ho ⊢
    simp only [decode, decodeWith, reqId?]
    cases hx : reqOptsJson o <;> cases m <;>
      simp [Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, hx, need, serverOf?_serverJson] <;>
      simp [hx, Json.msg, Json.mkObj] at ho <;> simp [ho, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  | close id srv =>
    simp [decode, decodeWith, encodeReq, need, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
      Json.lookup, reqId?, serverOf?_serverJson, Functor.map, Except.map]
  | registryList id q =>
    cases q <;> simp [decode, decodeWith, encodeReq, need, Json.msg, Json.mkObj, Json.getStr?,
      Json.get?, Json.lookup, reqId?, optF, regQueryOf?_regQueryJson, Functor.map, Except.map]
  | registryHas id sel srv =>
    have ho : regOptsOf? (encodeReq (.registryHas id sel srv)) = some srv := by
      apply regOptsOf?_of
      cases hx : regOptsJson srv <;> simp [encodeReq, Json.msg, Json.mkObj, Json.get?, Json.lookup, hx]
    simp only [encodeReq] at ho ⊢
    simp only [decode, decodeWith, reqId?]
    cases hx : regOptsJson srv <;>
      simp [Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, hx, need, selectorOf?_selectorJson] <;>
      simp [hx, Json.msg, Json.mkObj] at ho <;> simp [ho, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  | registryDescribe id sel srv =>
    have ho : regOptsOf? (encodeReq (.registryDescribe id sel srv)) = some srv := by
      apply regOptsOf?_of
      cases hx : regOptsJson srv <;> simp [encodeReq, Json.msg, Json.mkObj, Json.get?, Json.lookup, hx]
    simp only [encodeReq] at ho ⊢
    simp only [decode, decodeWith, reqId?]
    cases hx : regOptsJson srv <;>
      simp [Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, hx, need, selectorOf?_selectorJson] <;>
      simp [hx, Json.msg, Json.mkObj] at ho <;> simp [ho, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  | registryCall id sel tool args o =>
    have ho : callOptsOf? (encodeReq (.registryCall id sel tool args o)) = .ok o := by
      apply callOptsOf?_of
      cases hx : callOptsJson o <;> cases args <;>
        simp [encodeReq, Json.msg, Json.mkObj, Json.get?, Json.lookup, hx]
    simp only [encodeReq] at ho ⊢
    simp only [decode, decodeWith, reqId?]
    cases hx : callOptsJson o <;> cases args <;>
      simp [Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, hx, need, selectorOf?_selectorJson,
        optF, asObj?] <;>
      simp [hx, Json.msg, Json.mkObj] at ho <;> simp [ho, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]

/-! ### Teardown and `mentions` -/

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions, List.any_filter]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp only [drop, mentions, Bool.or_eq_true, List.any_eq_true, List.mem_filter] at h ⊢
  rcases h with ((⟨x, hx, hq⟩ | ⟨x, hx, hq⟩) | ⟨x, hx, hq⟩) | ⟨x, hx, hq⟩
  · exact .inl (.inl (.inl ⟨x, hx.1, hq⟩))
  · exact .inl (.inl (.inr ⟨x, hx.1, hq⟩))
  · exact .inl (.inr ⟨x, hx.1, hq⟩)
  · exact .inr ⟨x, hx.1, hq⟩

/-- A new state mentions only ports the old one mentions or ports in `P`. -/
def Within (s s' : St) (P : PortId → Prop) : Prop :=
  ∀ q, mentions s' q = true → mentions s q = true ∨ P q

theorem within_of {s s' : St} {P : PortId → Prop}
    (h1 : ∀ x ∈ s'.pending, mentions s x.port = true ∨ P x.port)
    (h2 : ∀ x ∈ s'.corr.pending, mentions s x.endpoint = true ∨ P x.endpoint)
    (h3 : ∀ x ∈ s'.sessions, mentions s x.port = true ∨ P x.port)
    (h4 : ∀ x ∈ s'.inbound, mentions s x.1 = true ∨ P x.1) : Within s s' P := by
  intro q hq
  simp only [mentions, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hq
  rcases hq with ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩
  · exact h1 x hx
  · exact h2 x hx
  · exact h3 x hx
  · exact h4 x hx

theorem m_pending {s : St} {x : Pend} (h : x ∈ s.pending) : mentions s x.port = true := by
  simp only [mentions, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]; exact .inl (.inl (.inl ⟨x, h, rfl⟩))
theorem m_corr {s : St} {x : NapCvm.Pending} (h : x ∈ s.corr.pending) : mentions s x.endpoint = true := by
  simp only [mentions, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]; exact .inl (.inl (.inr ⟨x, h, rfl⟩))
theorem m_session {s : St} {x : Session} (h : x ∈ s.sessions) : mentions s x.port = true := by
  simp only [mentions, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]; exact .inl (.inr ⟨x, h, rfl⟩)
theorem m_inbound {s : St} {x : PortId × String × Json} (h : x ∈ s.inbound) : mentions s x.1 = true := by
  simp only [mentions, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]; exact .inr ⟨x, h, rfl⟩

theorem Within.refl (s : St) (P : PortId → Prop) : Within s s P := fun _ h => .inl h

theorem Within.trans {a b c : St} {P : PortId → Prop} (h1 : Within a b P) (h2 : Within b c P) :
    Within a c P := by
  intro q hq
  rcases h2 q hq with h | h
  · exact h1 q h
  · exact .inr h

theorem Within.mono {a b : St} {P Q : PortId → Prop} (h : Within a b P) (hPQ : ∀ q, P q → Q q) :
    Within a b Q := fun q hq => (h q hq).imp id (hPQ q)

theorem within_rmPend (s : St) (k : Nat) : Within s (rmPend s k) (fun _ => False) :=
  within_of (fun x hx => .inl (m_pending (List.mem_filter.mp hx).1))
    (fun x hx => .inl (m_corr (by simp [rmPend, expire] at hx; exact hx.1)))
    (fun x hx => .inl (m_session hx)) (fun x hx => .inl (m_inbound hx))

theorem within_complete (s : St) (p : Pend) (f : List (String × Option Json)) :
    Within s (complete s p f).1 (fun _ => False) := within_rmPend s p.key

theorem within_fail (s : St) (p : Pend) (e : String) : Within s (fail s p e).1 (fun _ => False) :=
  within_complete s p _

theorem within_rewait (s : St) (p : Pend) (hp : p ∈ s.pending) (w : Wait) (c : Call) :
    Within s (rewait s p w c).1 (fun _ => False) :=
  within_of (by
      intro x hx
      simp only [rewait, List.mem_cons, List.mem_filter] at hx
      rcases hx with rfl | hx
      · exact .inl (show mentions s p.port = true from m_pending hp)
      · exact .inl (m_pending hx.1))
    (fun x hx => .inl (m_corr hx)) (fun x hx => .inl (m_session hx)) (fun x hx => .inl (m_inbound hx))

theorem within_allow (s : St) (al : List Allowance) : Within s { s with allowances := al } (fun _ => False) :=
  within_of (fun x hx => .inl (m_pending hx)) (fun x hx => .inl (m_corr hx))
    (fun x hx => .inl (m_session hx)) (fun x hx => .inl (m_inbound hx))

theorem within_rewait_sa (s : St) (p : Pend) (hp : p ∈ s.pending) (pm : String) (r : Nat) (w : Wait)
    (c : Call) : Within s (rewait (setAllowance s p pm r) p w c).1 (fun _ => False) :=
  within_of (by
      intro x hx
      simp only [rewait, setAllowance, List.mem_cons, List.mem_filter] at hx
      rcases hx with rfl | hx
      · exact .inl (show mentions s p.port = true from m_pending hp)
      · exact .inl (m_pending hx.1))
    (fun x hx => .inl (m_corr hx)) (fun x hx => .inl (m_session hx)) (fun x hx => .inl (m_inbound hx))

theorem within_gate (s : St) (p : Pend) (hp : p ∈ s.pending) (offer : Json) :
    Within s (gate s p offer).1 (fun _ => False) := by
  unfold gate
  repeat' first
    | exact within_fail _ _ _
    | exact within_rewait _ _ hp _ _
    | exact within_rewait_sa _ _ hp _ _ _ _
    | split

theorem within_answer (s : St) (p : Pend) (hp : p ∈ s.pending) (j : Json) (g : Bool) :
    Within s (answer s p j g).1 (fun _ => False) := by
  unfold answer
  split
  · split
    · exact within_fail _ _ _
    · exact within_gate _ _ hp _
  · split
    · exact within_fail _ _ _
    · split
      · split
        · exact within_complete _ _ _
        · exact within_fail _ _ _
      · split
        · split
          · exact within_complete _ _ _
          · exact within_fail _ _ _
        · exact within_complete _ _ _

theorem within_launch (s : St) (cx : Ctx) (id : String) (op : Op) (server method : String) (mode : PayMode)
    (cid : Option Json) (aw : Bool) (l : Option Nat) (nx : Json) (wt : Wait) (ms : Nat) (c : Call) :
    Within s (launch s cx id op server method mode cid aw l nx wt ms c).1 (· = cx.port) :=
  within_of (by
      intro x hx
      simp only [launch, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact .inr rfl
      · exact .inl (m_pending hx))
    (fun x hx => .inl (m_corr hx)) (fun x hx => .inl (m_session hx)) (fun x hx => .inl (m_inbound hx))

theorem within_openSession (s : St) (cx : Ctx) (server : String) :
    Within s (openSession s cx server) (· = cx.port) := by
  unfold openSession
  split
  · exact Within.refl _ _
  · exact within_of (fun x hx => .inl (m_pending hx)) (fun x hx => .inl (m_corr hx))
      (by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .inr rfl
        · exact .inl (m_session hx))
      (fun x hx => .inl (m_inbound hx))

theorem within_useId (s : St) (cx : Ctx) (server cid : String) :
    Within s (useId s cx server cid) (· = cx.port) := by
  unfold useId
  split
  · exact within_of (fun x hx => .inl (m_pending hx)) (fun x hx => .inl (m_corr hx))
      (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        split
        · exact .inl (show mentions s y.port = true from m_session hy)
        · exact .inl (m_session hy))
      (fun x hx => .inl (m_inbound hx))
  · exact within_of (fun x hx => .inl (m_pending hx)) (fun x hx => .inl (m_corr hx))
      (by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .inr rfl
        · exact .inl (m_session hx))
      (fun x hx => .inl (m_inbound hx))

theorem within_sendReq (s : St) (cx : Ctx) (server cid : String) :
    Within s { s with corr := (sendReq { s.corr with next := s.next } cx.port server cid).1 } (· = cx.port) :=
  within_of (fun x hx => .inl (m_pending hx))
    (by
      intro x hx
      simp only [sendReq, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact .inr rfl
      · exact .inl (m_corr hx))
    (fun x hx => .inl (m_session hx)) (fun x hx => .inl (m_inbound hx))

theorem within_inboundErase (s : St) (x : PortId × String × Json) :
    Within s { s with inbound := s.inbound.erase x } (fun _ => False) :=
  within_of (fun x hx => .inl (m_pending hx)) (fun x hx => .inl (m_corr hx))
    (fun x hx => .inl (m_session hx)) (fun y hy => .inl (m_inbound (List.mem_of_mem_erase hy)))

theorem acceptForm_within (s : St) (cx : Ctx) (id : String) (srv : ServerRef) (o : ReqOpts) (ms : Nat)
    (m : Json) (f : Form) : Within s (acceptForm s cx id srv o ms m f).1 (· = cx.port) := by
  have F : ∀ q, False → q = cx.port := fun _ h => h.elim
  cases f with
  | request i meth =>
    simp only [acceptForm]
    split
    · exact Within.refl _ _
    · exact Within.trans (within_sendReq _ _ _ _)
        (Within.trans (within_useId _ _ _ _) (within_launch _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  | notification meth =>
    simp only [acceptForm]
    split
    · exact Within.refl _ _
    · exact Within.trans (within_openSession _ _ _) (within_launch _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  | response i =>
    simp only [acceptForm]
    split
    · exact Within.trans ((within_inboundErase _ _).mono F) (within_launch _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    · exact Within.refl _ _

theorem handleRequest_within (s : St) (w : World) (cx : Ctx) (id : String) (srv : ServerRef)
    (msg : Option Json) (o : ReqOpts) : Within s (handleRequest s w cx id srv msg o).1 (· = cx.port) := by
  unfold handleRequest
  split
  · exact Within.refl _ _
  · split
    · exact Within.refl _ _
    · split
      · exact Within.refl _ _
      · split
        · exact Within.refl _ _
        · exact acceptForm_within _ _ _ _ _ _ _ _

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  have key : Within s (handle h w cx s r).1 (· = cx.port) := by
    cases r with
    | request id srv msg o => exact handleRequest_within s w cx id srv msg o
    | close id srv =>
      simp only [handle]
      split
      · exact Within.refl _ _
      · exact within_of
          (fun x hx => .inl (m_pending (List.mem_filter.mp hx).1))
          (fun x hx => .inl (m_corr (List.mem_filter.mp hx).1))
          (fun x hx => .inl (m_session (List.mem_filter.mp hx).1))
          (fun x hx => .inl (m_inbound (List.mem_filter.mp hx).1))
    | _ =>
      simp only [handle]
      repeat' first
        | (with_reducible exact Within.refl _ _)
        | exact within_launch _ _ _ _ _ _ _ _ _ _ _ _ _ _
        | split
  rcases key q hm with h1 | h1
  · exact .inl h1
  · exact .inr ⟨cx, hcx, h1.symm⟩

theorem onReply_within (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) :
    Within s (onReply h w s n rep).1 (fun _ => False) := by
  unfold onReply
  split
  · rename_i p _; exact within_fail s p "relay timeout"
  · split
    · exact Within.refl _ _
    · rename_i p hp
      have hpm : p ∈ s.pending := List.mem_of_find?_eq_some hp
      try dsimp only
      split
      · split
        · exact within_rewait _ _ hpm _ _
        · exact within_fail _ _ _
      · exact within_fail _ _ _
      · exact within_answer _ _ hpm _ _
      · repeat' first
          | exact within_fail _ _ _
          | exact within_rewait _ _ hpm _ _
          | (try dsimp only); split
      · split
        · exact within_answer _ _ hpm _ _
        · exact within_answer _ _ hpm _ _
        all_goals first
          | exact within_fail _ _ _
          | (split
             · exact within_complete _ _ _
             · first | exact within_fail _ _ _ | exact within_complete _ _ _)

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  rcases onReply_within h w s n rep q hm with h1 | h1
  · exact .inl h1
  · exact h1.elim

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  have key : Within s (onEvent h w s e).1 (fun _ => False) := by
    unfold onEvent
    split
    · split
      · split
        · exact Within.refl _ _
        · rename_i cx _
          split
          · exact Within.refl _ _
          · rename_i hses
            have hs : ∃ x ∈ s.sessions, x.port = cx.port := by
              have h0 := hses
              simp at h0
              obtain ⟨x, hx, h1, -⟩ := h0
              exact ⟨x, hx, h1⟩
            obtain ⟨x, hx, hxp⟩ := hs
            split
            · split
              · exact Within.refl _ _
              · exact within_of (fun y hy => .inl (m_pending hy)) (fun y hy => .inl (m_corr hy))
                  (fun y hy => .inl (m_session hy))
                  (by
                    intro y hy
                    simp only [List.mem_cons] at hy
                    rcases hy with rfl | hy
                    · exact .inl (hxp ▸ m_session hx)
                    · exact .inl (m_inbound hy))
            · split <;> exact Within.refl _ _
            · exact Within.refl _ _
      · exact Within.refl _ _
    · exact Within.refl _ _
  rcases key q hm with h1 | h1
  · exact h1
  · exact h1.elim

/-! ### NAP-CVM properties, lifted -/

/-- Without registry support, each well-formed registry operation gets exactly one
answer: `"unsupported method"`, or `has: false` for `registry.has`
(`NapCvm.exactly_one_result`, `NapCvm.unimplemented_has_false`). Malformed ones are
validated first and answer `"invalid request"` (NAP-CVM: validation errors are not
reported as `unsupported method`). -/
theorem registry_unsupported (h : Host) (w : World) (cx : Ctx) (s : St) (hr : s.cfg.registry = false)
    (id : String) (sel : Selector) (hsel : validSelector sel = true) :
    (handle h w cx s (.registryHas id sel none)).2 =
      [.send cx.port (Json.msg "cvm.registry.has.result" [("id", some (.str id)), ("has", some (.bool false))])] ∧
    ∀ r, (r = .registryList id none ∨ r = .registryDescribe id sel none) →
      (handle h w cx s r).2 = [.send cx.port (errResult (if r = .registryList id none then .registryList
        else .registryDescribe) id "unsupported method")] := by
  refine ⟨?_, ?_⟩
  · simp [handle, hr, hsel, unimplemented, respond, outJson, result, opType]
  · rintro r (rfl | rfl)
    · simp [handle, hr, positive, unimplemented, respond, outJson, errResult]
    · simp [handle, hr, hsel, unimplemented, respond, outJson, errResult]

theorem unimplemented_one (cx : Ctx) (id : String) (op : Op) : (unimplemented cx id op).length = 1 := by
  simp [unimplemented, exactly_one_result]

/-- The deadline of a `cvm.request` is exactly the requested (or default) timeout,
accepted by `NapCvm.checkTimeout`: in range, within shell policy, never clamped. -/
theorem launch_timer {s' : St} {cx : Ctx} {id : String} {op : Op} {server method : String}
    {mode : PayMode} {cid : Option Json} {aw : Bool} {l : Option Nat} {nx : Json} {wt : Wait} {ms : Nat}
    {c : Call} {t : CallTag} {a : Json} (hc : ∀ a', c ≠ .nap .cvm "timer" a')
    (hm : Eff.call t (.nap .cvm "timer" a) ∈ (launch s' cx id op server method mode cid aw l nx wt ms c).2) :
    a = .obj [("ms", .nat ms)] := by
  simp only [launch, timerCall, List.mem_cons, List.mem_singleton, Eff.call.injEq, List.not_mem_nil,
    or_false] at hm
  rcases hm with ⟨-, hm⟩ | ⟨-, hm⟩
  · simp only [Call.nap.injEq] at hm; exact hm.2.2
  · exact absurd hm.symm (hc a)

theorem acceptForm_timer {s : St} {cx : Ctx} {id : String} {srv : ServerRef} {o : ReqOpts} {ms : Nat}
    {m : Json} {f : Form} {t : CallTag} {a : Json}
    (ht : Eff.call t (.nap .cvm "timer" a) ∈ (acceptForm s cx id srv o ms m f).2) :
    a = .obj [("ms", .nat ms)] := by
  cases f with
  | request i meth =>
    simp only [acceptForm] at ht
    split at ht
    · simp at ht
    · exact launch_timer (by simp) ht
  | notification meth =>
    simp only [acceptForm] at ht
    split at ht
    · simp at ht
    · exact launch_timer (by simp) ht
  | response i =>
    simp only [acceptForm] at ht
    split at ht
    · exact launch_timer (by simp) ht
    · simp at ht

/-- The deadline of a `cvm.request` is exactly the requested (or default) timeout,
accepted by `NapCvm.checkTimeout`: in range, within shell policy, never clamped. -/
theorem request_timeout (h : Host) (w : World) (cx : Ctx) (s : St) (id : String) (srv : ServerRef)
    (msg : Option Json) (o : ReqOpts) (t : CallTag) (a : Json)
    (ht : Eff.call t (.nap .cvm "timer" a) ∈ (handle h w cx s (.request id srv msg o)).2) :
    ∃ ms, checkTimeout s.cfg.maxTimeout o.timeoutMs = .ok ms ∧ a = .obj [("ms", .nat ms)] ∧
      ms = o.timeoutMs.getD defaultTimeout ∧ 1 ≤ ms ∧ ms ≤ maxTimeout ∧ ms ≤ s.cfg.maxTimeout := by
  simp only [handle, handleRequest] at ht
  split at ht
  · simp at ht
  · split at ht
    · simp at ht
    · rename_i ms hms
      have key : a = .obj [("ms", .nat ms)] := by
        split at ht
        · simp at ht
        · split at ht
          · simp at ht
          · exact acceptForm_timer ht
      obtain ⟨h1, h2, h3, h4⟩ := timeout_ok hms
      exact ⟨ms, hms, key, h1, h2, h3, h4⟩

/-- After an operation is released (answered, expired or closed), a reply for its
calls produces nothing: no second result, no event (`NapCvm.late_response_dropped`). -/
theorem late_reply_dropped (h : Host) (w : World) (s : St) (k n : Nat) (rep : Reply)
    (hk : ∀ p ∈ s.pending, (p.key = n ∨ p.call = n) → p.key = k) :
    (onReply h w (rmPend s k) n rep).2 = [] := by
  have h1 : (rmPend s k).pending.find? (·.key == n) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp only [rmPend, List.mem_filter, bne_iff_ne, ne_eq] at hp
    have := hk p hp.1
    simp only [beq_iff_eq]
    intro he; exact hp.2 (this (.inl he))
  have h2 : (rmPend s k).pending.find? (·.call == n) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp only [rmPend, List.mem_filter, bne_iff_ne, ne_eq] at hp
    have := hk p hp.1
    simp only [beq_iff_eq]
    intro he; exact hp.2 (this (.inr he))
  simp [onReply, h1, h2]

/-- A `cvm.event` reaches only the endpoint whose client key received it, and only
while that endpoint has a session with the server (no broadcast). -/
theorem event_to_owner (h : Host) (w : World) (s : St) (a : Json) (p : PortId) (m : Json)
    (he : Eff.send p m ∈ (onEvent h w s (.nap .cvm "event" a)).2) :
    ∃ cx ∈ w.live, cx.port = p ∧ a.getStr? "client" = some cx.endpointId ∧
      ∃ x ∈ s.sessions, x.port = p ∧ a.getStr? "server" = some x.server := by
  simp only [onEvent] at he
  split at he
  · rename_i client server msg hc hsv _
    split at he
    · simp at he
    · rename_i cx hcx
      have hlive : cx ∈ w.live := List.mem_of_find?_eq_some hcx
      have hid : cx.endpointId = client := by simpa using List.find?_some hcx
      split at he
      · simp at he
      · rename_i hses
        have h0 := hses
        simp at h0
        obtain ⟨x, hx, h1, h2⟩ := h0
        have hp : p = cx.port := by
          split at he
          · split at he
            · simp at he
            · simp at he; exact he.1
          · split at he
            · simp at he
            · simp at he; exact he.1
          · simp at he
        subst hp
        exact ⟨cx, hlive, rfl, by rw [hc, hid], x, hx, h1, by rw [hsv, h2]⟩
  · simp at he

/-- Payment authority for settlement requests (NAP-CVM §Payment handling). -/
def PayAuth (s : St) (p : Pend) (rep : Reply) : Prop :=
  ∃ price c pm r, decidePay p.mode price c (allowanceOf s p pm) = .ok r ∧ (c = true → ∃ ch, rep = .decision true ch)

theorem rewait_calls {s : St} {p : Pend} {w : Wait} {c c' : Call} {t : CallTag}
    (h : Eff.call t c' ∈ (rewait s p w c).2) : c' = c := by
  simp [rewait] at h; exact h.2

theorem fail_calls {s : St} {p : Pend} {e : String} {t : CallTag} {c : Call} :
    Eff.call t c ∉ (fail s p e).2 := by
  simp [fail, complete]

theorem complete_calls {s : St} {p : Pend} {f : List (String × Option Json)} {t : CallTag} {c : Call} :
    Eff.call t c ∉ (complete s p f).2 := by
  simp [complete]

theorem gate_pay {s : St} {p : Pend} {offer : Json} {t : CallTag} {a : Json} (rep : Reply)
    (h : Eff.call t (.nap .cvm "pay" a) ∈ (gate s p offer).2) : PayAuth s p rep := by
  unfold gate at h
  split at h
  · exact absurd h fail_calls
  · split at h
    · rename_i price pm _ _
      split at h
      · have := rewait_calls h; simp at this
      · split at h
        · rename_i r hd
          exact ⟨price, false, pm, some r, hd, by simp⟩
        · rename_i hd
          exact ⟨price, false, pm, none, hd, by simp⟩
        · exact absurd h fail_calls
    · exact absurd h fail_calls

theorem answer_pay {s : St} {p : Pend} {j : Json} {g : Bool} {t : CallTag} {a : Json} (rep : Reply)
    (h : Eff.call t (.nap .cvm "pay" a) ∈ (answer s p j g).2) : PayAuth s p rep := by
  unfold answer at h
  split at h
  · split at h
    · exact absurd h fail_calls
    · exact gate_pay rep h
  · repeat' first
      | exact absurd h fail_calls
      | exact absurd h complete_calls
      | split at h

/-- The shell asks the host to settle a ContextVM payment only when
`NapCvm.decidePay` allows it for the operation's `payment` mode, the standing
allowance, and (for a consent) the user's decision delivered by this very reply.
With `NapCvm.paid_requires_authority`: a positive price is paid only with
per-invocation consent or a covering allowance. -/
theorem onReply_pay_authorized (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (t : CallTag)
    (a : Json) (hc : Eff.call t (.nap .cvm "pay" a) ∈ (onReply h w s n rep).2) :
    ∃ p ∈ s.pending, PayAuth s p rep := by
  unfold onReply at hc
  split at hc
  · simp [fail, complete] at hc
  · split at hc
    · simp at hc
    · rename_i p hp
      have hpm : p ∈ s.pending := List.mem_of_find?_eq_some hp
      refine ⟨p, hpm, ?_⟩
      try dsimp only at hc
      split at hc
      · split at hc
        · rename_i hd
          exact ⟨_, true, _, _, hd, fun _ => ⟨_, rfl⟩⟩
        · exact absurd hc fail_calls
      · exact absurd hc fail_calls
      · exact answer_pay _ hc
      · repeat' first
          | exact absurd hc fail_calls
          | (have := rewait_calls hc; simp at this; done)
          | ((try dsimp only at hc); split at hc)
      · repeat' first
          | exact answer_pay _ hc
          | exact absurd hc fail_calls
          | exact absurd hc complete_calls
          | split at hc

theorem hashOk_sound {entry nx : Json} {hsh : String} (h : hashOk entry nx = true)
    (hs : ((nx.get? "selector").getD .null).getStr? "schemaHash" = some hsh) :
    verifiedHash entry ((nx.getStr? "tool").getD "") = some hsh := by
  unfold hashOk at h
  simp only [hs] at h
  split at h
  · rename_i t ht
    exact (registry_call_hash_checked ht).2
  · simp at h

theorem answer_no_registry_call {s : St} {p : Pend} {j : Json} {g : Bool} {t : CallTag} {a : Json}
    (h : Eff.call t (.nap .cvm "registry.call" a) ∈ (answer s p j g).2) : False := by
  unfold answer at h
  repeat' first
    | exact absurd h fail_calls
    | exact absurd h complete_calls
    | (unfold gate at h; repeat' first
        | exact absurd h fail_calls
        | (have := rewait_calls h; simp at this; done)
        | split at h)
    | split at h

/-- `registry.call` is published only after the host's verified entry confirms the
tool's CEP-15 hash (`NapCvm.registry_call_hash_checked`), with the arguments
recorded when the napplet asked. -/
theorem onReply_registry_call_checked (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (t : CallTag)
    (a : Json) (hc : Eff.call t (.nap .cvm "registry.call" a) ∈ (onReply h w s n rep).2) :
    ∃ p ∈ s.pending, p.wait = .describe ∧ a = p.next ∧ ∃ entry, hashOk entry p.next = true := by
  unfold onReply at hc
  split at hc
  · simp [fail, complete] at hc
  · split at hc
    · simp at hc
    · rename_i p hp
      have hpm : p ∈ s.pending := List.mem_of_find?_eq_some hp
      refine ⟨p, hpm, ?_⟩
      try dsimp only at hc
      split at hc
      · split at hc
        · have := rewait_calls hc; simp at this
        · exact absurd hc fail_calls
      · exact absurd hc fail_calls
      · exact (answer_no_registry_call hc).elim
      · rename_i hw
        split at hc
        · exact absurd hc fail_calls
        · rename_i entry _
          split at hc
          · exact absurd hc fail_calls
          · rename_i hok
            have := rewait_calls hc
            simp only [Call.nap.injEq, true_and] at this
            exact ⟨hw, this, entry, by simpa using hok⟩
      · repeat' first
          | exact (answer_no_registry_call hc).elim
          | exact absurd hc fail_calls
          | exact absurd hc complete_calls
          | split at hc

/-! ### Vectors (upstream examples) -/

/-- Upstream abbreviates pubkeys and hashes; the vectors use full-length values. -/
def PK : String := "65a334" ++ String.ofList (List.replicate 58 '0')
def HSH : String := "a7f3d9" ++ String.ofList (List.replicate 58 '0')

def exHost : Host :=
  { crypto := ⟨fun _ => "", fun _ => true⟩, verifyEvent := fun _ => true, sniff := fun _ => "",
    rasterize := fun _ => none, looksCiphertext := fun _ => false, encryptedWith := fun _ => none,
    transform := fun b => b }

def exId : Identity := { dTag := some "relay-tool", artifactHash := "h" }

def exCx : Ctx := { port := 5, window := 9, identity := exId, exposed := [.cvm], inst := 0 }

def exWorld : World := { now := 1000, live := [exCx], user := "" }

def sub (s : String) : String := (s.replace "65a334..." PK).replace "a7f3d9..." HSH

def run1 (cfg : Cfg) (s : St) (j : String) : St × List Eff :=
  match decode (Json.parse! (sub j)) with
  | .ok r => handle exHost exWorld exCx { s with cfg := cfg } r
  | _ => (s, [])

def sends (es : List Eff) : List Json := es.filterMap fun | .send _ m => some m | _ => none

def calls (es : List Eff) : List (Nat × Call) := es.filterMap fun | .call t c => some (t.n, c) | _ => none

def mainCall? (es : List Eff) : Option (Nat × Call) := (calls es).getLast?

def sameAs (j : Json) (t : String) : Bool := Json.same j (Json.parse! (sub t))

-- decode of every upstream request example
#guard decode (Json.parse! "{ \"type\": \"cvm.discover\", \"id\": \"d1\", \"query\": { \"search\": \"relay\", \"limit\": 5 } }") matches
  .ok (.discover "d1" (some ⟨some "relay", none, none, some 5⟩))
#guard decode (Json.parse! "{ \"type\": \"cvm.request\", \"id\": \"r1\", \"server\": { \"pubkey\": \"65a334...\", \"relays\": [\"wss://relay.example.com\"] }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": 2, \"method\": \"tools/call\", \"params\": { \"name\": \"get_relay\", \"arguments\": { \"url\": \"wss://relay.example.com\" }, \"_meta\": { \"progressToken\": \"tool-2\" } } }, \"options\": { \"initialize\": true, \"payment\": \"prompt\" } }") matches
  .ok (.request "r1" ⟨"65a334...", some ["wss://relay.example.com"]⟩ (some _) ⟨none, some true, some .prompt⟩)
#guard decode (Json.parse! "{ \"type\": \"cvm.registry.has\", \"id\": \"h1\", \"selector\": { \"family\": \"relatr\" } }") matches
  .ok (.registryHas "h1" ⟨none, some "relatr"⟩ none)
#guard decode (Json.parse! "{ \"type\": \"cvm.registry.describe\", \"id\": \"s1\", \"selector\": { \"family\": \"relatr\" } }") matches
  .ok (.registryDescribe "s1" ⟨none, some "relatr"⟩ none)
#guard decode (Json.parse! "{ \"type\": \"cvm.registry.call\", \"id\": \"c1\", \"selector\": { \"schemaHash\": \"a7f3d9...\" }, \"tool\": \"search_profiles\", \"args\": { \"q\": \"jack\" } }") matches
  .ok (.registryCall "c1" ⟨some "a7f3d9...", none⟩ "search_profiles" (some [("q", .str "jack")]) _)
#guard decode (Json.parse! "{ \"type\": \"cvm.request\", \"id\": \"n1\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"method\": \"notifications/cancelled\", \"params\": { \"requestId\": 2 } } }") matches
  .ok (.request "n1" ⟨"65a334...", none⟩ (some _) _)
#guard decode (Json.parse! "{ \"type\": \"cvm.registry.list\", \"id\": \"l1\" }") matches .ok (.registryList "l1" none)
#guard decode (Json.parse! "{ \"type\": \"cvm.close\", \"id\": \"x1\", \"server\": { \"pubkey\": \"65a334...\" } }") matches .ok (.close "x1" ⟨"65a334...", none⟩)
#guard decode (Json.parse! "{ \"type\": \"cvm.subscribe\", \"id\": \"x1\" }") matches .unknown
#guard match decode (Json.parse! "{ \"type\": \"cvm.request\", \"id\": \"t0\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": {}, \"options\": { \"timeoutMs\": 1.5 } }") with
  | .reject [m] => sameAs m "{\"type\":\"cvm.request.result\",\"id\":\"t0\",\"error\":\"invalid timeout\"}"
  | _ => false

-- discover
#guard
  let (s1, e1) := run1 {} .init "{ \"type\": \"cvm.discover\", \"id\": \"d1\", \"query\": { \"search\": \"relay\", \"limit\": 5 } }"
  match mainCall? e1 with
  | some (n, .nap .cvm "discover" _) =>
    match onReply exHost exWorld s1 n (.json (Json.parse! <| sub "{\"servers\": [ { \"pubkey\": \"65a334...\", \"relays\": [\"wss://relay.example.com\"], \"name\": \"RelayVM\", \"description\": \"Relay intelligence exposed through MCP over Nostr\" } ]}")) with
    | (_, es) => match sends es with
      | [m] => sameAs m "{ \"type\": \"cvm.discover.result\", \"id\": \"d1\", \"servers\": [ { \"pubkey\": \"65a334...\", \"relays\": [\"wss://relay.example.com\"], \"name\": \"RelayVM\", \"description\": \"Relay intelligence exposed through MCP over Nostr\" } ] }"
      | _ => false
  | _ => false

-- tools/call, a server notification, a cancellation of the pending request, answering a server ping
#guard
  let (s1, e1) := run1 {} .init "{ \"type\": \"cvm.request\", \"id\": \"r1\", \"server\": { \"pubkey\": \"65a334...\", \"relays\": [\"wss://relay.example.com\"] }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": 2, \"method\": \"tools/call\", \"params\": { \"name\": \"get_relay\", \"arguments\": { \"url\": \"wss://relay.example.com\" }, \"_meta\": { \"progressToken\": \"tool-2\" } } }, \"options\": { \"initialize\": true, \"payment\": \"prompt\" } }"
  match mainCall? e1 with
  | some (n, .nap .cvm "request" a) =>
    let tid := ((a.get? "message").bind (·.get? "id")).getD .null
    -- progress notification for the owner
    (match onEvent exHost exWorld s1 (.nap .cvm "event" (Json.parse! (sub "{\"client\": \"endpoint-9\", \"server\": \"65a334...\", \"message\": { \"jsonrpc\": \"2.0\", \"method\": \"notifications/progress\", \"params\": { \"progressToken\": \"tool-2\", \"progress\": 50 } }}"))) with
     | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.event\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"method\": \"notifications/progress\", \"params\": { \"progressToken\": \"tool-2\", \"progress\": 50 } } }"
     | _ => false) &&
    -- cancelling MCP request 2 maps to its transport id
    (let (s2, e2) := run1 {} s1 "{ \"type\": \"cvm.request\", \"id\": \"n1\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"method\": \"notifications/cancelled\", \"params\": { \"requestId\": 2 } } }"
     match mainCall? e2 with
     | some (n2, .nap .cvm "request" a2) =>
       ((a2.get? "message").bind (·.get? "params")).bind (·.get? "requestId") == some tid &&
       (a2.get? "message").bind (·.get? "id") == none &&
       match onReply exHost exWorld s2 n2 (.json (Json.parse! "{\"published\": true}")) with
       | (_, es) => match sends es with
         | [m] => sameAs m "{ \"type\": \"cvm.request.result\", \"id\": \"n1\" }"
         | _ => false
     | _ => false) &&
    -- the response, with the caller's id restored
    (match onReply exHost exWorld s1 n (.json (.obj [("message", Json.mkObj [("jsonrpc", some (.str "2.0")), ("id", some tid),
        ("result", some (Json.parse! "{ \"content\": [{ \"type\": \"text\", \"text\": \"{...}\" }], \"isError\": false }"))])])) with
     | (s3, es) =>
       (match sends es with
        | [m] => sameAs m "{ \"type\": \"cvm.request.result\", \"id\": \"r1\", \"message\": { \"jsonrpc\": \"2.0\", \"id\": 2, \"result\": { \"content\": [{ \"type\": \"text\", \"text\": \"{...}\" }], \"isError\": false } } }"
        | _ => false) &&
       -- a late duplicate does nothing
       (onReply exHost exWorld s3 n (.json (Json.parse! "{}"))).2 == [] &&
       -- server ping, then the napplet answers it preserving the id
       match onEvent exHost exWorld s3 (.nap .cvm "event" (Json.parse! (sub "{\"client\": \"endpoint-9\", \"server\": \"65a334...\", \"message\": { \"jsonrpc\": \"2.0\", \"id\": \"srv-7\", \"method\": \"ping\" }}"))) with
       | (s4, [.send 5 ev]) =>
         sameAs ev "{ \"type\": \"cvm.event\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": \"srv-7\", \"method\": \"ping\" } }" &&
         let (s5, e5) := run1 {} s4 "{ \"type\": \"cvm.request\", \"id\": \"answer-1\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": \"srv-7\", \"result\": {} } }"
         match mainCall? e5 with
         | some (n5, .nap .cvm "request" a5) =>
           sameAs ((a5.get? "message").getD .null) "{ \"jsonrpc\": \"2.0\", \"id\": \"srv-7\", \"result\": {} }" &&
           match onReply exHost exWorld s5 n5 (.json (Json.parse! "{\"published\": true}")) with
           | (_, es) => match sends es with
             | [m] => sameAs m "{ \"type\": \"cvm.request.result\", \"id\": \"answer-1\" }"
             | _ => false
         | _ => false
       | _ => false)
  | _ => false

-- unsupported registry and a denied request
#guard
  match run1 {} .init "{ \"type\": \"cvm.registry.list\", \"id\": \"l1\" }" with
  | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.registry.list.result\", \"id\": \"l1\", \"error\": \"unsupported method\" }"
  | _ => false
#guard
  match run1 {} .init "{ \"type\": \"cvm.registry.has\", \"id\": \"h2\", \"selector\": { \"family\": \"relatr\" } }" with
  | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.registry.has.result\", \"id\": \"h2\", \"has\": false }"
  | _ => false
#guard
  match run1 { acl := fun _ _ meth => meth != "tools/list" } .init "{ \"type\": \"cvm.request\", \"id\": \"denied-1\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": 3, \"method\": \"tools/list\" } }" with
  | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.request.result\", \"id\": \"denied-1\", \"error\": \"policy denied\" }"
  | _ => false
-- conformance: invalid messages, timeouts
#guard
  match run1 {} .init "{ \"type\": \"cvm.request\", \"id\": \"i1\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": null, \"method\": \"x\" } }" with
  | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.request.result\", \"id\": \"i1\", \"error\": \"invalid message\" }"
  | _ => false
#guard
  match run1 { maxTimeout := 60000 } .init "{ \"type\": \"cvm.request\", \"id\": \"i2\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": 1, \"method\": \"x\" }, \"options\": { \"timeoutMs\": 120000 } }" with
  | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.request.result\", \"id\": \"i2\", \"error\": \"timeout out of policy\" }"
  | _ => false
#guard
  match run1 {} .init "{ \"type\": \"cvm.request\", \"id\": \"i3\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": 1, \"method\": \"x\" }, \"options\": { \"timeoutMs\": 120000 } }" with
  | (_, e) => (calls e).head? == some (0, .nap .cvm "timer" (.obj [("ms", .nat 120000)])) && (calls e).length == 2

-- registry implemented: has, describe, call by portable hash
#guard
  let cfg : Cfg := { registry := true }
  (let (s1, e1) := run1 cfg .init "{ \"type\": \"cvm.registry.has\", \"id\": \"h1\", \"selector\": { \"family\": \"relatr\" } }"
   match mainCall? e1 with
   | some (n, _) => match sends (onReply exHost exWorld s1 n (.json (Json.parse! "{\"has\": true}"))).2 with
     | [m] => sameAs m "{ \"type\": \"cvm.registry.has.result\", \"id\": \"h1\", \"has\": true }"
     | _ => false
   | none => false) &&
  (let entry := "{ \"family\": \"relatr\", \"schemaHashes\": [\"a7f3d9...\"], \"selected\": { \"pubkey\": \"65a334...\", \"relays\": [\"wss://relay.example.com\"] }, \"tools\": [ { \"name\": \"search_profiles\", \"schemaHash\": \"a7f3d9...\", \"inputSchema\": { \"type\": \"object\", \"properties\": { \"q\": { \"type\": \"string\" } }, \"required\": [\"q\"] } } ] }"
   (let (s1, e1) := run1 cfg .init "{ \"type\": \"cvm.registry.describe\", \"id\": \"s1\", \"selector\": { \"family\": \"relatr\" } }"
    match mainCall? e1 with
    | some (n, _) => match sends (onReply exHost exWorld s1 n (.json (Json.parse! (sub ("{\"entry\": " ++ entry ++ "}"))))).2 with
      | [m] => sameAs m ("{ \"type\": \"cvm.registry.describe.result\", \"id\": \"s1\", \"entry\": " ++ entry ++ " }")
      | _ => false
    | none => false) &&
   (let (s1, e1) := run1 cfg .init "{ \"type\": \"cvm.registry.call\", \"id\": \"c1\", \"selector\": { \"schemaHash\": \"a7f3d9...\" }, \"tool\": \"search_profiles\", \"args\": { \"q\": \"jack\" } }"
    match mainCall? e1 with
    | some (n, .nap .cvm "registry.describe" _) =>
      match onReply exHost exWorld s1 n (.json (Json.parse! (sub ("{\"entry\": " ++ entry ++ "}")))) with
      | (s2, [.call ⟨.cvm, n2⟩ (.nap .cvm "registry.call" _)]) =>
        match sends (onReply exHost exWorld s2 n2 (.json (Json.parse! "{\"result\": { \"content\": [{ \"type\": \"text\", \"text\": \"{...}\" }], \"isError\": false }}"))).2 with
        | [m] => sameAs m "{ \"type\": \"cvm.registry.call.result\", \"id\": \"c1\", \"result\": { \"content\": [{ \"type\": \"text\", \"text\": \"{...}\" }], \"isError\": false } }"
        | _ => false
      | _ => false
    | _ => false))

-- conformance: A and B use MCP id 1 on the same server; A closes; B is unaffected
#guard
  let cxB : Ctx := { exCx with port := 6, window := 10, identity := { exId with dTag := some "b" } }
  let w : World := { exWorld with live := [exCx, cxB] }
  let req := sub "{ \"type\": \"cvm.request\", \"id\": \"q\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": 1, \"method\": \"tools/list\" } }"
  match decode (Json.parse! req) with
  | .ok r =>
    let (s1, _) := handle exHost w exCx .init r
    let (s2, e2) := handle exHost w cxB s1 r
    let (s3, e3) := handle exHost w exCx s2 (.close "x" ⟨PK, none⟩)
    (sends e3).length == 2 &&
    (sends e3).any (sameAs · "{ \"type\": \"cvm.request.result\", \"id\": \"q\", \"error\": \"session closed\" }") &&
    (sends e3).any (sameAs · "{ \"type\": \"cvm.close.result\", \"id\": \"x\" }") &&
    match mainCall? e2 with
    | some (nb, _) => match onReply exHost w s3 nb (.json (Json.parse! "{\"message\": {\"jsonrpc\": \"2.0\", \"id\": 0, \"result\": {}}}")) with
      | (_, es) => (es.filterMap fun | .send p _ => some p | _ => none) == [6]
    | none => false
  | _ => false

-- CVM-1: an MCP id already used for a client request in the session answers
-- "invalid message", even after that request completed; closing the session clears it.
#guard
  let req := "{ \"type\": \"cvm.request\", \"id\": \"r\", \"server\": { \"pubkey\": \"65a334...\" }, \"message\": { \"jsonrpc\": \"2.0\", \"id\": 7, \"method\": \"tools/list\" } }"
  let (s1, e1) := run1 {} .init req
  match mainCall? e1 with
  | some (n, _) =>
    let (s2, _) := onReply exHost exWorld s1 n (.json (Json.parse! "{\"message\": {\"jsonrpc\": \"2.0\", \"id\": 0, \"result\": {}}}"))
    s2.pending.isEmpty &&
    (match run1 {} s2 req with
     | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.request.result\", \"id\": \"r\", \"error\": \"invalid message\" }"
     | _ => false) &&
    let (s3, _) := run1 {} s2 "{ \"type\": \"cvm.close\", \"id\": \"x\", \"server\": { \"pubkey\": \"65a334...\" } }"
    (calls (run1 {} s3 req).2).length == 2
  | none => false

-- CVM-2: validation comes before "unsupported method" when the registry is absent.
#guard
  (match run1 {} .init "{ \"type\": \"cvm.registry.list\", \"id\": \"l2\", \"query\": { \"limit\": 0 } }" with
   | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.registry.list.result\", \"id\": \"l2\", \"error\": \"invalid request\" }"
   | _ => false) &&
  (match run1 {} .init "{ \"type\": \"cvm.registry.has\", \"id\": \"h3\", \"selector\": { \"schemaHash\": \"zz\" } }" with
   | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.registry.has.result\", \"id\": \"h3\", \"error\": \"invalid request\" }"
   | _ => false) &&
  (match run1 {} .init "{ \"type\": \"cvm.registry.describe\", \"id\": \"s2\", \"selector\": {} }" with
   | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.registry.describe.result\", \"id\": \"s2\", \"error\": \"invalid request\" }"
   | _ => false) &&
  (match run1 {} .init "{ \"type\": \"cvm.registry.call\", \"id\": \"c2\", \"selector\": { \"family\": \"relatr\" }, \"tool\": \"t\", \"options\": { \"cache\": \"bogus\" } }" with
   | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.registry.call.result\", \"id\": \"c2\", \"error\": \"invalid request\" }"
   | _ => false) &&
  (match run1 {} .init "{ \"type\": \"cvm.registry.call\", \"id\": \"c3\", \"selector\": { \"family\": \"relatr\" }, \"tool\": \"t\", \"options\": { \"timeoutMs\": 0 } }" with
   | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.registry.call.result\", \"id\": \"c3\", \"error\": \"invalid timeout\" }"
   | _ => false) &&
  (match run1 {} .init "{ \"type\": \"cvm.registry.call\", \"id\": \"c4\", \"selector\": { \"family\": \"relatr\" }, \"tool\": \"t\" }" with
   | (_, [.send 5 m]) => sameAs m "{ \"type\": \"cvm.registry.call.result\", \"id\": \"c4\", \"error\": \"unsupported method\" }"
   | _ => false)

-- CVM-5: close(server) also finishes registry.call work pinned to that server.
#guard
  let cfg : Cfg := { registry := true }
  let (s1, _) := run1 cfg .init "{ \"type\": \"cvm.registry.call\", \"id\": \"c5\", \"selector\": { \"family\": \"relatr\" }, \"tool\": \"t\", \"options\": { \"server\": { \"pubkey\": \"65a334...\" } } }"
  let (s2, _) := run1 cfg s1 "{ \"type\": \"cvm.registry.call\", \"id\": \"c6\", \"selector\": { \"family\": \"relatr\" }, \"tool\": \"t\" }"
  let (s3, e3) := run1 cfg s2 "{ \"type\": \"cvm.close\", \"id\": \"x\", \"server\": { \"pubkey\": \"65a334...\" } }"
  s3.pending.length == 1 &&
  (match sends e3 with
   | [m1, m2] => sameAs m1 "{ \"type\": \"cvm.registry.call.result\", \"id\": \"c5\", \"error\": \"session closed\" }" &&
       sameAs m2 "{ \"type\": \"cvm.close.result\", \"id\": \"x\" }"
   | _ => false)

end Napplet.Run.Cvm
