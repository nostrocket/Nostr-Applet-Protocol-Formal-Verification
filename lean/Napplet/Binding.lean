/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Json
import Napplet.Wire

/-!
# The napplet side: bootstrap and binding (web projection)

What runs inside the iframe before and around napplet code (NIP-5D §Transport,
`projections/web.md`, and the binding rules each NAP states).

* **Bootstrap.** Before any napplet script runs, the bootstrap creates a
  `MessageChannel`, keeps one port in its closure and sends exactly one window
  message `{type: "napplet.hello"}` to the parent with the other port in the
  transfer list. Every NAP message then travels on the kept port. `boot` is the
  only producer of window messages, and it produces one at most
  (`boot_once`, `window_only_hello`).
* **Requests.** A method call becomes one envelope built by the domain's
  `encodeReq` (each component proves `decode (encodeReq r) = .ok r`) with a fresh
  `id`. The SDK uses `crypto.randomUUID()`; the model uses a counter, and only
  requires that an id is not already pending (`request_fresh`).
* **Correlation.** A result settles the pending request with the same `id` and an
  expected result type, exactly once (`resolve_once`); results nobody waits for
  are ignored.
* **Pushes and buffering.** Pushes go to registered handlers. Upstream requires the
  binding to *retain* some pushes until a handler exists: `intent.deliver`
  (NAP-INTENT), `inc.channel.opened`, `inc.channel.event` and `inc.channel.closed`
  (NAP-INC), `shell.init` (NAP-SHELL: late `onReady` handlers get the retained
  environment), and `media.session.ended` (NAP-MEDIA: late `onEnded` handlers get
  the record once). `register` hands the retained messages to the new handler in
  arrival order (`register_delivers_buffer`). Other pushes with no handler are
  dropped, which the specs allow (for example `theme.changed` with no `onChanged`).
* **Sticky records.** `shell.init` (NAP-SHELL `onReady`, `ready`, `services`),
  `inc.channel.closed` (NAP-INC `onClosed`) and `media.session.ended` (NAP-MEDIA
  `onEnded`) are retained until the endpoint is destroyed, not until the first
  handler: they are kept in `sticky` whether or not a handler is registered, and
  *every* later `register` for their key replays each of them once without removing
  it (`sticky_every_later_registration`).
* **Retired media sessions.** After `media.session.ended` for a `sessionId`, later
  `media.state`, `media.capabilities`, `media.command` and `media.controls` for that
  session are discarded (NAP-MEDIA: "The binding MUST discard late messages for it";
  `retired_discarded`).
* **Convention URIs.** `NapIntent.bindUri` (in `Nap/Intent.lean`) is the binding's
  convention URI normalisation for `intent.invoke` and `inc.emit`.
* **Sidecar hydration.** `relay.event` / `outbox.event` results with
  `sidecar.resources` hydrate the resource cache *before* the event handler runs;
  an existing cache entry wins (NAP-RELAY §Ordering semantics). See `receive`.
-/

namespace Napplet.Binding

/-- A key identifying a push stream: the push type plus its routing field
(`channelId`, `subId`, `sessionId`, `jobId`, ...), if any. -/
structure Key where
  type : String
  route : Option String := none
  deriving DecidableEq, Repr

/-- Pushes whose messages the binding must retain until a handler registers. -/
def retainedTypes : List String :=
  ["intent.deliver", "inc.channel.opened", "inc.channel.event", "inc.channel.closed",
   "shell.init", "media.session.ended"]

/-- Retained pushes kept for every later handler until the endpoint is destroyed. -/
def stickyTypes : List String := ["shell.init", "inc.channel.closed", "media.session.ended"]

/-- Session-scoped media pushes discarded once their session is retired. -/
def retiredLateTypes : List String :=
  ["media.state", "media.capabilities", "media.command", "media.controls"]

/-- The routing field a push type carries, if any. -/
def routeField : String → Option String
  | "inc.channel.event" | "inc.channel.closed" => some "channelId"
  | "inc.event" => some "topic"
  | "relay.event" | "relay.eose" | "relay.closed" => some "subId"
  | "outbox.event" | "outbox.closed" => some "subId"
  | "media.session.ended" | "media.state" | "media.capabilities" | "media.command"
  | "media.controls" => some "sessionId"
  | "pow.state" | "pow.progress" | "pow.done" | "pow.error" => some "jobId"
  | _ => none

def keyOf (j : Json) : Option Key :=
  (j.getStr? "type").map fun t => { type := t, route := (routeField t).bind j.getStr? }

/-- Result types that settle a request of type `t` (NIP-5D: `t.result`; with the
exceptions the NAPs define). -/
def resultTypes (t : String) : List String :=
  match t with
  | "notify.permission.request" => ["notify.permission.result"]
  | "config.get" => ["config.values"]
  | "resource.info" => ["resource.info.result", "resource.info.error"]
  | "resource.bytes" => ["resource.bytes.result", "resource.bytes.error"]
  | "resource.bytesMany" => ["resource.bytesMany.result", "resource.bytesMany.error"]
  | _ => [resultType t]

/-- Request types with no correlated result: fire-and-forget, or streams whose
messages are pushes keyed by `subId` (NAP-RELAY `relay.subscribe`/`relay.close`,
NAP-OUTBOX `outbox.subscribe`/`outbox.close`). -/
def noResult : List String :=
  ["relay.subscribe", "relay.close", "outbox.subscribe", "outbox.close"]

structure Pending where
  /-- Request number; the wire id is `idFor n`. -/
  n : Nat
  /-- Accepted result types. -/
  accepts : List String
  deriving DecidableEq, Repr

structure St where
  /-- `napplet.hello` has been sent (the port is handed over). -/
  booted : Bool
  next : Nat
  pending : List Pending
  handlers : List Key
  /-- Retained pushes, oldest first. -/
  buffer : List (Key × Json)
  /-- Resource cache hydrated from sidecars: URL ↦ entry JSON. -/
  cache : List (String × Json)
  /-- Sticky records (`stickyTypes`), oldest first; never removed before teardown. -/
  sticky : List (Key × Json) := []

def St.init : St := ⟨false, 0, [], [], [], [], []⟩

/-- `k` is a late session-scoped media push for a session already retired. -/
def St.retired (s : St) (k : Key) : Bool :=
  k.type ∈ retiredLateTypes && k.route.isSome &&
    s.sticky.any (·.1 == { type := "media.session.ended", route := k.route })

/-! ### Bootstrap -/

/-- What the bootstrap does through the browser. -/
inductive Window where
  /-- `window.parent.postMessage({type: "napplet.hello"}, '*', [port])`. -/
  | hello
  deriving DecidableEq, Repr

/-- Run the bootstrap: create the channel and hand the port over, once per document. -/
def boot (s : St) : St × List Window :=
  if s.booted then (s, []) else ({ s with booted := true }, [.hello])

theorem boot_once (s : St) : (boot (boot s).1).2 = [] := by
  unfold boot; split <;> simp_all

/-- The hello carries no payload but the type; the window message JSON. -/
def helloJson : Json := Json.msg "napplet.hello" []

/-! ### What napplet code sees -/

inductive App where
  /-- The promise for request `id` settles with this result envelope. -/
  | settle (id : String) (msg : Json)
  /-- A push handler registered under `key` receives this message. -/
  | push (key : Key) (msg : Json)
  deriving DecidableEq, Repr

/-! ### Requests -/

/-- The wire id for the binding's `n`-th request. -/
def idFor (n : Nat) : String := "r" ++ toString n

/-- Send a request built from a fresh id. `build id` is the domain's `encodeReq` for
the method call; its `type` decides what settles it. Returns the new state and
the envelope to post on the port. -/
def request (s : St) (build : String → Json) : St × Json :=
  let m := build (idFor s.next)
  let t := (m.getStr? "type").getD ""
  let s' := { s with next := s.next + 1 }
  if t ∈ noResult then (s', m)
  else ({ s' with pending := ⟨s.next, resultTypes t⟩ :: s.pending }, m)

/-- Invariant: pending requests have distinct numbers, all below the counter. -/
structure Inv (s : St) : Prop where
  lt : ∀ p ∈ s.pending, p.n < s.next
  nodup : (s.pending.map (·.n)).Nodup

theorem Inv.init : Inv St.init := ⟨by simp [St.init], by simp [St.init]⟩

/-- A new request's number is not pending, and the invariant is kept. -/
theorem request_fresh {s : St} (hi : Inv s) (build : String → Json) :
    (∀ p ∈ s.pending, p.n ≠ s.next) ∧ Inv (request s build).1 := by
  refine ⟨fun p hp heq => by have := hi.lt p hp; omega, ?_⟩
  unfold request
  dsimp only
  split
  · exact ⟨fun p hp => by have := hi.lt p hp; simp; omega, hi.nodup⟩
  · refine ⟨?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · have := hi.lt p hp; simp; omega
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, hi.nodup⟩
      simp only [List.mem_map, not_exists, not_and]
      intro p hp heq
      have := hi.lt p hp
      omega

/-! ### Receiving -/

/-- Settle the pending request this result answers, if any. -/
def settle (s : St) (id t : String) (m : Json) : Option (St × List App) :=
  match s.pending.find? (fun p => idFor p.n == id && p.accepts.contains t) with
  | some _ => some ({ s with pending := s.pending.filter (idFor ·.n != id) }, [.settle id m])
  | none => none

/-- Hydrate the resource cache from a read result's `sidecar.resources`; an entry
already cached wins. -/
def hydrate (cache : List (String × Json)) (m : Json) : List (String × Json) :=
  let entries := ((m.get? "result").bind (·.get? "sidecar") |>.bind (·.get? "resources")
    |>.bind Json.asArr?).getD []
  entries.foldl (fun c e =>
    match e.getStr? "url" with
    | some u => if c.any (·.1 == u) then c else c ++ [(u, e)]
    | none => c) cache

/-- One message arriving on the port. -/
def receive (s : St) (m : Json) : St × List App :=
  match m.getStr? "type", m.getStr? "id" with
  | some t, some id =>
    match settle s id t m with
    | some r => r
    | none => pushIn s t m
  | some t, none => pushIn s t m
  | none, _ => (s, [])
where
  pushIn (s : St) (t : String) (m : Json) : St × List App :=
    let k : Key := { type := t, route := (routeField t).bind m.getStr? }
    let s := if t = "relay.event" || t = "outbox.event" then { s with cache := hydrate s.cache m } else s
    if s.retired k then (s, [])
    else if t ∈ stickyTypes then
      ({ s with sticky := s.sticky ++ [(k, m)] }, if s.handlers.contains k then [.push k m] else [])
    else if s.handlers.contains k then (s, [.push k m])
    else if t ∈ retainedTypes then ({ s with buffer := s.buffer ++ [(k, m)] }, [])
    else (s, [])

/-- Register a push handler; retained messages for it are delivered at once, in order:
buffered ones are handed over and removed, sticky ones are replayed and kept. -/
def register (s : St) (k : Key) : St × List App :=
  ({ s with handlers := k :: s.handlers, buffer := s.buffer.filter (·.1 != k) },
   (s.buffer.filter (·.1 == k)).map (fun (k', m) => .push k' m) ++
   (s.sticky.filter (·.1 == k)).map fun (k', m) => .push k' m)

/-! ### Properties -/

/-- A result settles a request at most once: after settling, the same id and type
settle nothing. -/
theorem resolve_once (s : St) (id t : String) (m m' : Json) (r : St × List App)
    (h : settle s id t m = some r) : settle r.1 id t m' = none := by
  unfold settle at h ⊢
  split at h
  · simp at h
    subst h
    have : (s.pending.filter (idFor ·.n != id)).find?
        (fun p => idFor p.n == id && p.accepts.contains t) = none := by
      rw [List.find?_eq_none]
      intro q hq
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at hq
      simp [hq.2]
    dsimp only
    rw [this]
  · simp at h

/-- A retained push is not lost: registering its handler delivers every retained
message for that key, in arrival order (buffered, then sticky), clears the buffered
ones and keeps the sticky ones. -/
theorem register_delivers_buffer (s : St) (k : Key) :
    (register s k).2 = (s.buffer.filter (·.1 == k)).map (fun (k', m) => App.push k' m) ++
      (s.sticky.filter (·.1 == k)).map (fun (k', m) => App.push k' m) ∧
    (∀ e ∈ (register s k).1.buffer, e.1 ≠ k) ∧ (register s k).1.sticky = s.sticky := by
  refine ⟨rfl, ?_, rfl⟩
  intro e he
  simp [register] at he
  exact he.2

/-- Retained (non-sticky) pushes wait in the buffer when no handler is registered. -/
theorem retained_buffered (s : St) (t : String) (m : Json) (ht : t ∈ retainedTypes)
    (hs : t ∉ stickyTypes)
    (hn : ¬ s.handlers.contains { type := t, route := (routeField t).bind m.getStr? }) :
    ((receive.pushIn s t m).1.buffer.map (·.2)).getLast? = some m := by
  have hn' : { type := t, route := (routeField t).bind m.getStr? } ∉ s.handlers := by
    simpa using hn
  have hnr : ∀ s' : St, s'.retired { type := t, route := (routeField t).bind m.getStr? } = false := by
    intro s'
    simp only [St.retired, retiredLateTypes, retainedTypes] at ht ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  unfold receive.pushIn
  by_cases hr : (t = "relay.event" || t = "outbox.event") = true
  · simp [hr, hn', ht, hs, hnr]
  · simp [hr, hn', ht, hs, hnr]

/-- A sticky push is recorded as the newest sticky record, handler or not. -/
theorem sticky_retained (s : St) (t : String) (m : Json) (ht : t ∈ stickyTypes) :
    ((receive.pushIn s t m).1.sticky.map (·.2)).getLast? = some m := by
  have hnr : ∀ s' : St, s'.retired { type := t, route := (routeField t).bind m.getStr? } = false := by
    intro s'
    simp only [St.retired, retiredLateTypes, stickyTypes] at ht ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp
  unfold receive.pushIn
  by_cases hr : (t = "relay.event" || t = "outbox.event") = true
  · simp [hr, ht, hnr]
  · simp [hr, ht, hnr]

theorem pushIn_sticky_mono (s : St) (t : String) (m : Json) (e : Key × Json) (he : e ∈ s.sticky) :
    e ∈ (receive.pushIn s t m).1.sticky := by
  unfold receive.pushIn
  dsimp only
  repeat' split
  all_goals first | exact he | simp [he]

/-- Receiving never removes a sticky record. -/
theorem receive_keeps_sticky (s : St) (m : Json) (e : Key × Json) (he : e ∈ s.sticky) :
    e ∈ (receive s m).1.sticky := by
  unfold receive
  split
  · split
    · rename_i hs
      unfold settle at hs
      split at hs
      · simp at hs; rw [← hs]; exact he
      · simp at hs
    · exact pushIn_sticky_mono _ _ _ _ he
  · exact pushIn_sticky_mono _ _ _ _ he
  · exact he

/-- One step of napplet-side activity: a message arrives, or code registers a handler. -/
def step (s : St) : Json ⊕ Key → St
  | .inl m => (receive s m).1
  | .inr k => (register s k).1

/-- A sticky record (`shell.init`, `inc.channel.closed`, `media.session.ended`) is
delivered to every later registration for its key, however many messages and
registrations (including earlier ones for the same key) came in between. -/
theorem sticky_every_later_registration (s : St) (e : Key × Json) (he : e ∈ s.sticky)
    (steps : List (Json ⊕ Key)) :
    App.push e.1 e.2 ∈ (register (steps.foldl step s) e.1).2 := by
  have hk : e ∈ (steps.foldl step s).sticky := by
    induction steps generalizing s with
    | nil => exact he
    | cons x xs ih =>
      apply ih
      cases x with
      | inl m => exact receive_keeps_sticky _ _ _ he
      | inr k => exact he
  simp only [register, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq]
  exact .inr ⟨e, ⟨hk, rfl⟩, rfl⟩

/-- After `media.session.ended` for a session, a later `media.state`,
`media.capabilities`, `media.command` or `media.controls` for it is discarded:
nothing reaches napplet code and nothing is buffered. -/
theorem retired_discarded (s : St) (t sid : String) (m : Json) (ht : t ∈ retiredLateTypes)
    (hr : m.getStr? "sessionId" = some sid)
    (hend : ∃ j, ({ type := "media.session.ended", route := some sid }, j) ∈ s.sticky) :
    (receive.pushIn s t m).2 = [] ∧ (receive.pushIn s t m).1.buffer = s.buffer ∧
      (receive.pushIn s t m).1.sticky = s.sticky := by
  obtain ⟨j, hj⟩ := hend
  have hroute : (routeField t).bind m.getStr? = some sid := by
    simp only [retiredLateTypes, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> simp [routeField, hr]
  have hret : s.retired { type := t, route := (routeField t).bind m.getStr? } = true := by
    simp only [St.retired, hroute, Option.isSome_some, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq, List.any_eq_true, beq_iff_eq]
    exact ⟨ht, _, hj, rfl⟩
  have hne : ¬ (t = "relay.event" || t = "outbox.event") = true := by
    simp only [retiredLateTypes, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> decide
  unfold receive.pushIn
  simp [hne, hret]

/-- The bootstrap is the only thing that sends a window message, and it sends only
`napplet.hello`. -/
theorem window_only_hello (s : St) (w : Window) (h : w ∈ (boot s).2) : w = .hello := by
  cases w; rfl

/-! ### Vectors -/

#guard (boot St.init).2 == [.hello] && (boot (boot St.init).1).2 == []
#guard
  let (s, m) := request St.init fun id => Json.msg "storage.get" [("id", some (.str id)), ("key", some (.str "theme"))]
  let (_, out) := receive s (Json.msg "storage.get.result" [("id", m.get? "id"), ("value", some (.str "dark"))])
  out.length == 1
#guard
  let s := (receive St.init (Json.parse! "{\"type\":\"intent.deliver\",\"delivery\":{\"sender\":\"x\",\"archetype\":\"a\",\"action\":\"open\",\"convention\":\"napplet:a/open\"}}")).1
  (register s { type := "intent.deliver" }).2.length == 1
-- NAP-SHELL: every late `onReady` gets the retained `shell.init` (not only the first)
#guard
  let s := (receive St.init (Json.parse! "{\"type\":\"shell.init\",\"services\":[]}")).1
  let (s, o1) := register s { type := "shell.init" }
  let (_, o2) := register s { type := "shell.init" }
  (o1.length, o2.length) == (1, 1)
-- NAP-INC: every late `onClosed` gets the terminal record
#guard
  let s := (receive St.init (Json.parse! "{\"type\":\"inc.channel.closed\",\"channelId\":\"c1\",\"reason\":\"closed\"}")).1
  let k : Key := { type := "inc.channel.closed", route := some "c1" }
  let (s, o1) := register s k
  let (_, o2) := register s k
  (o1.length, o2.length) == (1, 1)
-- NAP-MEDIA M1: `onEnded` registered before and after retirement; each new handler gets it once
#guard
  let k : Key := { type := "media.session.ended", route := some "s1" }
  let (s, _) := register St.init k
  let (s, live) := receive s (Json.parse! "{\"type\":\"media.session.ended\",\"sessionId\":\"s1\",\"reason\":\"destroyed\"}")
  let (s, o1) := register s k
  let (_, o2) := register s k
  (live.length, o1.length, o2.length) == (1, 1, 1)
-- NAP-MEDIA M2: late messages for a retired session are discarded
#guard
  let ks : Key := { type := "media.state", route := some "s1" }
  let (s, _) := register St.init ks
  let (s, before) := receive s (Json.parse! "{\"type\":\"media.state\",\"sessionId\":\"s1\"}")
  let s := (receive s (Json.parse! "{\"type\":\"media.session.ended\",\"sessionId\":\"s1\",\"reason\":\"destroyed\"}")).1
  let (_, after) := receive s (Json.parse! "{\"type\":\"media.state\",\"sessionId\":\"s1\"}")
  let (_, other) := receive s (Json.parse! "{\"type\":\"media.state\",\"sessionId\":\"s2\"}")
  (before.length, after.length, other.length) == (1, 0, 0)

end Napplet.Binding
