/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Inc

/-!
# NAP-INC runtime component

Upstream: `napplet/naps` `master`, `naps/NAP-INC.md` at `377bf939`.

Wire (napplet → shell): `inc.emit {topic, payload?}`, `inc.subscribe {id, topic}`,
`inc.unsubscribe {topic}`, `inc.channel.open {id, target}`,
`inc.channel.emit {channelId, payload?}`, `inc.channel.broadcast {payload?}`,
`inc.channel.list {id}`, `inc.channel.close {channelId}`.
Wire (shell → napplet): `inc.subscribe.result {id, error?}`,
`inc.event {topic, sender, payload?}`, `inc.channel.open.result {id, channelId?, peer?, error?}`,
`inc.channel.opened {channelId, peer}`, `inc.channel.event {channelId, sender, payload?}`,
`inc.channel.list.result {id, channels: [{id, peer}]}`, `inc.channel.closed {channelId, reason?}`.

This restates `Napplet.NapInc` with the wire's types: payloads are any JSON
(`Option Json`, absent ≠ `null`), endpoints are ports internally and
`Ctx.endpointId` on the wire, channel ids are shell-assigned opaque strings.

* `sender` (in `inc.event`, `inc.channel.event`) and `peer` (in `inc.channel.opened`)
  come from the authenticated `Ctx`; `Req` has no field that could carry them.
* Topic routing is exact string equality over the complete topic; the topic is
  never parsed (convention-URI transposition is the binding's job, before sending).
* No echo: an emitter never receives its own `inc.event`, nor a channel member its
  own `inc.channel.event`.
* A subscription is a (port, topic) pair; subscribing twice to the same topic is
  one subscription (the binding fans out to its local handlers), so each emit
  reaches each subscriber at most once. `inc.unsubscribe` removes it.
* `inc.channel.open` resolves `target` with `World.byEndpointId?`. It fails with
  `"target not found"` when no live endpoint has that id, the target is the opener
  itself, or the target does not have `inc` exposed (it "cannot receive the
  notification"); with `"target denied"` when `Cfg.openAllowed` refuses; with
  `"channel limit reached"` when either side already has `Cfg.maxChannels`
  channels. On success `inc.channel.opened` to the target precedes the opener's
  result.
* Closing (by a member) notifies both members without `reason`. Endpoint teardown
  (`drop`) removes the endpoint's subscriptions and channels and sends the survivor
  `inc.channel.closed` with `reason: "peer destroyed"`. ACL revocation
  (`HostEvent.nap .inc "revoke"`) closes the endpoint's channels notifying both
  sides and drops its subscriptions.
* Malformed requests: `inc.subscribe` / `inc.channel.open` with a string `id` but a
  missing or non-string `topic` / `target` get their result type with
  `error: "invalid request"`; every other malformed message (no usable `id`, or a
  fire-and-forget type) is dropped.
-/

/-! ## Host operations

* `HostEvent.nap .inc "revoke" {"endpoint": <endpoint id>}`: the shell's INC
  policy for that live endpoint was revoked (NAP-INC §Channel management, "ACL
  revocation"). The runtime closes every channel the endpoint is a member of,
  sending `inc.channel.closed {channelId}` to both members, and drops the
  endpoint's topic subscriptions. An unknown or non-live endpoint id has no effect.
  The endpoint id is `Ctx.endpointId` (`"endpoint-<window id>"`).

No calls or effects: INC is answered entirely inside the runtime. Policy that is not
asynchronous is in `Cfg` (`subscribeAllowed`, `openAllowed`, `maxChannels`).
-/

namespace Napplet.Run.Inc

/-- Shell INC policy. ACL inputs are catalog identifiers (`Ctx.catalogId`). -/
structure Cfg where
  /-- May the napplet with this catalog id subscribe to this topic? -/
  subscribeAllowed : String → String → Bool := fun _ _ => true
  /-- May the opener (catalog id) open a channel to the target (catalog id)? -/
  openAllowed : String → String → Bool := fun _ _ => true
  /-- Maximum concurrent channels per endpoint (kehto `MAX_CHANNELS_PER_WINDOW`). -/
  maxChannels : Nat := 32

/-- An open channel: opener `a`, target `b`, each with the endpoint id bound at open. -/
structure Channel where
  id : String
  a : PortId
  aId : String
  b : PortId
  bId : String
  deriving DecidableEq, Repr

namespace Channel

def has (c : Channel) (p : PortId) : Bool := c.a == p || c.b == p

/-- The other member (port and endpoint id) when `p` is exactly one of the members. -/
def peer? (c : Channel) (p : PortId) : Option (PortId × String) :=
  if c.a == p && c.b != p then some (c.b, c.bId)
  else if c.b == p && c.a != p then some (c.a, c.aId)
  else none

theorem peer?_some {c : Channel} {p q : PortId} {i : String} (h : c.peer? p = some (q, i)) :
    c.has p = true ∧ c.has q = true ∧ q ≠ p := by
  unfold peer? at h
  split at h
  · rename_i hc
    simp at h hc
    obtain ⟨rfl, rfl⟩ := h
    simp [has, hc.1]
    exact hc.2
  · split at h
    · rename_i _ hc
      simp at h hc
      obtain ⟨rfl, rfl⟩ := h
      simp [has, hc.1]
      exact hc.2
    · simp at h

end Channel

structure St where
  cfg : Cfg
  /-- Topic subscriptions, in subscription order. -/
  subs : List (PortId × String)
  channels : List Channel
  /-- Next channel number. -/
  next : Nat

def St.init (cfg : Cfg := {}) : St := ⟨cfg, [], [], 0⟩

inductive Req where
  | emit (topic : String) (payload : Option Json)
  | subscribe (id : String) (topic : String)
  | unsubscribe (topic : String)
  | chOpen (id : String) (target : String)
  | chEmit (channelId : String) (payload : Option Json)
  | chBroadcast (payload : Option Json)
  | chList (id : String)
  | chClose (channelId : String)
  deriving DecidableEq, Repr

/-! ### Codec -/

def decode (j : Json) : Decoded Req :=
  let pl := j.get? "payload"
  match j.getStr? "type" with
  | some "inc.emit" =>
    match j.getStr? "topic" with
    | some t => .ok (.emit t pl)
    | none => .reject []
  | some "inc.subscribe" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match j.getStr? "topic" with
      | some t => .ok (.subscribe id t)
      | none => .reject (errorReply "inc.subscribe.result" j "invalid request")
  | some "inc.unsubscribe" =>
    match j.getStr? "topic" with
    | some t => .ok (.unsubscribe t)
    | none => .reject []
  | some "inc.channel.open" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match j.getStr? "target" with
      | some t => .ok (.chOpen id t)
      | none => .reject (errorReply "inc.channel.open.result" j "invalid request")
  | some "inc.channel.emit" =>
    match j.getStr? "channelId" with
    | some c => .ok (.chEmit c pl)
    | none => .reject []
  | some "inc.channel.broadcast" => .ok (.chBroadcast pl)
  | some "inc.channel.list" =>
    match reqId? j with
    | some id => .ok (.chList id)
    | none => .reject []
  | some "inc.channel.close" =>
    match j.getStr? "channelId" with
    | some c => .ok (.chClose c)
    | none => .reject []
  | _ => .unknown

def encodeReq : Req → Json
  | .emit t pl => Json.msg "inc.emit" [("topic", some (.str t)), ("payload", pl)]
  | .subscribe id t => Json.msg "inc.subscribe" [("id", some (.str id)), ("topic", some (.str t))]
  | .unsubscribe t => Json.msg "inc.unsubscribe" [("topic", some (.str t))]
  | .chOpen id t => Json.msg "inc.channel.open" [("id", some (.str id)), ("target", some (.str t))]
  | .chEmit c pl => Json.msg "inc.channel.emit" [("channelId", some (.str c)), ("payload", pl)]
  | .chBroadcast pl => Json.msg "inc.channel.broadcast" [("payload", pl)]
  | .chList id => Json.msg "inc.channel.list" [("id", some (.str id))]
  | .chClose c => Json.msg "inc.channel.close" [("channelId", some (.str c))]

/-! ### Shell → napplet messages -/

def eventJson (topic sender : String) (pl : Option Json) : Json :=
  Json.msg "inc.event" [("topic", some (.str topic)), ("sender", some (.str sender)), ("payload", pl)]

def subResult (id : String) (err : Option String) : Json :=
  Json.msg "inc.subscribe.result" [("id", some (.str id)), ("error", err.map .str)]

def openedJson (ch peer : String) : Json :=
  Json.msg "inc.channel.opened" [("channelId", some (.str ch)), ("peer", some (.str peer))]

def openOk (id ch peer : String) : Json :=
  Json.msg "inc.channel.open.result"
    [("id", some (.str id)), ("channelId", some (.str ch)), ("peer", some (.str peer))]

def openErr (id err : String) : Json :=
  Json.msg "inc.channel.open.result" [("id", some (.str id)), ("error", some (.str err))]

def chEventJson (ch sender : String) (pl : Option Json) : Json :=
  Json.msg "inc.channel.event" [("channelId", some (.str ch)), ("sender", some (.str sender)), ("payload", pl)]

def listJson (id : String) (infos : List (String × String)) : Json :=
  Json.msg "inc.channel.list.result"
    [("id", some (.str id)),
     ("channels", some (.arr (infos.map fun x => .obj [("id", .str x.1), ("peer", .str x.2)])))]

def closedJson (ch : String) (reason : Option String) : Json :=
  Json.msg "inc.channel.closed" [("channelId", some (.str ch)), ("reason", reason.map .str)]

/-! ### Component -/

/-- Shell-assigned opaque channel id. -/
def chanName (n : Nat) : String := "c-" ++ toString n

/-- Channels endpoint `p` is a member of. -/
def count (s : St) (p : PortId) : Nat := (s.channels.filter (·.has p)).length

def openCh (w : World) (cx : Ctx) (s : St) (id tgt : String) : St × List Eff :=
  match w.byEndpointId? tgt with
  | none => (s, [.send cx.port (openErr id "target not found")])
  | some t =>
    if t.port = cx.port ∨ Domain.inc ∉ t.exposed then
      (s, [.send cx.port (openErr id "target not found")])
    else if s.cfg.openAllowed cx.catalogId t.catalogId = false then
      (s, [.send cx.port (openErr id "target denied")])
    else if s.cfg.maxChannels ≤ count s cx.port ∨ s.cfg.maxChannels ≤ count s t.port then
      (s, [.send cx.port (openErr id "channel limit reached")])
    else
      let ch := chanName s.next
      ({ s with channels := s.channels ++ [⟨ch, cx.port, cx.endpointId, t.port, t.endpointId⟩],
                next := s.next + 1 },
       [.send t.port (openedJson ch cx.endpointId), .send cx.port (openOk id ch t.endpointId)])

def handle (_h : Host) (w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .emit t pl =>
    (s, (s.subs.filter fun x => x.2 == t && x.1 != cx.port).map fun x =>
      .send x.1 (eventJson t cx.endpointId pl))
  | .subscribe id t =>
    if s.cfg.subscribeAllowed cx.catalogId t then
      ({ s with subs := if s.subs.contains (cx.port, t) then s.subs else s.subs ++ [(cx.port, t)] },
       [.send cx.port (subResult id none)])
    else (s, [.send cx.port (subResult id (some "topic rejected by ACL"))])
  | .unsubscribe t => ({ s with subs := s.subs.filter fun x => !(x.1 == cx.port && x.2 == t) }, [])
  | .chOpen id tgt => openCh w cx s id tgt
  | .chEmit ch pl =>
    match s.channels.find? (·.id == ch) with
    | some c =>
      match c.peer? cx.port with
      | some (p, _) => (s, [.send p (chEventJson ch cx.endpointId pl)])
      | none => (s, [])
    | none => (s, [])
  | .chBroadcast pl =>
    (s, s.channels.filterMap fun c =>
      (c.peer? cx.port).map fun x => .send x.1 (chEventJson c.id cx.endpointId pl))
  | .chList id =>
    (s, [.send cx.port (listJson id (s.channels.filterMap fun c =>
      (c.peer? cx.port).map fun x => (c.id, x.2)))])
  | .chClose ch =>
    match s.channels.find? (·.id == ch) with
    | some c =>
      if c.has cx.port then
        ({ s with channels := s.channels.filter (·.id != ch) },
         [.send c.a (closedJson ch none), .send c.b (closedJson ch none)])
      else (s, [])
    | none => (s, [])

def onReply (_h : Host) (_w : World) (s : St) (_n : Nat) (_r : Reply) : St × List Eff := (s, [])

/-- Close every channel of `p` (both members told, no reason) and drop its subscriptions. -/
def revoke (s : St) (p : PortId) : St × List Eff :=
  ({ s with subs := s.subs.filter (·.1 != p), channels := s.channels.filter (!·.has p) },
   (s.channels.filter (·.has p)).flatMap fun c =>
     [.send c.a (closedJson c.id none), .send c.b (closedJson c.id none)])

def onEvent (_h : Host) (w : World) (s : St) : HostEvent → St × List Eff
  | .nap .inc "revoke" args =>
    match args.getStr? "endpoint" >>= w.byEndpointId? with
    | some c => revoke s c.port
    | none => (s, [])
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with subs := s.subs.filter (·.1 != p), channels := s.channels.filter (!·.has p) },
   s.channels.filterMap fun c =>
     (c.peer? p).map fun x => .send x.1 (closedJson c.id (some "peer destroyed")))

def mentions (s : St) (p : PortId) : Bool :=
  s.subs.any (·.1 == p) || s.channels.any (·.has p)

/-! ### Required properties -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r with
  | emit t pl => cases pl <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]
  | chEmit c pl => cases pl <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]
  | chBroadcast pl => cases pl <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]
  | _ => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp only [drop, mentions, Bool.or_eq_true, List.any_eq_true, List.mem_filter] at h ⊢
  rcases h with ⟨x, ⟨hx, -⟩, hq⟩ | ⟨x, ⟨hx, -⟩, hq⟩
  · exact .inl ⟨x, hx, hq⟩
  · exact .inr ⟨x, hx, hq⟩

theorem byEndpointId_live {w : World} {e : String} {c : Ctx} (h : w.byEndpointId? e = some c) :
    c ∈ w.live := List.mem_of_find?_eq_some h

theorem openCh_mentions (w : World) (cx : Ctx) (s : St) (id tgt : String) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (openCh w cx s id tgt).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  unfold openCh at hm
  split at hm
  · exact .inl hm
  · rename_i t ht
    split at hm
    · exact .inl hm
    · split at hm
      · exact .inl hm
      · split at hm
        · exact .inl hm
        · simp only [mentions, Bool.or_eq_true, List.any_append, List.any_cons, List.any_nil,
            Bool.or_false, Channel.has, beq_iff_eq] at hm
          rcases hm with hm | (hm | hm | hm)
          · exact .inl (by simp only [mentions, Channel.has, Bool.or_eq_true]; exact .inl hm)
          · exact .inl (by simp only [mentions, Channel.has, Bool.or_eq_true]; exact .inr hm)
          · exact .inr ⟨cx, hcx, hm⟩
          · exact .inr ⟨t, byEndpointId_live ht, hm⟩

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  cases r with
  | emit => exact .inl hm
  | subscribe id t =>
    simp only [handle] at hm
    split at hm
    · split at hm
      · exact .inl hm
      · simp only [mentions, Bool.or_eq_true, List.any_append, List.any_cons, List.any_nil,
          Bool.or_false, beq_iff_eq] at hm
        rcases hm with (hm | hm) | hm
        · exact .inl (by simp [mentions, hm])
        · exact .inr ⟨cx, hcx, hm⟩
        · exact .inl (by simp [mentions, hm])
    · exact .inl hm
  | unsubscribe t =>
    apply Or.inl
    simp only [handle, mentions, Bool.or_eq_true, List.any_eq_true, List.mem_filter] at hm ⊢
    rcases hm with ⟨x, ⟨hx, -⟩, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  | chOpen id tgt => exact openCh_mentions w cx s id tgt q hcx hm
  | chEmit ch pl =>
    simp only [handle] at hm
    split at hm
    · split at hm <;> exact .inl hm
    · exact .inl hm
  | chBroadcast => exact .inl hm
  | chList => exact .inl hm
  | chClose ch =>
    apply Or.inl
    simp only [handle] at hm
    split at hm
    · split at hm
      · simp only [mentions, Bool.or_eq_true, List.any_eq_true, List.mem_filter] at hm ⊢
        rcases hm with h | ⟨x, ⟨hx, -⟩, hq⟩
        · exact .inl h
        · exact .inr ⟨x, hx, hq⟩
      · exact hm
    · exact hm

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := .inl hm

theorem revoke_mentions (s : St) (p q : PortId) (h : mentions (revoke s p).1 q = true) :
    mentions s q = true := by
  simp only [revoke, mentions, Bool.or_eq_true, List.any_eq_true, List.mem_filter] at h ⊢
  rcases h with ⟨x, ⟨hx, -⟩, hq⟩ | ⟨x, ⟨hx, -⟩, hq⟩
  · exact .inl ⟨x, hx, hq⟩
  · exact .inr ⟨x, hx, hq⟩

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  unfold onEvent at hm
  split at hm
  · split at hm
    · exact revoke_mentions _ _ _ hm
    · exact hm
  · exact hm

/-! ### NAP-INC properties at the component level -/

/-- Topic delivery: only to exact-topic subscribers, never back to the emitter, each
event stamped with the emitter's authenticated endpoint id and carrying the topic
and payload unchanged. -/
theorem emit_delivery (h : Host) (w : World) (cx : Ctx) (s : St) (t : String) (pl : Option Json)
    (e : Eff) (he : e ∈ (handle h w cx s (.emit t pl)).2) :
    ∃ p, e = .send p (eventJson t cx.endpointId pl) ∧ (p, t) ∈ s.subs ∧ p ≠ cx.port := by
  simp only [handle, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at he
  obtain ⟨⟨p, t'⟩, ⟨hm, ht, hne⟩, rfl⟩ := he
  simp only at ht hne
  subst ht
  exact ⟨p, rfl, hm, hne⟩

/-- `emit` changes no state. -/
theorem emit_state (h : Host) (w : World) (cx : Ctx) (s : St) (t : String) (pl : Option Json) :
    (handle h w cx s (.emit t pl)).1 = s := rfl

/-- `inc.subscribe` is always answered once, to the subscriber, with its `id`. -/
theorem subscribe_answered (h : Host) (w : World) (cx : Ctx) (s : St) (id t : String) :
    ∃ err, (handle h w cx s (.subscribe id t)).2 = [.send cx.port (subResult id err)] := by
  simp only [handle]
  split
  · exact ⟨none, rfl⟩
  · exact ⟨_, rfl⟩

/-- A successful open: target's `inc.channel.opened` (peer = opener's authenticated id)
is enqueued before the opener's result (peer = target's id). -/
theorem open_ok (h : Host) (w : World) (cx : Ctx) (s : St) (id tgt : String) (t : Ctx)
    (ht : w.byEndpointId? tgt = some t) (hne : t.port ≠ cx.port) (hinc : Domain.inc ∈ t.exposed)
    (hacl : s.cfg.openAllowed cx.catalogId t.catalogId = true)
    (hl1 : count s cx.port < s.cfg.maxChannels) (hl2 : count s t.port < s.cfg.maxChannels) :
    (handle h w cx s (.chOpen id tgt)).2 =
      [.send t.port (openedJson (chanName s.next) cx.endpointId),
       .send cx.port (openOk id (chanName s.next) t.endpointId)] := by
  simp [handle, openCh, ht, hne, hinc, hacl, Nat.not_le.mpr hl1, Nat.not_le.mpr hl2]

/-- Every open either fails, changing nothing and answering the opener with an
`error`, or succeeds with a live target other than the opener that has `inc`
exposed, and then the target's `inc.channel.opened` precedes the opener's result. -/
theorem open_cases (h : Host) (w : World) (cx : Ctx) (s : St) (id tgt : String) :
    (∃ err, handle h w cx s (.chOpen id tgt) = (s, [.send cx.port (openErr id err)])) ∨
    (∃ t ∈ w.live, t.endpointId = tgt ∧ t.port ≠ cx.port ∧ Domain.inc ∈ t.exposed ∧
      (handle h w cx s (.chOpen id tgt)).2 =
        [.send t.port (openedJson (chanName s.next) cx.endpointId),
         .send cx.port (openOk id (chanName s.next) t.endpointId)]) := by
  simp only [handle, openCh]
  split
  · exact .inl ⟨_, rfl⟩
  · rename_i t ht
    split
    · exact .inl ⟨_, rfl⟩
    · rename_i hc
      split
      · exact .inl ⟨_, rfl⟩
      · split
        · exact .inl ⟨_, rfl⟩
        · have he := List.find?_some ht
          simp only [beq_iff_eq] at he
          refine .inr ⟨t, byEndpointId_live ht, he, ?_, ?_, rfl⟩
          · intro h'; exact hc (.inl h')
          · exact Classical.byContradiction fun h' => hc (.inr h')

/-- Channel emit: delivered only to the other member of a channel the sender belongs
to, stamped with the sender's authenticated endpoint id. -/
theorem chEmit_delivery (h : Host) (w : World) (cx : Ctx) (s : St) (ch : String) (pl : Option Json)
    (e : Eff) (he : e ∈ (handle h w cx s (.chEmit ch pl)).2) :
    ∃ c ∈ s.channels, c.id = ch ∧ ∃ p i, c.peer? cx.port = some (p, i) ∧ p ≠ cx.port ∧
      e = .send p (chEventJson ch cx.endpointId pl) := by
  simp only [handle] at he
  split at he
  · rename_i c hc
    split at he
    · rename_i p i hp
      simp only [List.mem_singleton] at he
      have hid := List.find?_some hc
      simp at hid
      exact ⟨c, List.mem_of_find?_eq_some hc, hid, p, i, hp, (Channel.peer?_some hp).2.2, he⟩
    · simp at he
  · simp at he

/-- Broadcast: one event per channel the sender belongs to, to its other member, never
to the sender, stamped with the sender's endpoint id. -/
theorem broadcast_delivery (h : Host) (w : World) (cx : Ctx) (s : St) (pl : Option Json)
    (e : Eff) (he : e ∈ (handle h w cx s (.chBroadcast pl)).2) :
    ∃ c ∈ s.channels, ∃ p i, c.peer? cx.port = some (p, i) ∧ p ≠ cx.port ∧
      e = .send p (chEventJson c.id cx.endpointId pl) := by
  simp only [handle, List.mem_filterMap, Option.map_eq_some_iff] at he
  obtain ⟨c, hc, ⟨p, i⟩, hp, rfl⟩ := he
  exact ⟨c, hc, p, i, hp, (Channel.peer?_some hp).2.2, rfl⟩

/-- A member's close removes the channel and notifies both members, without `reason`. -/
theorem close_notifies_both (h : Host) (w : World) (cx : Ctx) (s : St) (ch : String) (c : Channel)
    (hc : s.channels.find? (·.id == ch) = some c) (hm : c.has cx.port = true) :
    handle h w cx s (.chClose ch) =
      ({ s with channels := s.channels.filter (·.id != ch) },
       [.send c.a (closedJson ch none), .send c.b (closedJson ch none)]) := by
  simp [handle, hc, hm]

/-- A non-member cannot close or emit on a channel (channel ids grant nothing). -/
theorem nonmember_ignored (h : Host) (w : World) (cx : Ctx) (s : St) (ch : String)
    (hn : ∀ c ∈ s.channels, c.has cx.port = false) (pl : Option Json) :
    handle h w cx s (.chClose ch) = (s, []) ∧ handle h w cx s (.chEmit ch pl) = (s, []) := by
  constructor
  · simp only [handle]
    split
    · rename_i c hc
      simp [hn c (List.mem_of_find?_eq_some hc)]
    · rfl
  · simp only [handle]
    split
    · rename_i c hc
      split
      · rename_i p i hp
        have := (Channel.peer?_some hp).1
        rw [hn c (List.mem_of_find?_eq_some hc)] at this
        simp at this
      · rfl
    · rfl

/-- Endpoint teardown tells every surviving peer `"peer destroyed"`. -/
theorem drop_notifies_peers (s : St) (p q : PortId) (i : String) (c : Channel)
    (hc : c ∈ s.channels) (hp : c.peer? p = some (q, i)) :
    Eff.send q (closedJson c.id (some "peer destroyed")) ∈ (drop s p).2 := by
  simp only [drop, List.mem_filterMap]
  exact ⟨c, hc, by simp [hp]⟩

/-- Teardown leaves no subscription or channel of the endpoint. -/
theorem drop_removes (s : St) (p : PortId) :
    (∀ x ∈ (drop s p).1.subs, x.1 ≠ p) ∧ (∀ c ∈ (drop s p).1.channels, c.has p = false) := by
  constructor
  · intro x hx; simp [drop] at hx; exact hx.2
  · intro c hc; simp [drop] at hc; simpa using hc.2

/-! ### Vectors (upstream examples) -/

section vectors

private def ctxA : Ctx :=
  { port := 1, window := 10, identity := { dTag := some "music-controller", artifactHash := "h1" },
    exposed := [.inc], inst := 0 }
private def ctxB : Ctx :=
  { port := 2, window := 20, identity := { dTag := some "media-player", artifactHash := "h2" },
    exposed := [.inc], inst := 0 }
private def wAB : World := { now := 0, live := [ctxA, ctxB], user := "" }
private def hst : Host :=
  { crypto := { sha256 := fun _ => "", verifySig := fun _ => true }, verifyEvent := fun _ => true,
    sniff := fun _ => "", rasterize := fun _ => none, looksCiphertext := fun _ => false,
    encryptedWith := fun _ => none, transform := id }

private def isOk (d : Decoded Req) (r : Req) : Bool :=
  match d with
  | .ok x => x == r
  | _ => false

private def sendsSame (es : List Eff) (exp : List (PortId × String)) : Bool :=
  es.length == exp.length &&
  (es.zip exp).all fun (e, p, t) => match e with
    | .send q m => q == p && Json.same m (Json.parse! t)
    | _ => false

-- decode: upstream request examples
#guard isOk (decode (Json.parse! "{ \"type\": \"inc.emit\", \"topic\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } }")) (.emit "napplet:profile/open" (some (Json.parse! "{ \"pubkey\": \"abc123...\" }")))
#guard isOk (decode (Json.parse! "{ \"type\": \"inc.subscribe\", \"id\": \"a1\", \"topic\": \"napplet:profile/open\" }")) (.subscribe "a1" "napplet:profile/open")
#guard isOk (decode (Json.parse! "{ \"type\": \"inc.unsubscribe\", \"topic\": \"napplet:profile/open\" }")) (.unsubscribe "napplet:profile/open")
#guard isOk (decode (Json.parse! "{ \"type\": \"inc.channel.open\", \"id\": \"ch1\", \"target\": \"endpoint-media-player\" }")) (.chOpen "ch1" "endpoint-media-player")
#guard isOk (decode (Json.parse! "{ \"type\": \"inc.channel.emit\", \"channelId\": \"c-abc\", \"payload\": { \"command\": \"play\", \"track\": 3 } }")) (.chEmit "c-abc" (some (Json.parse! "{ \"command\": \"play\", \"track\": 3 }")))
#guard isOk (decode (Json.parse! "{ \"type\": \"inc.channel.broadcast\", \"payload\": { \"announcement\": \"shutting down\" } }")) (.chBroadcast (some (Json.parse! "{ \"announcement\": \"shutting down\" }")))
#guard isOk (decode (Json.parse! "{ \"type\": \"inc.channel.list\", \"id\": \"l1\" }")) (.chList "l1")
#guard isOk (decode (Json.parse! "{ \"type\": \"inc.channel.close\", \"channelId\": \"c-abc\" }")) (.chClose "c-abc")
#guard isOk (decode (Json.parse! "{ \"type\": \"inc.emit\", \"topic\": \"t\", \"payload\": null }")) (.emit "t" (some .null))
#guard decode (Json.parse! "{ \"type\": \"inc.publish\", \"topic\": \"t\" }") matches .unknown
#guard decode (Json.parse! "{ \"type\": \"inc.emit\" }") matches .reject []
#guard match decode (Json.parse! "{ \"type\": \"inc.subscribe\", \"id\": \"a9\" }") with
  | .reject [m] => Json.same m (Json.parse! "{\"type\":\"inc.subscribe.result\",\"id\":\"a9\",\"error\":\"invalid request\"}")
  | _ => false

-- response builders: upstream examples verbatim
#guard Json.same (subResult "a1" none) (Json.parse! "{ \"type\": \"inc.subscribe.result\", \"id\": \"a1\" }")
#guard Json.same (subResult "a1" (some "topic rejected by ACL"))
  (Json.parse! "{ \"type\": \"inc.subscribe.result\", \"id\": \"a1\", \"error\": \"topic rejected by ACL\" }")
#guard Json.same (eventJson "napplet:profile/open" "endpoint-social-feed" (some (Json.parse! "{ \"pubkey\": \"abc123...\" }")))
  (Json.parse! "{ \"type\": \"inc.event\", \"topic\": \"napplet:profile/open\", \"sender\": \"endpoint-social-feed\", \"payload\": { \"pubkey\": \"abc123...\" } }")
#guard Json.same (openedJson "c-abc" "endpoint-music-controller")
  (Json.parse! "{ \"type\": \"inc.channel.opened\", \"channelId\": \"c-abc\", \"peer\": \"endpoint-music-controller\" }")
#guard Json.same (openOk "ch1" "c-abc" "endpoint-media-player")
  (Json.parse! "{ \"type\": \"inc.channel.open.result\", \"id\": \"ch1\", \"channelId\": \"c-abc\", \"peer\": \"endpoint-media-player\" }")
#guard Json.same (openErr "ch1" "target not found")
  (Json.parse! "{ \"type\": \"inc.channel.open.result\", \"id\": \"ch1\", \"error\": \"target not found\" }")
#guard Json.same (listJson "l1" [("c-abc", "endpoint-media-player"), ("c-def", "endpoint-chat-widget")])
  (Json.parse! "{ \"type\": \"inc.channel.list.result\", \"id\": \"l1\", \"channels\": [{ \"id\": \"c-abc\", \"peer\": \"endpoint-media-player\" }, { \"id\": \"c-def\", \"peer\": \"endpoint-chat-widget\" }] }")
#guard Json.same (closedJson "c-abc" none) (Json.parse! "{ \"type\": \"inc.channel.closed\", \"channelId\": \"c-abc\" }")
#guard Json.same (closedJson "c-abc" (some "peer destroyed"))
  (Json.parse! "{ \"type\": \"inc.channel.closed\", \"channelId\": \"c-abc\", \"reason\": \"peer destroyed\" }")

-- handle: subscribe, emit (no echo), open, channel emit, list, close, drop
private def s0 : St := .init
private def s1 : St := (handle hst wAB ctxB s0 (.subscribe "a1" "napplet:profile/open")).1
#guard sendsSame (handle hst wAB ctxB s0 (.subscribe "a1" "napplet:profile/open")).2
  [(2, "{ \"type\": \"inc.subscribe.result\", \"id\": \"a1\" }")]
#guard sendsSame (handle hst wAB ctxA s1 (.emit "napplet:profile/open" (some (Json.parse! "{ \"pubkey\": \"abc123...\" }")))).2
  [(2, "{ \"type\": \"inc.event\", \"topic\": \"napplet:profile/open\", \"sender\": \"endpoint-10\", \"payload\": { \"pubkey\": \"abc123...\" } }")]
#guard (handle hst wAB ctxB s1 (.emit "napplet:profile/open" none)).2 == []
#guard (handle hst wAB ctxA s1 (.emit "napplet:profile/open?x=1" none)).2 == []
private def s2 : St := (handle hst wAB ctxA s1 (.chOpen "ch1" "endpoint-20")).1
#guard sendsSame (handle hst wAB ctxA s1 (.chOpen "ch1" "endpoint-20")).2
  [(2, "{ \"type\": \"inc.channel.opened\", \"channelId\": \"c-0\", \"peer\": \"endpoint-10\" }"),
   (1, "{ \"type\": \"inc.channel.open.result\", \"id\": \"ch1\", \"channelId\": \"c-0\", \"peer\": \"endpoint-20\" }")]
#guard sendsSame (handle hst wAB ctxA s1 (.chOpen "ch1" "endpoint-media-player")).2
  [(1, "{ \"type\": \"inc.channel.open.result\", \"id\": \"ch1\", \"error\": \"target not found\" }")]
#guard sendsSame (handle hst wAB ctxA s2 (.chEmit "c-0" (some (Json.parse! "{ \"command\": \"play\", \"track\": 3 }")))).2
  [(2, "{ \"type\": \"inc.channel.event\", \"channelId\": \"c-0\", \"sender\": \"endpoint-10\", \"payload\": { \"command\": \"play\", \"track\": 3 } }")]
#guard sendsSame (handle hst wAB ctxB s2 (.chEmit "c-0" (some (Json.parse! "{ \"status\": \"playing\", \"track\": 3 }")))).2
  [(1, "{ \"type\": \"inc.channel.event\", \"channelId\": \"c-0\", \"sender\": \"endpoint-20\", \"payload\": { \"status\": \"playing\", \"track\": 3 } }")]
#guard sendsSame (handle hst wAB ctxA s2 (.chBroadcast (some (Json.parse! "{ \"announcement\": \"shutting down\" }")))).2
  [(2, "{ \"type\": \"inc.channel.event\", \"channelId\": \"c-0\", \"sender\": \"endpoint-10\", \"payload\": { \"announcement\": \"shutting down\" } }")]
#guard sendsSame (handle hst wAB ctxA s2 (.chList "l1")).2
  [(1, "{ \"type\": \"inc.channel.list.result\", \"id\": \"l1\", \"channels\": [{ \"id\": \"c-0\", \"peer\": \"endpoint-20\" }] }")]
#guard sendsSame (handle hst wAB ctxA s2 (.chClose "c-0")).2
  [(1, "{ \"type\": \"inc.channel.closed\", \"channelId\": \"c-0\" }"),
   (2, "{ \"type\": \"inc.channel.closed\", \"channelId\": \"c-0\" }")]
#guard sendsSame (drop s2 1).2
  [(2, "{ \"type\": \"inc.channel.closed\", \"channelId\": \"c-0\", \"reason\": \"peer destroyed\" }")]
#guard mentions (drop s2 2).1 2 == false
#guard sendsSame (onEvent hst wAB s2 (.nap .inc "revoke" (Json.parse! "{\"endpoint\":\"endpoint-20\"}"))).2
  [(1, "{ \"type\": \"inc.channel.closed\", \"channelId\": \"c-0\" }"),
   (2, "{ \"type\": \"inc.channel.closed\", \"channelId\": \"c-0\" }")]

end vectors

end Napplet.Run.Inc
