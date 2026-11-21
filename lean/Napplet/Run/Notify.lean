/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Notify

/-!
# NAP-NOTIFY runtime component

Upstream: `napplet/naps` PR #11, `naps/NAP-NOTIFY.md` at `67877ef6`.

Wire (napplet → shell, the wire table's names):
`notify.send {id, title, body?, icon?, actions?, channel?, priority?}`,
`notify.dismiss {notificationId}`, `notify.badge {count}`,
`notify.channel.register {channelId, label, description?, defaultPriority?}`,
`notify.permission.request {id, channel?}`.
Wire (shell → napplet): `notify.send.result {id, notificationId?, error?}`,
`notify.permission.result {id, granted}`, `notify.action {notificationId, actionId}`,
`notify.clicked {notificationId}`, `notify.dismissed {notificationId, reason?}`,
`notify.controls {controls}`.

Behaviour.
* `notify.send` runs `NapNotify.send`: refused with `"permission denied"` when the
  endpoint lacks permission, `"rate limited"` over the rate limit; otherwise the
  notification is created with a shell-assigned id `shell-<n>`, sanitised title
  and body, at most three actions, rendered by the host (`Effect.nap .notify "show"`),
  and the result carries `notificationId`. An absent `priority` is `normal`.
* `notify.dismiss` hides the caller's own notification; unknown or foreign ids are
  silently ignored (`NapNotify.dismiss`).
* `notify.badge` sets the endpoint's badge, capped at `Cfg.badgeMax`.
* `notify.channel.register` is passed to the host (which owns channel policy).
* `notify.permission.request` is answered at once with `granted: true` when the
  endpoint already has permission or the shell does not require it; otherwise the
  user is prompted (`Call.prompt`, asynchronous, so other messages keep flowing)
  and the decision grants permission to the endpoint for its lifetime.
* The first `notify.*` request on an endpoint is preceded by one `notify.controls`
  push listing `Cfg.controls` (as kehto does), unless that list is empty.
* User interaction (`HostEvent.nap .notify "clicked" | "action" | "dismissed"`) is
  routed only to the endpoint that owns the notification.

Malformed requests: `notify.send` with a string `id` but a missing/non-string
`title` or a wrongly typed optional field gets
`notify.send.result {id, error: "invalid request"}` (upstream names no error for
invalid input; kehto uses `"invalid notification"`). `notify.permission.request`
with a non-string `channel` gets `notify.permission.result {id, granted: false}`
(the result has no `error` field; this is kehto's choice too). Malformed
fire-and-forget messages and requests without a string `id` are dropped.

State, all per endpoint (`mentions`): active notifications (owner), permission
grants, pending prompts, recent sends (for the rate limit), endpoints that got
`notify.controls`, endpoints with a non-zero badge. Teardown hides every
notification of the endpoint (`NapNotify.cleanup`), cancels its prompts, clears its
badge, and forgets the rest.
-/

/-! ## Host operations

`port` is the endpoint's `PortId` (from `Output.bound`); `napplet` is its catalog id
(`Ctx.catalogId`), for attribution.

* `Effect.nap .notify "show" {notificationId, port, napplet, title, body?, icon?,
  actions: [{id, label}], channel?, priority}`: render a notification in shell UI
  (toast, system notification, notification centre). The host MUST render `title`,
  `body` and labels as plain text, never markup, MUST visibly attribute it to the
  napplet, SHOULD honour `priority` (`low`, `normal`, `high`, `urgent`) and its
  per-channel user settings, and fetches `icon` only under its own resource policy.
* `Effect.nap .notify "hide" {notificationId}`: remove that notification from shell UI.
* `Effect.nap .notify "badge" {port, count}`: show `count` on the napplet's tile, tab
  or icon; `0` clears it.
* `Effect.nap .notify "channel.register" {port, napplet, channelId, label,
  description?, defaultPriority?}`: record a channel the user can configure
  (mute, priority) for this napplet; the host MAY ignore channels.
* `Call.prompt .notify "permission" {port, napplet, channel?}`, reply `decision allowed _`:
  ask the user whether this napplet may show notifications (for `channel`, when
  given). Any other reply counts as a refusal. The prompt MUST NOT block other inputs.
* `HostEvent.nap .notify "clicked" {notificationId}`: the user clicked the body.
* `HostEvent.nap .notify "action" {notificationId, actionId}`: the user clicked an
  action button (ignored unless `actionId` is one of that notification's actions).
* `HostEvent.nap .notify "dismissed" {notificationId, reason?}`: the notification left
  the screen (`reason` one of `user`, `timeout`, `replaced`; anything else is
  dropped). The runtime forgets it.

Events for ids the runtime does not hold are ignored.
-/

namespace Napplet.Run.Notify

open NapNotify

/-- Shell policy. -/
structure Cfg where
  /-- Features pushed in `notify.controls` (`toasts`, `badges`, `actions`, `channels`, `system`). -/
  controls : List String := ["toasts", "badges", "actions", "channels"]
  /-- Text sanitiser applied to title and body before rendering. -/
  sanitize : String → String := id
  /-- Require a granted `notify.permission.request` before `notify.send`. -/
  requirePermission : Bool := true
  /-- Rate limit: at most `rateMax` notifications (and `urgentMax` urgent ones) per
  endpoint in any `rateWindow` seconds. -/
  rateWindow : Nat := 60
  rateMax : Nat := 30
  urgentMax : Nat := 3
  badgeMax : Nat := 9999

structure Pending where
  n : Nat
  port : PortId
  id : String
  deriving DecidableEq, Repr

structure St where
  cfg : Cfg
  ns : NotifyState
  granted : List PortId
  pending : List Pending
  nextCall : Nat
  /-- Successful sends: endpoint, priority, time. -/
  recent : List (PortId × Priority × Nat)
  controlsSent : List PortId
  badged : List PortId

def St.init (cfg : Cfg := {}) : St :=
  { cfg, ns := ⟨[], 0⟩, granted := [], pending := [], nextCall := 0, recent := [],
    controlsSent := [], badged := [] }

/-- The `notify.send` payload as sent (optional fields kept optional). -/
structure Payload where
  title : String
  body : Option String := none
  icon : Option String := none
  actions : Option (List Action) := none
  channel : Option String := none
  priority : Option Priority := none
  deriving DecidableEq, Repr

structure Channel where
  channelId : String
  label : String
  description : Option String := none
  defaultPriority : Option Priority := none
  deriving DecidableEq, Repr

inductive Req where
  | send (id : String) (p : Payload)
  | dismiss (notificationId : String)
  | badge (count : Nat)
  | registerChannel (c : Channel)
  | requestPermission (id : String) (channel : Option String)
  deriving DecidableEq, Repr

/-! ### JSON -/

def priorityName : Priority → String
  | .low => "low" | .normal => "normal" | .high => "high" | .urgent => "urgent"

def priorityOf? : Json → Option Priority
  | .str "low" => some .low | .str "normal" => some .normal | .str "high" => some .high
  | .str "urgent" => some .urgent | _ => none

def actionJson (a : Action) : Json := .obj [("id", .str a.id), ("label", .str a.label)]

def actionOf? (j : Json) : Option Action := do some ⟨← j.getStr? "id", ← j.getStr? "label"⟩

def actionsJson (as : List Action) : Json := .arr (as.map actionJson)

def actionsOf? (j : Json) : Option (List Action) := j.asArr?.bind (·.mapM actionOf?)

/-- An optional member: absent is `some none`, present and well typed is `some (some v)`. -/
def opt {α : Type} (j : Json) (k : String) (f : Json → Option α) : Option (Option α) :=
  match j.get? k with
  | none => some none
  | some v => (f v).map some

def payloadOf? (j : Json) : Option Payload := do
  some { title := ← j.getStr? "title", body := ← opt j "body" Json.asStr?,
         icon := ← opt j "icon" Json.asStr?, actions := ← opt j "actions" actionsOf?,
         channel := ← opt j "channel" Json.asStr?, priority := ← opt j "priority" priorityOf? }

def channelOf? (j : Json) : Option Channel := do
  some { channelId := ← j.getStr? "channelId", label := ← j.getStr? "label",
         description := ← opt j "description" Json.asStr?,
         defaultPriority := ← opt j "defaultPriority" priorityOf? }

theorem actionsOf?_actionsJson (as : List Action) : actionsOf? (actionsJson as) = some as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [actionsOf?, actionsJson, Json.asArr?, Option.bind_some, List.map_cons,
      List.mapM_cons] at ih ⊢
    simp [ih, actionOf?, actionJson, Json.getStr?, Json.get?, Json.lookup]

theorem priorityOf?_name (p : Priority) : priorityOf? (.str (priorityName p)) = some p := by
  cases p <;> rfl

/-! ### Codec -/

def nidStr (n : Nat) : String := "shell-" ++ toString n

def requestTypes : List String :=
  ["notify.send", "notify.dismiss", "notify.badge", "notify.channel.register",
   "notify.permission.request"]

def permissionResult (id : String) (granted : Bool) : Json :=
  Json.msg "notify.permission.result" [("id", some (.str id)), ("granted", some (.bool granted))]

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some "notify.send" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match payloadOf? j with
      | some p => .ok (.send id p)
      | none => .reject (errorReply "notify.send.result" j "invalid request")
  | some "notify.dismiss" =>
    match j.getStr? "notificationId" with
    | some nid => .ok (.dismiss nid)
    | none => .reject []
  | some "notify.badge" =>
    match (j.get? "count").bind Json.asNat? with
    | some c => .ok (.badge c)
    | none => .reject []
  | some "notify.channel.register" =>
    match channelOf? j with
    | some c => .ok (.registerChannel c)
    | none => .reject []
  | some "notify.permission.request" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match opt j "channel" Json.asStr? with
      | some ch => .ok (.requestPermission id ch)
      | none => .reject [permissionResult id false]
  | _ => .unknown

def encodeReq : Req → Json
  | .send id p => Json.msg "notify.send"
      [("id", some (.str id)), ("title", some (.str p.title)), ("body", p.body.map .str),
       ("icon", p.icon.map .str), ("actions", p.actions.map actionsJson),
       ("channel", p.channel.map .str), ("priority", p.priority.map (.str ∘ priorityName))]
  | .dismiss nid => Json.msg "notify.dismiss" [("notificationId", some (.str nid))]
  | .badge c => Json.msg "notify.badge" [("count", some (Json.nat c))]
  | .registerChannel c => Json.msg "notify.channel.register"
      [("channelId", some (.str c.channelId)), ("label", some (.str c.label)),
       ("description", c.description.map .str),
       ("defaultPriority", c.defaultPriority.map (.str ∘ priorityName))]
  | .requestPermission id ch => Json.msg "notify.permission.request"
      [("id", some (.str id)), ("channel", ch.map .str)]

def sendResult (id : String) (nid : Option Nat) (err : Option String) : Json :=
  Json.msg "notify.send.result"
    [("id", some (.str id)), ("notificationId", nid.map (.str ∘ nidStr)), ("error", err.map .str)]

def controlsJson (cs : List String) : Json := Json.msg "notify.controls" [("controls", some (Json.strs cs))]

def showArgs (cx : Ctx) (p : Payload) (n : Shown) : Json :=
  Json.mkObj
    [("notificationId", some (.str (nidStr n.nid))), ("port", some (Json.nat cx.port)),
     ("napplet", some (.str cx.catalogId)), ("title", some (.str n.title)),
     ("body", n.body.map .str), ("icon", p.icon.map .str), ("actions", some (actionsJson n.actions)),
     ("channel", p.channel.map .str), ("priority", some (.str (priorityName n.priority)))]

def hideArgs (nid : Nat) : Json := .obj [("notificationId", .str (nidStr nid))]

def badgeArgs (p : PortId) (c : Nat) : Json := .obj [("port", Json.nat p), ("count", Json.nat c)]

def encodeOut (cx : Ctx) (p : Payload) : NotifyOut → Eff
  | .render n => .effect (.nap .notify "show" (showArgs cx p n))
  | .hide nid => .effect (.nap .notify "hide" (hideArgs nid))
  | .sendResult to id nid err => .send to (sendResult id nid err)

/-! ### Policy -/

def permitted (s : St) (p : PortId) : Bool := !s.cfg.requirePermission || s.granted.contains p

def recentCount (s : St) (now : Nat) (p : PortId) (urgentOnly : Bool) : Nat :=
  (s.recent.filter fun r => r.1 == p && (!urgentOnly || r.2.1 == .urgent) &&
    decide (now < r.2.2 + s.cfg.rateWindow)).length

def limited (s : St) (now : Nat) (p : PortId) (pri : Priority) : Bool :=
  if pri = .urgent then decide (s.cfg.urgentMax ≤ recentCount s now p true)
  else decide (s.cfg.rateMax ≤ recentCount s now p false)

def env (s : St) (now : Nat) : NotifyEnv :=
  { sanitize := s.cfg.sanitize, permitted := permitted s, rateLimited := limited s now }

def toModel (p : Payload) : NotificationPayload :=
  { title := p.title, body := p.body, actions := p.actions.getD [],
    priority := p.priority.getD .normal }

/-! ### Component -/

/-- One `notify.controls` per endpoint, before its first result. -/
def pushControls (s : St) (p : PortId) : St × List Eff :=
  if s.cfg.controls.isEmpty || s.controlsSent.contains p then (s, [])
  else ({ s with controlsSent := p :: s.controlsSent }, [.send p (controlsJson s.cfg.controls)])

def core (w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .send id p =>
    let pri := p.priority.getD .normal
    let ok := permitted s cx.port && !limited s w.now cx.port pri
    let (ns', outs) := NapNotify.send (env s w.now) s.ns cx.port id (toModel p)
    let recent' := s.recent.filter fun r => decide (w.now < r.2.2 + s.cfg.rateWindow)
    ({ s with ns := ns', recent := if ok then (cx.port, pri, w.now) :: recent' else recent' },
     outs.map (encodeOut cx p))
  | .dismiss str =>
    match s.ns.shown.find? (fun n => nidStr n.nid == str) with
    | none => (s, [])
    | some n =>
      let (ns', outs) := NapNotify.dismiss s.ns cx.port n.nid
      ({ s with ns := ns' }, outs.map (encodeOut cx { title := "" }))
  | .badge c =>
    let c' := min c s.cfg.badgeMax
    ({ s with badged := if c' = 0 then s.badged.filter (· != cx.port)
                        else if s.badged.contains cx.port then s.badged else cx.port :: s.badged },
     [.effect (.nap .notify "badge" (badgeArgs cx.port c'))])
  | .registerChannel c =>
    (s, [.effect (.nap .notify "channel.register" (Json.mkObj
      [("port", some (Json.nat cx.port)), ("napplet", some (.str cx.catalogId)),
       ("channelId", some (.str c.channelId)), ("label", some (.str c.label)),
       ("description", c.description.map .str),
       ("defaultPriority", c.defaultPriority.map (.str ∘ priorityName))]))])
  | .requestPermission id ch =>
    if permitted s cx.port then (s, [.send cx.port (permissionResult id true)])
    else
      ({ s with pending := ⟨s.nextCall, cx.port, id⟩ :: s.pending, nextCall := s.nextCall + 1 },
       [.call ⟨.notify, s.nextCall⟩ (.prompt .notify "permission" (Json.mkObj
          [("port", some (Json.nat cx.port)), ("napplet", some (.str cx.catalogId)),
           ("channel", ch.map .str)]))])

def handle (_h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) : St × List Eff :=
  let (s1, pre) := pushControls s cx.port
  let (s2, effs) := core w cx s1 r
  (s2, pre ++ effs)

def onReply (_h : Host) (_w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.pending.find? (·.n == n) with
  | none => (s, [])
  | some p =>
    let ok := match rep with | .decision true _ => true | _ => false
    ({ s with pending := s.pending.filter (·.n != n),
              granted := if ok && !s.granted.contains p.port then p.port :: s.granted else s.granted },
     [.send p.port (permissionResult p.id ok)])

def reasonOf? (j : Json) : Option String :=
  match j.getStr? "reason" with
  | some "user" => some "user" | some "timeout" => some "timeout"
  | some "replaced" => some "replaced" | _ => none

def onEvent (_h : Host) (_w : World) (s : St) : HostEvent → St × List Eff
  | .nap .notify "clicked" args =>
    match (args.getStr? "notificationId").bind fun i => s.ns.shown.find? (nidStr ·.nid == i) with
    | some n => (s, [.send n.owner (Json.msg "notify.clicked" [("notificationId", some (.str (nidStr n.nid)))])])
    | none => (s, [])
  | .nap .notify "action" args =>
    match (args.getStr? "notificationId").bind (fun i => s.ns.shown.find? (nidStr ·.nid == i)),
        args.getStr? "actionId" with
    | some n, some a =>
      if n.actions.any (·.id == a) then
        (s, [.send n.owner (Json.msg "notify.action"
          [("notificationId", some (.str (nidStr n.nid))), ("actionId", some (.str a))])])
      else (s, [])
    | _, _ => (s, [])
  | .nap .notify "dismissed" args =>
    match (args.getStr? "notificationId").bind fun i => s.ns.shown.find? (nidStr ·.nid == i) with
    | some n =>
      ({ s with ns := { s.ns with shown := s.ns.shown.filter (·.nid != n.nid) } },
       [.send n.owner (Json.msg "notify.dismissed"
          [("notificationId", some (.str (nidStr n.nid))), ("reason", (reasonOf? args).map .str)])])
    | none => (s, [])
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  let (ns', outs) := cleanup s.ns p
  ({ s with ns := ns', granted := s.granted.filter (· != p),
            pending := s.pending.filter (·.port != p),
            recent := s.recent.filter (·.1 != p), controlsSent := s.controlsSent.filter (· != p),
            badged := s.badged.filter (· != p) },
   outs.filterMap (fun o => match o with
     | .hide nid => some (.effect (.nap .notify "hide" (hideArgs nid)))
     | _ => none) ++
   (s.pending.filter (·.port == p)).map (fun q => .effect (.cancel ⟨.notify, q.n⟩)) ++
   (if s.badged.contains p then [.effect (.nap .notify "badge" (badgeArgs p 0))] else []))

/-- Every port any per-endpoint state refers to. -/
def ports (s : St) : List PortId :=
  s.ns.shown.map (·.owner) ++ s.granted ++ s.pending.map (·.port) ++ s.recent.map (·.1) ++
  s.controlsSent ++ s.badged

def mentions (s : St) (p : PortId) : Bool := (ports s).contains p

/-! ### Properties: codec -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r with
  | send id p =>
    obtain ⟨t, b, i, as, ch, pr⟩ := p
    cases b <;> cases i <;> cases as <;> cases ch <;> cases pr <;>
      simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?,
        payloadOf?, opt, actionsOf?_actionsJson, priorityOf?_name]
  | dismiss => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]
  | badge => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]
  | registerChannel c =>
    obtain ⟨ci, l, d, dp⟩ := c
    cases d <;> cases dp <;>
      simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup,
        channelOf?, opt, priorityOf?_name]
  | requestPermission id ch =>
    cases ch <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
      Json.lookup, reqId?, opt]

/-! ### Properties: per-endpoint state -/

theorem mentions_iff (s : St) (q : PortId) : mentions s q = true ↔ q ∈ ports s := by
  simp [mentions]

theorem send_owners {env : NotifyEnv} {s : NotifyState} {sender : PortId} {id : String}
    {p : NotificationPayload} {n : Shown} (hn : n ∈ (NapNotify.send env s sender id p).1.shown) :
    n ∈ s.shown ∨ n.owner = sender := by
  unfold NapNotify.send at hn
  split at hn
  · exact .inl hn
  · split at hn
    · exact .inl hn
    · rcases List.mem_cons.mp hn with rfl | hn
      · exact .inr rfl
      · exact .inl hn

theorem dismiss_owners {s : NotifyState} {sender : PortId} {nid : Nat} {n : Shown}
    (hn : n ∈ (NapNotify.dismiss s sender nid).1.shown) : n ∈ s.shown := by
  unfold NapNotify.dismiss at hn
  split at hn
  · exact (List.mem_filter.mp hn).1
  · exact hn

theorem pushControls_ports (s : St) (p q : PortId) (hq : q ∈ ports (pushControls s p).1) :
    q ∈ ports s ∨ q = p := by
  unfold pushControls at hq
  split at hq
  · exact .inl hq
  · simp only [ports, List.mem_append, List.mem_cons] at hq ⊢
    rcases hq with ((((h | h) | h) | h) | h | h) | h
    all_goals first
      | exact .inr h
      | (left; simp_all)

theorem core_ports (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hq : q ∈ ports (core w cx s r).1) : q ∈ ports s ∨ q = cx.port := by
  cases r with
  | send id p =>
    simp only [core, ports, List.mem_append, List.mem_map] at hq ⊢
    rcases hq with ((((⟨n, hn, rfl⟩ | h) | h) | ⟨x, hx, rfl⟩) | h) | h
    · rcases send_owners hn with hn | hn
      · exact .inl (.inl (.inl (.inl (.inl (.inl ⟨n, hn, rfl⟩)))))
      · exact .inr hn
    · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
    · exact .inl (.inl (.inl (.inl (.inr h))))
    · split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact .inr rfl
        · exact .inl (.inl (.inl (.inr ⟨x, (List.mem_filter.mp hx).1, rfl⟩)))
      · exact .inl (.inl (.inl (.inr ⟨x, (List.mem_filter.mp hx).1, rfl⟩)))
    · exact .inl (.inl (.inr h))
    · exact .inl (.inr h)
  | dismiss str =>
    simp only [core] at hq
    split at hq
    · exact .inl hq
    · simp only [ports, List.mem_append, List.mem_map] at hq ⊢
      rcases hq with ((((⟨n, hn, rfl⟩ | h) | h) | h) | h) | h
      · exact .inl (.inl (.inl (.inl (.inl (.inl ⟨n, dismiss_owners hn, rfl⟩)))))
      all_goals simp_all
  | badge c =>
    simp only [core, ports, List.mem_append] at hq ⊢
    rcases hq with ((((h | h) | h) | h) | h) | h
    any_goals simp_all
    split at h
    · exact .inl (.inr (List.mem_filter.mp h).1)
    · split at h
      · exact .inl (.inr h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr rfl
        · exact .inl (.inr h)
  | registerChannel => exact .inl hq
  | requestPermission id ch =>
    simp only [core] at hq
    split at hq
    · exact .inl hq
    · simp only [ports, List.mem_append, List.mem_map, List.mem_cons] at hq ⊢
      rcases hq with ((((h | h) | ⟨x, hx | hx, rfl⟩) | h) | h) | h
      · exact .inl (.inl (.inl (.inl (.inl (.inl h)))))
      · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
      · exact .inr (by rw [hx])
      · exact .inl (.inl (.inl (.inl (.inr ⟨x, hx, rfl⟩))))
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  have h := (cleanup_removes_all s.ns p).1
  simp only [drop] at h ⊢
  cases hm : mentions _ p
  · rfl
  · rw [mentions_iff] at hm
    simp only [ports, List.mem_append, List.mem_map, List.mem_filter] at hm
    rcases hm with ((((⟨n, hn, hno⟩ | h) | ⟨x, hx, hxp⟩) | ⟨x, hx, hxp⟩) | h) | h
    · exact absurd hno (h n hn)
    all_goals simp_all

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  rw [mentions_iff] at h ⊢
  simp only [drop, cleanup, ports, List.mem_append, List.mem_map, List.mem_filter] at h ⊢
  rcases h with ((((⟨n, hn, rfl⟩ | h) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) | h) | h
  · exact .inl (.inl (.inl (.inl (.inl ⟨n, hn.1, rfl⟩))))
  · exact .inl (.inl (.inl (.inl (.inr h.1))))
  · exact .inl (.inl (.inl (.inr ⟨x, hx.1, rfl⟩)))
  · exact .inl (.inl (.inr ⟨x, hx.1, rfl⟩))
  · exact .inl (.inr h.1)
  · exact .inr h.1

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  rw [mentions_iff] at hm ⊢
  simp only [handle] at hm
  rcases core_ports w cx _ r q hm with hq | hq
  · rcases pushControls_ports s cx.port q hq with hq | hq
    · exact .inl hq
    · exact .inr ⟨cx, hcx, hq.symm⟩
  · exact .inr ⟨cx, hcx, hq.symm⟩

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  rw [mentions_iff] at hm ⊢
  simp only [onReply] at hm
  split at hm
  · exact hm
  · rename_i pd hpd
    have hmem := List.mem_of_find?_eq_some hpd
    simp only [ports, List.mem_append, List.mem_map, List.mem_filter] at hm ⊢
    rcases hm with ((((h | h) | ⟨x, hx, rfl⟩) | h) | h) | h
    · exact .inl (.inl (.inl (.inl (.inl h))))
    · have key : ∀ c : Bool, q ∈ (if c = true then pd.port :: s.granted else s.granted) →
          q = pd.port ∨ q ∈ s.granted := by
        intro c hc
        split at hc
        · exact List.mem_cons.mp hc
        · exact .inr hc
      rcases key _ h with rfl | h
      · exact .inl (.inl (.inl (.inr ⟨pd, hmem, rfl⟩)))
      · exact .inl (.inl (.inl (.inl (.inr h))))
    · exact .inl (.inl (.inl (.inr ⟨x, hx.1, rfl⟩)))
    · exact .inl (.inl (.inr h))
    · exact .inl (.inr h)
    · exact .inr h

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  rw [mentions_iff] at hm ⊢
  match e with
  | .userChanged _ => exact hm
  | .themeChanged _ => exact hm
  | .nap d ev args =>
    simp only [onEvent] at hm
    split at hm
    · split at hm <;> exact hm
    · split at hm
      · split at hm <;> exact hm
      · exact hm
    · split at hm
      · simp only [ports, List.mem_append, List.mem_map, List.mem_filter] at hm ⊢
        rcases hm with ((((⟨n, hn, rfl⟩ | h) | h) | h) | h) | h
        · exact .inl (.inl (.inl (.inl (.inl ⟨n, hn.1, rfl⟩))))
        all_goals simp_all
      · exact hm
    · exact hm

/-! ### Properties: NAP-NOTIFY guarantees at the component level -/

/-- Every rendered notification is attributed to the requesting endpoint, has a
sanitised title and body, at most three actions, and exists only because the
endpoint has permission and is under the rate limit (`NapNotify.send_render`). -/
theorem show_safe (h : Host) (w : World) (cx : Ctx) (s : St) (id : String) (p : Payload) (a : Json)
    (he : Eff.effect (.nap .notify "show" a) ∈ (handle h w cx s (.send id p)).2) :
    ∃ n, a = showArgs cx p n ∧ n.owner = cx.port ∧ n.title = s.cfg.sanitize p.title ∧
      n.body = p.body.map s.cfg.sanitize ∧ n.actions.length ≤ 3 ∧
      permitted s cx.port = true ∧ limited s w.now cx.port (p.priority.getD .normal) = false := by
  simp only [handle, core, List.mem_append] at he
  rcases he with he | he
  · simp only [pushControls] at he; split at he <;> simp at he
  · simp only [List.mem_map] at he
    obtain ⟨o, ho, he⟩ := he
    cases o with
    | render n =>
      simp only [encodeOut, Eff.effect.injEq, Effect.nap.injEq, true_and] at he
      have := NapNotify.send_render ho
      have hc : ∀ s', pushControls s cx.port = s' → s'.1.cfg = s.cfg ∧ s'.1.granted = s.granted ∧
          s'.1.recent = s.recent := by
        intro s' hs; subst hs; unfold pushControls; split <;> exact ⟨rfl, rfl, rfl⟩
      obtain ⟨h1, h2, h3⟩ := hc _ rfl
      simp only [env, permitted, limited, recentCount, h1, h2, h3, toModel] at this ⊢
      exact ⟨n, he.symm, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩
    | hide => simp [encodeOut] at he
    | sendResult => simp [encodeOut] at he

/-- Every message a `notify.send` produces goes back to the requester. -/
theorem send_replies_to_requester (h : Host) (w : World) (cx : Ctx) (s : St) (id : String)
    (p : Payload) (q : PortId) (m : Json)
    (hm : Eff.send q m ∈ (handle h w cx s (.send id p)).2) : q = cx.port := by
  simp only [handle, core, List.mem_append] at hm
  rcases hm with hm | hm
  · simp only [pushControls] at hm; split at hm <;> simp_all
  · simp only [List.mem_map] at hm
    obtain ⟨o, ho, he⟩ := hm
    cases o with
    | render => simp [encodeOut] at he
    | hide => simp [encodeOut] at he
    | sendResult to =>
      simp only [encodeOut, Eff.send.injEq] at he
      unfold NapNotify.send at ho
      split at ho
      · simp at ho; exact he.1.symm.trans ho.1
      · split at ho
        · simp at ho; exact he.1.symm.trans ho.1
        · simp at ho; exact he.1.symm.trans ho.1

/-- A refused `notify.send` creates nothing (`NapNotify.send_error_creates_nothing`):
when no notification is rendered, the set of notifications is unchanged. -/
theorem send_refused_creates_nothing (h : Host) (w : World) (cx : Ctx) (s : St) (id : String)
    (p : Payload) (hn : ∀ a, Eff.effect (.nap .notify "show" a) ∉ (handle h w cx s (.send id p)).2) :
    (handle h w cx s (.send id p)).1.ns = s.ns := by
  have hc : (pushControls s cx.port).1.ns = s.ns := by unfold pushControls; split <;> rfl
  simp only [handle, core] at hn ⊢
  rw [← hc]
  generalize (pushControls s cx.port).1 = s1 at hn ⊢
  generalize hr : NapNotify.send (env s1 w.now) s1.ns cx.port id (toModel p) = res at hn ⊢
  obtain ⟨ns', outs⟩ := res
  simp only
  unfold NapNotify.send at hr
  split at hr
  · simp at hr; exact hr.1.symm
  · split at hr
    · simp at hr; exact hr.1.symm
    · simp only [Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact absurd (List.mem_append_right _ (List.mem_cons_self ..)) (hn _)

/-- A napplet hides only its own notifications; an unknown or foreign id is
silently ignored (`NapNotify.dismiss_only_own`). -/
theorem dismiss_only_own (h : Host) (w : World) (cx : Ctx) (s : St) (str : String) (a : Json)
    (he : Eff.effect (.nap .notify "hide" a) ∈ (handle h w cx s (.dismiss str)).2) :
    ∃ n ∈ s.ns.shown, n.owner = cx.port ∧ a = hideArgs n.nid := by
  have hc : (pushControls s cx.port).1.ns = s.ns := by unfold pushControls; split <;> rfl
  simp only [handle, List.mem_append] at he
  rcases he with he | he
  · simp only [pushControls] at he; split at he <;> simp at he
  · rw [← hc]
    generalize (pushControls s cx.port).1 = s1 at he ⊢
    simp only [core] at he
    split at he
    · simp at he
    · rename_i n _
      simp only [List.mem_map] at he
      obtain ⟨o, ho, he⟩ := he
      have hne : (NapNotify.dismiss s1.ns cx.port n.nid).2 ≠ [] := List.ne_nil_of_mem ho
      obtain ⟨m, hm, hmn, hmo⟩ := NapNotify.dismiss_only_own hne
      unfold NapNotify.dismiss at ho
      split at ho
      · simp only [List.mem_singleton] at ho; subst ho
        simp only [encodeOut, Eff.effect.injEq, Effect.nap.injEq, true_and] at he
        exact ⟨m, hm, hmo, by rw [hmn]; exact he.symm⟩
      · simp at ho

/-- User interaction reaches only the endpoint that owns the notification. -/
theorem event_to_owner (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId) (m : Json)
    (hm : Eff.send q m ∈ (onEvent h w s e).2) : ∃ n ∈ s.ns.shown, n.owner = q := by
  match e with
  | .userChanged _ => simp [onEvent] at hm
  | .themeChanged _ => simp [onEvent] at hm
  | .nap d ev args =>
    simp only [onEvent] at hm
    split at hm
    · split at hm
      · rename_i n hn
        simp only [Option.bind_eq_some_iff] at hn
        obtain ⟨_, -, hn⟩ := hn
        simp only [List.mem_singleton, Eff.send.injEq] at hm
        exact ⟨n, List.mem_of_find?_eq_some hn, hm.1.symm⟩
      · simp at hm
    · split at hm
      · rename_i n _ hn _
        simp only [Option.bind_eq_some_iff] at hn
        obtain ⟨_, -, hn⟩ := hn
        split at hm
        · simp only [List.mem_singleton, Eff.send.injEq] at hm
          exact ⟨n, List.mem_of_find?_eq_some hn, hm.1.symm⟩
        · simp at hm
      · simp at hm
    · split at hm
      · rename_i n hn
        simp only [Option.bind_eq_some_iff] at hn
        obtain ⟨_, -, hn⟩ := hn
        simp only [List.mem_singleton, Eff.send.injEq] at hm
        exact ⟨n, List.mem_of_find?_eq_some hn, hm.1.symm⟩
      · simp at hm
    · simp at hm

/-- Teardown hides every notification of the endpoint and no other
(`NapNotify.cleanup_removes_all`). -/
theorem drop_cleanup (s : St) (p : PortId) :
    (∀ n ∈ (drop s p).1.ns.shown, n.owner ≠ p) ∧
    (∀ n ∈ s.ns.shown, n.owner ≠ p → n ∈ (drop s p).1.ns.shown) :=
  cleanup_removes_all s.ns p

/-! ### Vectors (upstream examples) -/

def sampleCtx : Ctx :=
  { port := 7, window := 1, identity := { dTag := some "app", artifactHash := "h" },
    exposed := [.notify], inst := 0 }

def sampleWorld : World := { now := 100, live := [sampleCtx], user := "" }

def sampleHost : Host :=
  { crypto := { sha256 := fun _ => "", verifySig := fun _ => false }, verifyEvent := fun _ => false,
    sniff := fun _ => "application/octet-stream", rasterize := fun _ => none,
    looksCiphertext := fun _ => false, encryptedWith := fun _ => none, transform := id }

/-- An endpoint that already has permission and has seen `notify.controls`, with
the next notification numbered 42. -/
def sampleSt : St := { St.init with ns := ⟨[], 42⟩, granted := [7], controlsSent := [7] }

def sentJson : List Eff → List Json
  | [] => []
  | .send _ m :: es => m :: sentJson es
  | _ :: es => sentJson es

def step (s : St) (j : Json) : St × List Eff :=
  match decode j with
  | .ok r => handle sampleHost sampleWorld sampleCtx s r
  | .reject rs => (s, rs.map (.send sampleCtx.port))
  | .unknown => (s, [])

def send1 : Json := Json.parse! "{ \"type\": \"notify.send\", \"id\": \"n1\", \"title\": \"New message\", \"body\": \"Alice: hey!\", \"priority\": \"normal\" }"
def send1Res : Json := Json.parse! "{ \"type\": \"notify.send.result\", \"id\": \"n1\", \"notificationId\": \"shell-42\" }"
def send2 : Json := Json.parse! "{ \"type\": \"notify.send\", \"id\": \"n2\", \"title\": \"Incoming call\", \"priority\": \"urgent\", \"actions\": [{ \"id\": \"answer\", \"label\": \"Answer\" }, { \"id\": \"decline\", \"label\": \"Decline\" }] }"
def send2Res : Json := Json.parse! "{ \"type\": \"notify.send.result\", \"id\": \"n2\", \"notificationId\": \"shell-43\" }"
def send3 : Json := Json.parse! "{ \"type\": \"notify.send\", \"id\": \"n3\", \"title\": \"Hi\" }"
def send3Res : Json := Json.parse! "{ \"type\": \"notify.send.result\", \"id\": \"n3\", \"error\": \"permission denied\" }"
def actionEv : Json := Json.parse! "{ \"notificationId\": \"shell-43\", \"actionId\": \"answer\" }"
def actionPush : Json := Json.parse! "{ \"type\": \"notify.action\", \"notificationId\": \"shell-43\", \"actionId\": \"answer\" }"
def clickedPush : Json := Json.parse! "{ \"type\": \"notify.clicked\", \"notificationId\": \"shell-42\" }"
def dismissedPush : Json := Json.parse! "{ \"type\": \"notify.dismissed\", \"notificationId\": \"shell-42\", \"reason\": \"timeout\" }"
def badgeReq : Json := Json.parse! "{ \"type\": \"notify.badge\", \"count\": 3 }"
def badgeClear : Json := Json.parse! "{ \"type\": \"notify.badge\", \"count\": 0 }"
def channelReq : Json := Json.parse! "{ \"type\": \"notify.channel.register\", \"channelId\": \"messages\", \"label\": \"Messages\", \"description\": \"Direct messages and mentions\", \"defaultPriority\": \"normal\" }"
def permReq : Json := Json.parse! "{ \"type\": \"notify.permission.request\", \"id\": \"p1\", \"channel\": \"messages\" }"
def permRes : Json := Json.parse! "{ \"type\": \"notify.permission.result\", \"id\": \"p1\", \"granted\": true }"
def dismissReq : Json := Json.parse! "{ \"type\": \"notify.dismiss\", \"notificationId\": \"shell-42\" }"
def controlsPush : Json := Json.parse! "{ \"type\": \"notify.controls\", \"controls\": [\"toasts\", \"badges\", \"actions\", \"channels\"] }"

def sA : St := (step sampleSt send1).1
def sB : St := (step sA send2).1

#guard decode send1 matches .ok (.send "n1" ⟨"New message", some "Alice: hey!", none, none, none, some .normal⟩)
#guard decode send2 matches .ok (.send "n2" ⟨"Incoming call", none, none,
  some [⟨"answer", "Answer"⟩, ⟨"decline", "Decline"⟩], none, some .urgent⟩)
#guard decode badgeReq matches .ok (.badge 3)
#guard decode badgeClear matches .ok (.badge 0)
#guard decode channelReq matches .ok (.registerChannel ⟨"messages", "Messages", some "Direct messages and mentions", some .normal⟩)
#guard decode permReq matches .ok (.requestPermission "p1" (some "messages"))
#guard decode dismissReq matches .ok (.dismiss "shell-42")
#guard decode (Json.parse! "{ \"type\": \"notify.registerChannel\", \"channelId\": \"x\", \"label\": \"X\" }") matches .unknown
#guard match sentJson (step sampleSt send1).2 with | [m] => Json.same m send1Res | _ => false
#guard match sentJson (step sA send2).2 with | [m] => Json.same m send2Res | _ => false
#guard (step sA send2).2.length == 2
-- No permission yet: refused, and the first message on the endpoint is preceded by `notify.controls`.
#guard match sentJson (step St.init send3).2 with
  | [c, m] => Json.same c controlsPush && Json.same m send3Res | _ => false
#guard match (onEvent sampleHost sampleWorld sB (.nap .notify "action" actionEv)).2 with
  | [.send 7 m] => Json.same m actionPush | _ => false
#guard match (onEvent sampleHost sampleWorld sB (.nap .notify "action" (Json.parse! "{ \"notificationId\": \"shell-43\", \"actionId\": \"steal\" }"))).2 with
  | [] => true | _ => false
#guard match (onEvent sampleHost sampleWorld sB (.nap .notify "clicked" (Json.parse! "{ \"notificationId\": \"shell-42\" }"))).2 with
  | [.send 7 m] => Json.same m clickedPush | _ => false
#guard match (onEvent sampleHost sampleWorld sB (.nap .notify "dismissed" (Json.parse! "{ \"notificationId\": \"shell-42\", \"reason\": \"timeout\" }"))).2 with
  | [.send 7 m] => Json.same m dismissedPush | _ => false
#guard match (step sB dismissReq).2 with
  | [.effect (.nap .notify "hide" a)] => Json.same a (Json.parse! "{ \"notificationId\": \"shell-42\" }") | _ => false
-- Another endpoint cannot dismiss it.
#guard (handle sampleHost sampleWorld { sampleCtx with port := 8 } { sB with controlsSent := [8, 7] } (.dismiss "shell-42")).2 == []
#guard match (step sampleSt badgeReq).2 with
  | [.effect (.nap .notify "badge" a)] => Json.same a (Json.parse! "{ \"port\": 7, \"count\": 3 }") | _ => false
#guard (step sampleSt channelReq).2.length == 1
-- Permission: already granted, answered at once.
#guard match (step sampleSt permReq).2 with | [.send 7 m] => Json.same m permRes | _ => false
-- Not yet granted: prompt, then the user's decision.
#guard match (step { St.init with controlsSent := [7] } permReq) with
  | (s', [.call ⟨.notify, 0⟩ (.prompt .notify "permission" _)]) =>
    match onReply sampleHost sampleWorld s' 0 (.decision true none) with
    | (s'', [.send 7 m]) => Json.same m permRes && s''.granted == [7]
    | _ => false
  | _ => false
-- Teardown hides both notifications.
#guard (drop sB 7).2.length == 2
#guard mentions (drop sB 7).1 7 == false

end Napplet.Run.Notify
