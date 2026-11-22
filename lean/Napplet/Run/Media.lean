/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Media

/-!
# NAP-MEDIA runtime component

Upstream: `napplet/naps` PR #10, `naps/NAP-MEDIA.md` at `7806f438`.

Wire (napplet → shell): `media.session.create {id, owner, sessionId?, source?, metadata?,
context?, capabilities?, autoplay?, live?}`, `media.session.update {sessionId, metadata}`,
`media.session.destroy {sessionId}`, `media.state {sessionId, status, position?, duration?,
volume?, reason?}` (napplet-owned sessions), `media.capabilities {sessionId, actions}`
(napplet-owned sessions), `media.command {sessionId, action, value?, reason?}` (shell-owned
sessions).

Wire (shell → napplet): `media.session.create.result {id, sessionId, owner}` or
`{id, error}`, `media.session.ended {sessionId, reason}`, `media.state` and
`media.capabilities` (shell-owned sessions), `media.command` (napplet-owned sessions),
`media.controls {sessionId, controls}` (either owner).

The session registry is `NapMedia.MediaState` (numeric ids, owner, endpoint, status,
focus-pause flag), so `NapMedia.Inv` and the NAP's retirement and focus results apply to
the component directly. Each numeric id has one canonical wire id (`Info.sid`), kept for
the whole runtime session, so a canonical id is never issued twice (not even to a
replacement endpoint).

Canonical ids: the napplet's preferred `sessionId` is used when it is non-empty, has
never been issued, and does not start with the shell's reserved prefix `shell-`;
otherwise the shell issues `shell-<n>`.

Malformed requests: `media.session.create` with a string `id` but a missing or unknown
`owner`, or a non-boolean `autoplay`/`live`, or a bad `capabilities` list, gets
`media.session.create.result {id, error: "invalid request"}`; a non-string `sessionId`
hint gets `error: "invalid session ID"` (the NAP's error string for it). Without a
string `id` nothing is sent. The other requests are fire-and-forget: malformed ones are
dropped. Unknown `MediaAction` strings in a `capabilities`/`actions` list are dropped
(forward compatibility); an unknown `action` in `media.command` makes the command
malformed. Messages naming an unknown, retired or foreign `sessionId` are silently
ignored, as are messages that are not valid for the session's owner mode.
-/

/-! ## Host operations

All are in domain `media`. `sessionId` is always the canonical id; `window` is the
endpoint's `WindowId` (JSON number). Numbers are JSON numbers. A `MediaState` object is
`{status, position?, duration?, volume?, reason?}` as in NAP-MEDIA.

Effects (`Effect.nap .media op args`, fire-and-forget):

* `open {sessionId, window, source, metadata?, context?, autoplay?, live?}`: start a
  **shell-owned** session. The host resolves `source` (`MediaSourceRef`: `url`,
  `blossomHash` per BUD-10 from servers it chooses, `nostr` event/address one NIP-19 hop)
  and fetches the bytes under the NAP-RESOURCE policy (private-address block at DNS
  resolution, MIME byte sniffing); it never gives the bytes to the napplet. It shows the
  session on its media surface with `metadata`; artwork is fetched only through that same
  policy. It starts output only if `autoplay` is `true` and its autoplay and audio-focus
  policy allow it. It then reports through the `state` and `capabilities` events below;
  if the source cannot be played it stops and sends `retire` with reason `error`.
* `register {sessionId, window, metadata?, context?, capabilities}`: show a
  **napplet-owned** session on the media surface (metadata, media keys, OS integration).
  No source is passed; the host MUST NOT fetch or play anything for it.
  For both, `context` (`MediaSessionContext`) is display data only: the host ignores
  link relations it does not know, treats a link without `nostr.relays` as valid,
  SHOULD validate Nostr references before using them, and never takes fetch authority
  or ownership from it.
* `update {sessionId, metadata}`: merge `metadata` (a partial `MediaMetadata`) into the
  displayed metadata; only the given fields change.
* `state {sessionId, status, position?, duration?, volume?, reason?}`: a napplet-owned
  session's reported state, for display (out-of-range numbers already removed).
* `capabilities {sessionId, actions}`: a napplet-owned session's supported actions; the
  host enables only these controls for it.
* `command {sessionId, action, value?, reason}`: perform `action` on a **shell-owned**
  session's backend (`value`: seek position in seconds, or volume 0–1). The runtime has
  checked that the action was exposed and its value is in range; the backend still
  applies its policy (it MAY ignore `seek` on live sources and `next`/`prev` without a
  queue) and reports the outcome through the `state` event. With reason `focus-lost` or
  `focus-gained` it is the runtime's audio-focus decision; the runtime has already sent
  the corresponding `media.state`, so the host need not report that transition again.
* `close {sessionId, reason}`: stop the session's output and remove it from the media
  surface, before the runtime sends `media.session.ended` (shell-owned: stop and release
  the backend; napplet-owned: revoke the frame's output authority, for example by muting
  it, when `reason` is `policy`). Sent on destroy (`destroyed`), on focus loss of a
  napplet-owned session that cannot pause (`policy`) and on endpoint teardown
  (`destroyed`, with no `ended`). This model does not promote sessions to persistent
  playback; teardown always stops shell-owned output.

Events (`HostEvent.nap .media ev args`):

* `state {sessionId, status, position?, duration?, volume?, reason?}`: a **shell-owned**
  backend's state change (buffering, position, natural end as `stopped`/`ended`, user
  action in the shell's own player as reason `user`, failure as `error`). Forwarded as
  `media.state`. Ignored for napplet-owned sessions.
* `capabilities {sessionId, actions}`: a shell-owned backend's supported actions;
  forwarded as `media.capabilities`.
* `controls {sessionId, controls}`: the shell's control list for a session; forwarded as
  `media.controls`.
* `command {sessionId, action, value?, reason?}`: the user used a shell control on a
  **napplet-owned** session. Forwarded as `media.command` only if the action is in the
  session's current capabilities and `seek`/`volume` carry a valid `value`.
* `focusLost {sessionId}`, `focusGained {sessionId}`: the host's audio-focus decision for
  one session (NAP-MEDIA §Temporary audio-focus loss). The runtime decides what is sent.
* `retire {sessionId, reason}`: the host has already stopped the session's output and
  retires it (`preempted`, `ended`, `error`, `backend-exited`, `user`, `policy`; an
  unknown reason is treated as `policy`). The runtime sends the one `media.session.ended`.
  When the host retires a session because its source completed, `retire` with reason
  `ended` is the sole notification of that completion: it MUST NOT also send a `state`
  event with reason `ended` for it.

Events naming an unknown or retired `sessionId` are ignored.
-/

namespace Napplet.Run.Media

open NapMedia

/-! ### Names -/

def ownerName : Owner → String
  | .shell => "shell" | .napplet => "napplet"

def ownerOf? : String → Option Owner
  | "shell" => some .shell | "napplet" => some .napplet | _ => none

def statusName : Status → String
  | .playing => "playing" | .paused => "paused" | .stopped => "stopped" | .buffering => "buffering"

def statusOf? : String → Option Status
  | "playing" => some .playing | "paused" => some .paused | "stopped" => some .stopped
  | "buffering" => some .buffering | _ => none

def actionName : Action → String
  | .play => "play" | .pause => "pause" | .stop => "stop" | .next => "next" | .prev => "prev"
  | .seek => "seek" | .volume => "volume"

def actionOf? : String → Option Action
  | "play" => some .play | "pause" => some .pause | "stop" => some .stop | "next" => some .next
  | "prev" => some .prev | "seek" => some .seek | "volume" => some .volume | _ => none

def reasonName : Reason → String
  | .user => "user" | .ended => "ended" | .error => "error" | .preempted => "preempted"
  | .focusLost => "focus-lost" | .focusGained => "focus-gained" | .destroyed => "destroyed"
  | .backendExited => "backend-exited" | .policy => "policy"

def reasonOf? : String → Option Reason
  | "user" => some .user | "ended" => some .ended | "error" => some .error
  | "preempted" => some .preempted | "focus-lost" => some .focusLost
  | "focus-gained" => some .focusGained | "destroyed" => some .destroyed
  | "backend-exited" => some .backendExited | "policy" => some .policy | _ => none

@[simp] theorem ownerOf?_name (o : Owner) : ownerOf? (ownerName o) = some o := by cases o <;> rfl
@[simp] theorem statusOf?_name (s : Status) : statusOf? (statusName s) = some s := by cases s <;> rfl
@[simp] theorem actionOf?_name (a : Action) : actionOf? (actionName a) = some a := by cases a <;> rfl
@[simp] theorem reasonOf?_name (r : Reason) : reasonOf? (reasonName r) = some r := by cases r <;> rfl

def allActions : List Action := [.play, .pause, .stop, .next, .prev, .seek, .volume]

/-! ### JSON helpers -/

/-- An optional member: absent is `some none`, present and well-typed is `some (some x)`,
present and ill-typed is `none`. -/
def optOf {α : Type} (o : Option Json) (f : Json → Option α) : Option (Option α) :=
  match o with
  | none => some none
  | some v => (f v).map some

def numOf? : Json → Option Num
  | .num n => some n
  | _ => none

/-- A list of `MediaAction` strings; unknown strings are dropped. -/
def actionsOf? (j : Json) : Option (List Action) :=
  (j.asStrs?).map (·.filterMap actionOf?)

def actionsJson (as : List Action) : Json := Json.strs (as.map actionName)

theorem get_mkObj_cons (k k' : String) (o : Option Json) (rest : List (String × Option Json)) :
    (Json.mkObj ((k', o) :: rest)).get? k = ((Json.mkObj rest).get? k).or (if k' = k then o else none) := by
  cases o with
  | none => simp [Json.mkObj, Json.get?]
  | some v =>
    simp only [Json.mkObj, Json.get?, List.filterMap_cons, Option.map_some, Json.lookup]
    split <;> simp_all

theorem get_mkObj_nil (k : String) : (Json.mkObj []).get? k = none := rfl

theorem optOf_map {α : Type} (o : Option α) (g : α → Json) (f : Json → Option α)
    (h : ∀ x, f (g x) = some x) : optOf (o.map g) f = some o := by
  cases o <;> simp [optOf, h]

@[simp] theorem numOf?_num (n : Num) : numOf? (.num n) = some n := rfl

theorem filterMap_actionOf? (as : List Action) : (as.map actionName).filterMap actionOf? = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa using ih

@[simp] theorem actionsOf?_json (as : List Action) : actionsOf? (actionsJson as) = some as := by
  simp only [actionsOf?, actionsJson, Json.asStrs?_strs, Option.map_some, filterMap_actionOf?]

@[simp] theorem optOf_str (o : Option String) : optOf (o.map .str) Json.asStr? = some o :=
  optOf_map _ _ _ fun _ => rfl
@[simp] theorem optOf_num (o : Option Num) : optOf (o.map .num) numOf? = some o :=
  optOf_map _ _ _ fun _ => rfl
@[simp] theorem optOf_bool (o : Option Bool) : optOf (o.map .bool) Json.asBool? = some o :=
  optOf_map _ _ _ fun _ => rfl
@[simp] theorem optOf_actions (o : Option (List Action)) :
    optOf (o.map actionsJson) actionsOf? = some o :=
  optOf_map _ _ _ actionsOf?_json

/-! ### Typed payloads -/

/-- `MediaState` as carried by `media.state`. `reason` is kept as text: an unrecognised
reason is an unspecified cause, never an error. -/
structure MState where
  status : Status
  position : Option Num := none
  duration : Option Num := none
  volume : Option Num := none
  reason : Option String := none
  deriving DecidableEq, Repr

/-- `MediaCommand` as carried by `media.command`. -/
structure MCommand where
  action : Action
  value : Option Num := none
  reason : Option String := none
  deriving DecidableEq, Repr

/-- `MediaSessionCreate` plus the correlation `id`. `source`, `metadata` and `context`
are carried as JSON. -/
structure Create where
  id : String
  owner : Owner
  hint : Option String := none
  source : Option Json := none
  metadata : Option Json := none
  context : Option Json := none
  capabilities : Option (List Action) := none
  autoplay : Option Bool := none
  live : Option Bool := none
  deriving DecidableEq, Repr

inductive Req where
  | create (c : Create)
  | update (sid : String) (metadata : Json)
  | destroy (sid : String)
  | state (sid : String) (st : MState)
  | capabilities (sid : String) (actions : List Action)
  | command (sid : String) (cmd : MCommand)
  deriving DecidableEq, Repr

def Req.sid? : Req → Option String
  | .create _ => none
  | .update w _ | .destroy w | .state w _ | .capabilities w _ | .command w _ => some w

/-! ### Codec -/

def stateOf? (j : Json) : Option MState := do
  let status ← (j.getStr? "status").bind statusOf?
  let position ← optOf (j.get? "position") numOf?
  let duration ← optOf (j.get? "duration") numOf?
  let volume ← optOf (j.get? "volume") numOf?
  let reason ← optOf (j.get? "reason") Json.asStr?
  some { status, position, duration, volume, reason }

def commandOf? (j : Json) : Option MCommand := do
  let action ← (j.getStr? "action").bind actionOf?
  let value ← optOf (j.get? "value") numOf?
  let reason ← optOf (j.get? "reason") Json.asStr?
  some { action, value, reason }

def stateFields (st : MState) : List (String × Option Json) :=
  [("status", some (.str (statusName st.status))), ("position", st.position.map .num),
   ("duration", st.duration.map .num), ("volume", st.volume.map .num),
   ("reason", st.reason.map .str)]

def commandFields (c : MCommand) : List (String × Option Json) :=
  [("action", some (.str (actionName c.action))), ("value", c.value.map .num),
   ("reason", c.reason.map .str)]

def decodeCreate (j : Json) : Decoded Req :=
  match reqId? j with
  | none => .reject []
  | some id =>
    match (j.getStr? "owner").bind ownerOf? with
    | none => .reject (errorReply "media.session.create.result" j "invalid request")
    | some owner =>
      match optOf (j.get? "sessionId") Json.asStr? with
      | none => .reject (errorReply "media.session.create.result" j "invalid session ID")
      | some hint =>
        match optOf (j.get? "capabilities") actionsOf?, optOf (j.get? "autoplay") Json.asBool?,
            optOf (j.get? "live") Json.asBool? with
        | some capabilities, some autoplay, some live =>
          .ok (.create { id, owner, hint, source := j.get? "source", metadata := j.get? "metadata",
                         context := j.get? "context", capabilities, autoplay, live })
        | _, _, _ => .reject (errorReply "media.session.create.result" j "invalid request")

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some "media.session.create" => decodeCreate j
  | some "media.session.update" =>
    match j.getStr? "sessionId", j.get? "metadata" with
    | some w, some m => .ok (.update w m)
    | _, _ => .reject []
  | some "media.session.destroy" =>
    match j.getStr? "sessionId" with
    | some w => .ok (.destroy w)
    | none => .reject []
  | some "media.state" =>
    match j.getStr? "sessionId", stateOf? j with
    | some w, some st => .ok (.state w st)
    | _, _ => .reject []
  | some "media.capabilities" =>
    match j.getStr? "sessionId", (j.get? "actions").bind actionsOf? with
    | some w, some as => .ok (.capabilities w as)
    | _, _ => .reject []
  | some "media.command" =>
    match j.getStr? "sessionId", commandOf? j with
    | some w, some c => .ok (.command w c)
    | _, _ => .reject []
  | _ => .unknown

def encodeReq : Req → Json
  | .create c => Json.msg "media.session.create"
      [("id", some (.str c.id)), ("owner", some (.str (ownerName c.owner))),
       ("sessionId", c.hint.map .str), ("source", c.source), ("metadata", c.metadata),
       ("context", c.context), ("capabilities", c.capabilities.map actionsJson),
       ("autoplay", c.autoplay.map .bool), ("live", c.live.map .bool)]
  | .update w m => Json.msg "media.session.update" [("sessionId", some (.str w)), ("metadata", some m)]
  | .destroy w => Json.msg "media.session.destroy" [("sessionId", some (.str w))]
  | .state w st => Json.msg "media.state" (("sessionId", some (.str w)) :: stateFields st)
  | .capabilities w as => Json.msg "media.capabilities"
      [("sessionId", some (.str w)), ("actions", some (actionsJson as))]
  | .command w c => Json.msg "media.command" (("sessionId", some (.str w)) :: commandFields c)

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r with
  | create c =>
    obtain ⟨id, owner, hint, source, metadata, context, caps, ap, lv⟩ := c
    simp only [decode, decodeCreate, encodeReq, reqId?, Json.getStr?, Json.msg, get_mkObj_cons,
      get_mkObj_nil]
    simp [optOf_map]
  | update w m =>
    simp only [decode, encodeReq, Json.getStr?, Json.msg, get_mkObj_cons, get_mkObj_nil]
    simp
  | destroy w =>
    simp only [decode, encodeReq, Json.getStr?, Json.msg, get_mkObj_cons, get_mkObj_nil]
    simp
  | state w st =>
    obtain ⟨status, pos, dur, vol, reason⟩ := st
    simp only [decode, encodeReq, stateOf?, stateFields, Json.getStr?, Json.msg, get_mkObj_cons,
      get_mkObj_nil]
    simp
  | capabilities w as =>
    simp only [decode, encodeReq, Json.getStr?, Json.msg, get_mkObj_cons, get_mkObj_nil]
    simp
  | command w c =>
    obtain ⟨a, v, reason⟩ := c
    simp only [decode, encodeReq, commandOf?, commandFields, Json.getStr?, Json.msg,
      get_mkObj_cons, get_mkObj_nil]
    simp


/-! ### Component state -/

/-- Shell media policy. Defaults follow the kehto reference service (16 sessions per
endpoint, shell playback available, every source form and every control supported). -/
structure Cfg where
  /-- Concurrent sessions per endpoint (`"session limit exceeded"`). -/
  maxSessions : Nat := 16
  /-- Whether the shell offers shell-owned playback (`"unsupported owner mode"`). -/
  shellPlayback : Bool := true
  /-- Whether `autoplay: true` is permitted on creation (`"autoplay denied"`). -/
  autoplay : Bool := true
  /-- `MediaSourceRef` forms the shell plays (`"unsupported source"`). -/
  sourceForms : List String := ["url", "blossomHash", "nostr"]
  /-- Static source policy (`"source blocked"`); network-level blocking is the host's
  `open` contract. -/
  blockSource : Json → Bool := fun _ => false
  /-- The shell's control list, pushed as `media.controls` after creation. -/
  controls : List Action := allActions

/-- Per-session wire data, kept for the whole runtime session so canonical ids are
never reissued. Holds no port. -/
structure Info where
  n : Nat
  sid : String
  /-- Current owner-declared capabilities (`media.capabilities`). -/
  actions : List Action
  /-- Last `media.controls` list sent. -/
  controls : List Action
  deriving DecidableEq, Repr

structure St where
  core : MediaState
  info : List Info
  cfg : Cfg

def St.init (cfg : Cfg := {}) : St := ⟨⟨[], [], 0⟩, [], cfg⟩

/-- Canonical ids ever issued. -/
def used (s : St) : List String := s.info.map (·.sid)

def infoOf (s : St) (w : String) : Option Info := s.info.find? (·.sid == w)

/-- The live session with canonical id `w`. Retired and unknown ids give `none`. -/
def lookup (s : St) (w : String) : Option (Info × Session) :=
  match infoOf s w with
  | none => none
  | some i => (find s.core i.n).map (i, ·)

/-- The live session `w`, if endpoint `p` owns it. -/
def owned (s : St) (p : PortId) (w : String) : Option (Info × Session) :=
  match lookup s w with
  | some (i, x) => if x.endpoint = p then some (i, x) else none
  | none => none

def setInfo (s : St) (n : Nat) (f : Info → Info) : St :=
  { s with info := s.info.map fun i => if i.n = n then f i else i }

/-! ### Messages -/

def sidField (w : String) : String × Option Json := ("sessionId", some (.str w))

def createOk (id w : String) (o : Owner) : Json :=
  Json.msg "media.session.create.result"
    [("id", some (.str id)), sidField w, ("owner", some (.str (ownerName o)))]

/-- A rejected create. `sessionId` is "Required on successful creation" and optional
otherwise; the result echoes the napplet's preferred id when it gave one, as in
upstream's "Session creation rejected" example. No session exists. -/
def createErr (id : String) (hint : Option String) (e : String) : Json :=
  Json.msg "media.session.create.result"
    [("id", some (.str id)), ("sessionId", hint.map .str), ("error", some (.str e))]

def endedJson (w : String) (r : Reason) : Json :=
  Json.msg "media.session.ended" [sidField w, ("reason", some (.str (reasonName r)))]

def stateJson (w : String) (st : MState) : Json := Json.msg "media.state" (sidField w :: stateFields st)

def capsJson (w : String) (as : List Action) : Json :=
  Json.msg "media.capabilities" [sidField w, ("actions", some (actionsJson as))]

def commandJson (w : String) (c : MCommand) : Json := Json.msg "media.command" (sidField w :: commandFields c)

def controlsJson (w : String) (as : List Action) : Json :=
  Json.msg "media.controls" [sidField w, ("controls", some (actionsJson as))]

/-- A `media` host instruction. -/
def hostEff (op : String) (args : List (String × Option Json)) : Eff :=
  .effect (.nap .media op (Json.mkObj args))

def closeEff (w : String) (r : Reason) : Eff :=
  hostEff "close" [sidField w, ("reason", some (.str (reasonName r)))]

/-! ### Policy helpers -/

def nonneg (n : Num) : Bool := decide (0 ≤ n.mant)

def unitInterval (n : Num) : Bool := nonneg n && Num.le n ⟨1, 0⟩

/-- Drop out-of-range numbers (negative position/duration, volume outside 0–1). -/
def sanitize (st : MState) : MState :=
  { st with position := st.position.filter nonneg, duration := st.duration.filter nonneg,
            volume := st.volume.filter unitInterval }

/-- NAP-MEDIA §Command Validity: `seek` needs a position, `volume` a value in 0–1. -/
def cmdOk (c : MCommand) : Bool :=
  match c.action with
  | .seek => (c.value.map nonneg).getD false
  | .volume => (c.value.map unitInterval).getD false
  | _ => true

/-- The command as forwarded: `value` only where it means something, and the given
`reason`. A napplet's own `reason` is replaced by `user` (it is never authority); the
host's reason is passed through. -/
def cleanCmd (c : MCommand) (reason : Option String) : MCommand :=
  { c with value := if c.action = .seek ∨ c.action = .volume then c.value else none, reason }

/-- Does a state report keep a focus-induced pause pending? Only a `paused` report with
no reason or reason `focus-lost`; any other status or reason supersedes it. -/
def keepsFocusPause (st : MState) : Bool :=
  st.status = .paused && (st.reason = none || st.reason = some "focus-lost")

/-- Record the owner's reported status. -/
def report (s : St) (x : Session) (st : MState) : St :=
  { s with core := modify s.core x.id st.status (x.pausedByFocus && keepsFocusPause st) }

/-- A user pause or stop supersedes a pending focus pause. -/
def supersede (s : St) (x : Session) : Action → St
  | .pause => { s with core := userPause s.core x.id }
  | .stop => { s with core := modify s.core x.id x.status false }
  | _ => s

def genId (n : Nat) : String := "shell-" ++ toString n

def canonical (s : St) (hint : Option String) : String :=
  match hint with
  | some h => if h ≠ "" ∧ ¬ h.startsWith "shell-" ∧ h ∉ used s then h else genId s.core.next
  | none => genId s.core.next

def sourceSupported (cfg : Cfg) (src : Json) : Bool := cfg.sourceForms.any fun f => (src.get? f).isSome

/-- Creation checks that come before the NAP's own (`missing source`, `autoplay denied`). -/
def precheck (cx : Ctx) (s : St) (c : Create) : Option String :=
  if (s.core.live.filter (·.endpoint == cx.port)).length ≥ s.cfg.maxSessions then
    some "session limit exceeded"
  else if c.owner = .shell then
    if !s.cfg.shellPlayback then some "unsupported owner mode"
    else match c.source with
      | some src =>
        if !sourceSupported s.cfg src then some "unsupported source"
        else if s.cfg.blockSource src then some "source blocked"
        else none
      | none => none
  else none

def openArgs (cx : Ctx) (w : String) (c : Create) : List (String × Option Json) :=
  [sidField w, ("window", some (Json.nat cx.window)), ("source", c.source), ("metadata", c.metadata),
   ("context", c.context), ("autoplay", c.autoplay.map .bool), ("live", c.live.map .bool)]

def registerArgs (cx : Ctx) (w : String) (c : Create) (caps : List Action) : List (String × Option Json) :=
  [sidField w, ("window", some (Json.nat cx.window)), ("metadata", c.metadata),
   ("context", c.context), ("capabilities", some (actionsJson caps))]

def realizeCreate (cx : Ctx) (s : St) (c : Create) (w : String) : MediaOut → List Eff
  | .createResult to id (some _) _ =>
    [.send to (createOk id w c.owner), .send to (controlsJson w s.cfg.controls)]
  | .createResult to id none e => [.send to (createErr id c.hint (e.getD "invalid request"))]
  | .fetchSource _ => [hostEff "open" (openArgs cx w c)]
  | _ => []

def created? : List MediaOut → Option Nat
  | .createResult _ _ (some n) _ :: _ => some n
  | _ => none

def handleCreate (cx : Ctx) (s : St) (c : Create) : St × List Eff :=
  match precheck cx s c with
  | some e => (s, [.send cx.port (createErr c.id c.hint e)])
  | none =>
    let w := canonical s c.hint
    if w ∈ used s then (s, [.send cx.port (createErr c.id c.hint "invalid session ID")])
    else
      let consent := !(c.owner = .shell && c.autoplay = some true && !s.cfg.autoplay)
      let res := NapMedia.create s.core cx.port c.id c.owner c.source.isSome consent
      let effs := res.2.flatMap (realizeCreate cx s c w)
      match created? res.2 with
      | none => (s, effs)
      | some n =>
        let caps := if c.owner = .napplet then c.capabilities.getD [] else []
        ({ s with core := res.1, info := ⟨n, w, caps, s.cfg.controls⟩ :: s.info },
         effs ++ (if c.owner = .napplet then [hostEff "register" (registerArgs cx w c caps)] else []))

/-- Retire a live session: stop output first (when the runtime decides), then exactly
one `media.session.ended` to its endpoint. -/
def retireWith (s : St) (i : Info) (x : Session) (r : Reason) (close : Bool) : St × List Eff :=
  let res := retire s.core x.id r
  ({ s with core := res.1 },
   (if close then [closeEff i.sid r] else []) ++
   res.2.flatMap fun o => match o with
     | .ended to _ r' => [.send to (endedJson i.sid r')]
     | _ => [])

def onSession (s : St) (i : Info) (x : Session) : Req → St × List Eff
  | .create _ => (s, [])
  | .update _ m =>
    if m.isObj then (s, [hostEff "update" [sidField i.sid, ("metadata", some m)]]) else (s, [])
  | .destroy _ => retireWith s i x .destroyed true
  | .state _ st =>
    if x.owner = .napplet then
      (report s x (sanitize st), [hostEff "state" (sidField i.sid :: stateFields (sanitize st))])
    else (s, [])
  | .capabilities _ as =>
    if x.owner = .napplet then
      (setInfo s i.n (fun j => { j with actions := as }),
       [hostEff "capabilities" [sidField i.sid, ("actions", some (actionsJson as))]])
    else (s, [])
  | .command _ c =>
    if x.owner = .shell ∧ (c.action ∈ i.actions ∨ c.action ∈ i.controls) ∧ cmdOk c = true then
      (supersede s x c.action, [hostEff "command" (sidField i.sid :: commandFields (cleanCmd c (some "user")))])
    else (s, [])

def handle (_h : Host) (_w : World) (cx : Ctx) (s : St) (r : Req) : St × List Eff :=
  match r with
  | .create c => handleCreate cx s c
  | _ =>
    match r.sid? with
    | none => (s, [])
    | some w =>
      match owned s cx.port w with
      | none => (s, [])
      | some (i, x) => onSession s i x r

def onReply (_h : Host) (_w : World) (s : St) (_n : Nat) (_r : Reply) : St × List Eff := (s, [])

def actionFor : Status → Action
  | .playing | .buffering => .play
  | .paused => .pause
  | .stopped => .stop

/-- Focus decisions: a backend command plus the `media.state` report for shell-owned
sessions, a `media.command` for napplet-owned ones. -/
def realizeFocus (w : String) : MediaOut → List Eff
  | .state to _ st r =>
    [hostEff "command" (sidField w :: commandFields ⟨actionFor st, none, r.map reasonName⟩),
     .send to (stateJson w ⟨st, none, none, none, r.map reasonName⟩)]
  | .command to _ a r => [.send to (commandJson w ⟨a, none, r.map reasonName⟩)]
  | _ => []

def hostEvent (s : St) (i : Info) (x : Session) (ev : String) (args : Json) : St × List Eff :=
  match ev with
  | "state" =>
    match x.owner, stateOf? args with
    | .shell, some st => (report s x (sanitize st), [.send x.endpoint (stateJson i.sid (sanitize st))])
    | _, _ => (s, [])
  | "capabilities" =>
    match x.owner, (args.get? "actions").bind actionsOf? with
    | .shell, some as =>
      (setInfo s i.n (fun j => { j with actions := as }), [.send x.endpoint (capsJson i.sid as)])
    | _, _ => (s, [])
  | "controls" =>
    match (args.get? "controls").bind actionsOf? with
    | some as =>
      (setInfo s i.n (fun j => { j with controls := as }), [.send x.endpoint (controlsJson i.sid as)])
    | none => (s, [])
  | "command" =>
    match x.owner, commandOf? args with
    | .napplet, some c =>
      if c.action ∈ i.actions ∧ cmdOk c = true then
        (supersede s x c.action, [.send x.endpoint (commandJson i.sid (cleanCmd c c.reason))])
      else (s, [])
    | _, _ => (s, [])
  | "focusLost" =>
    if x.owner = .napplet ∧ x.status = .playing ∧ Action.pause ∉ i.actions then
      retireWith s i x .policy true
    else
      let res := focusLost s.core x.id
      ({ s with core := res.1 }, res.2.flatMap (realizeFocus i.sid))
  | "focusGained" =>
    let res := focusGained s.core x.id
    ({ s with core := res.1 }, res.2.flatMap (realizeFocus i.sid))
  | "retire" => retireWith s i x (((args.getStr? "reason").bind reasonOf?).getD .policy) false
  | _ => (s, [])

def onEvent (_h : Host) (_w : World) (s : St) : HostEvent → St × List Eff
  | .nap .media ev args =>
    match args.getStr? "sessionId" with
    | none => (s, [])
    | some w =>
      match lookup s w with
      | none => (s, [])
      | some (i, x) => hostEvent s i x ev args
  | _ => (s, [])

/-- Endpoint teardown: every session it owns is stopped (`close`) and retired, with no
notification to the dead endpoint (NAP-MEDIA §Session retirement). Canonical ids stay
issued. -/
def drop (s : St) (p : PortId) : St × List Eff :=
  let gone := s.core.live.filter (·.endpoint == p)
  ({ s with core := { s.core with live := s.core.live.filter (·.endpoint != p),
                                  retired := gone.map (·.id) ++ s.core.retired } },
   gone.filterMap fun x => (s.info.find? (·.n == x.id)).map fun i => closeEff i.sid .destroyed)

def mentions (s : St) (p : PortId) : Bool := s.core.live.any (·.endpoint == p)


/-! ### Properties -/

/-- Every live session after a transition existed before with the same id, owner and
endpoint (NAP-MEDIA: nothing changes a session's owner). -/
def Keeps (c c' : MediaState) : Prop :=
  ∀ x ∈ c'.live, ∃ y ∈ c.live, y.id = x.id ∧ y.owner = x.owner ∧ y.endpoint = x.endpoint

theorem Keeps.refl (c : MediaState) : Keeps c c := fun x hx => ⟨x, hx, rfl, rfl, rfl⟩

theorem keeps_modify (c : MediaState) (n : Nat) (st : Status) (b : Bool) : Keeps c (modify c n st b) :=
  fun _ hx => mem_modify hx

theorem keeps_retire (c : MediaState) (n : Nat) (r : Reason) : Keeps c (retire c n r).1 := by
  intro x hx
  unfold retire at hx
  split at hx
  · exact ⟨x, hx, rfl, rfl, rfl⟩
  · simp only [List.mem_filter] at hx
    exact ⟨x, hx.1, rfl, rfl, rfl⟩

theorem keeps_userPause (c : MediaState) (n : Nat) : Keeps c (userPause c n) := by
  unfold userPause; split
  · exact Keeps.refl _
  · exact keeps_modify _ _ _ _

theorem keeps_focusLost (c : MediaState) (n : Nat) : Keeps c (focusLost c n).1 := by
  unfold focusLost; split
  · exact Keeps.refl _
  · split
    · exact Keeps.refl _
    · exact keeps_modify _ _ _ _

theorem keeps_focusGained (c : MediaState) (n : Nat) : Keeps c (focusGained c n).1 := by
  unfold focusGained; split
  · exact Keeps.refl _
  · split
    · exact Keeps.refl _
    · exact keeps_modify _ _ _ _

theorem keeps_supersede (s : St) (x : Session) (a : Action) : Keeps s.core (supersede s x a).core := by
  cases a <;> simp only [supersede]
  all_goals first | exact keeps_userPause _ _ | exact keeps_modify _ _ _ _ | exact Keeps.refl _

theorem keeps_retireWith (s : St) (i : Info) (x : Session) (r : Reason) (c : Bool) :
    Keeps s.core (retireWith s i x r c).1.core := keeps_retire _ _ _

theorem keeps_onSession (s : St) (i : Info) (x : Session) (r : Req) :
    Keeps s.core (onSession s i x r).1.core := by
  cases r <;> simp only [onSession] <;> (try split)
  all_goals first | exact Keeps.refl _ | exact keeps_retireWith _ _ _ _ _ | exact keeps_modify _ _ _ _ | exact keeps_supersede _ _ _

theorem keeps_hostEvent (s : St) (i : Info) (x : Session) (ev : String) (args : Json) :
    Keeps s.core (hostEvent s i x ev args).1.core := by
  unfold hostEvent
  split <;> (try split) <;> (try split)
  all_goals first | exact Keeps.refl _ | exact keeps_retireWith _ _ _ _ _ | exact keeps_modify _ _ _ _ | exact keeps_supersede _ _ _ | exact keeps_focusLost _ _ | exact keeps_focusGained _ _

/-- Host events never create sessions or change an owner or endpoint. -/
theorem onEvent_keeps (h : Host) (w : World) (s : St) (e : HostEvent) :
    Keeps s.core (onEvent h w s e).1.core := by
  unfold onEvent
  split
  · split
    · exact Keeps.refl _
    · split
      · exact Keeps.refl _
      · exact keeps_hostEvent _ _ _ _ _
  · exact Keeps.refl _

theorem create_live {c : MediaState} {p : Endpoint} {id : String} {o : Owner} {hs cn : Bool}
    {x : Session} (hx : x ∈ (NapMedia.create c p id o hs cn).1.live) : x ∈ c.live ∨ x.endpoint = p := by
  unfold NapMedia.create at hx
  split at hx
  · exact .inl hx
  · split at hx
    · exact .inl hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact .inr rfl
      · exact .inl hx

/-- Requests change existing sessions only as `Keeps` allows; the only new session is
the requester's own. -/
theorem handle_keeps (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (x : Session)
    (hx : x ∈ (handle h w cx s r).1.core.live) :
    (∃ y ∈ s.core.live, y.id = x.id ∧ y.owner = x.owner ∧ y.endpoint = x.endpoint) ∨
      x.endpoint = cx.port := by
  cases r
  case create c =>
    simp only [handle, handleCreate] at hx
    split at hx
    · exact .inl ⟨x, hx, rfl, rfl, rfl⟩
    · split at hx
      · exact .inl ⟨x, hx, rfl, rfl, rfl⟩
      · split at hx
        · exact .inl ⟨x, hx, rfl, rfl, rfl⟩
        · rcases create_live hx with hx | hx
          · exact .inl ⟨x, hx, rfl, rfl, rfl⟩
          · exact .inr hx
  all_goals
    simp only [handle, Req.sid?] at hx
    split at hx
    · exact .inl ⟨x, hx, rfl, rfl, rfl⟩
    · exact .inl (keeps_onSession _ _ _ _ x hx)

theorem mentions_iff (s : St) (q : PortId) :
    mentions s q = true ↔ ∃ x ∈ s.core.live, x.endpoint = q := by
  simp [mentions]

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  cases hm : mentions (drop s p).1 p
  · rfl
  · obtain ⟨x, hx, he⟩ := (mentions_iff _ _).1 hm
    simp only [drop, List.mem_filter] at hx
    simp [he] at hx

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  obtain ⟨x, hx, he⟩ := (mentions_iff _ _).1 h
  simp only [drop, List.mem_filter] at hx
  exact (mentions_iff _ _).2 ⟨x, hx.1, he⟩

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  obtain ⟨x, hx, rfl⟩ := (mentions_iff _ _).1 hm
  rcases handle_keeps h w cx s r x hx with ⟨y, hy, -, -, he⟩ | he
  · exact .inl ((mentions_iff _ _).2 ⟨y, hy, he⟩)
  · exact .inr ⟨cx, hcx, he.symm⟩

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := .inl hm

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  obtain ⟨x, hx, rfl⟩ := (mentions_iff _ _).1 hm
  obtain ⟨y, hy, -, -, he⟩ := onEvent_keeps h w s e x hx
  exact .inl ((mentions_iff _ _).2 ⟨y, hy, he⟩)

/-! #### The NAP-MEDIA registry invariant is preserved -/

/-- Component invariant: `NapMedia.Inv` on the registry. -/
def Inv (s : St) : Prop := NapMedia.Inv s.core

theorem Inv.init (cfg : Cfg) : Inv (St.init cfg) := NapMedia.Inv.init

theorem inv_supersede {s : St} (hi : Inv s) (x : Session) (a : Action) : Inv (supersede s x a) := by
  cases a <;> simp only [supersede]
  all_goals first | exact NapMedia.Inv.userPause hi _ | exact NapMedia.Inv.modify hi _ _ _ | exact hi

theorem inv_onSession {s : St} (hi : Inv s) (i : Info) (x : Session) (r : Req) :
    Inv (onSession s i x r).1 := by
  cases r <;> simp only [onSession] <;> (try split)
  all_goals first | exact hi | exact NapMedia.Inv.retire hi _ _ | exact NapMedia.Inv.modify hi _ _ _ | exact inv_supersede hi _ _

theorem handle_inv (h : Host) (w : World) (cx : Ctx) {s : St} (hi : Inv s) (r : Req) :
    Inv (handle h w cx s r).1 := by
  cases r
  case create c =>
    simp only [handle, handleCreate]
    split
    · exact hi
    · split
      · exact hi
      · split
        · exact hi
        · exact NapMedia.Inv.create hi _ _ _ _ _
  all_goals
    simp only [handle, Req.sid?]
    split
    · exact hi
    · exact inv_onSession hi ..

theorem inv_hostEvent {s : St} (hi : Inv s) (i : Info) (x : Session) (ev : String) (args : Json) :
    Inv (hostEvent s i x ev args).1 := by
  unfold hostEvent
  split <;> (try split) <;> (try split)
  all_goals first | exact hi | exact NapMedia.Inv.retire hi _ _ | exact NapMedia.Inv.modify hi _ _ _ | exact inv_supersede hi _ _ | exact NapMedia.Inv.focusLost hi _ | exact NapMedia.Inv.focusGained hi _

theorem onEvent_inv (h : Host) (w : World) {s : St} (hi : Inv s) (e : HostEvent) :
    Inv (onEvent h w s e).1 := by
  unfold onEvent
  split
  · split
    · exact hi
    · split
      · exact hi
      · exact inv_hostEvent hi ..
  · exact hi

theorem eq_of_nodup_map {l : List Session} (h : (l.map (·.id)).Nodup) {x y : Session}
    (hx : x ∈ l) (hy : y ∈ l) (he : x.id = y.id) : x = y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
    · rw [hx, hy]
    · rw [hx] at he; exact absurd he.symm (h.1 y hy)
    · rw [hy] at he; exact absurd he (h.1 x hx)
    · exact ih h.2 hx hy

theorem drop_inv {s : St} (hi : Inv s) (p : PortId) : Inv (drop s p).1 := by
  constructor
  · intro x hx
    simp only [drop, List.mem_filter] at hx
    exact hi.live_lt x hx.1
  · intro r hr
    simp only [drop, List.mem_append, List.mem_map, List.mem_filter] at hr
    rcases hr with ⟨x, ⟨hx, -⟩, rfl⟩ | hr
    · exact hi.live_lt x hx
    · exact hi.retired_lt r hr
  · intro x hx
    simp only [drop, List.mem_filter, bne_iff_ne, ne_eq] at hx
    simp only [drop, List.mem_append, List.mem_map, List.mem_filter, beq_iff_eq, not_or, not_exists,
      not_and]
    refine ⟨fun y hy hid => ?_, hi.disjoint x hx.1⟩
    have := eq_of_nodup_map hi.nodup hy.1 hx.1 hid
    subst this
    exact hx.2 hy.2
  · exact hi.nodup.sublist ((List.filter_sublist).map _)

/-! #### Canonical ids are never reissued -/

theorem used_setInfo (s : St) (n : Nat) (f : Info → Info) (hf : ∀ j, (f j).sid = j.sid) :
    used (setInfo s n f) = used s := by
  simp only [used, setInfo, List.map_map]
  congr 1
  funext j
  simp only [Function.comp]
  split <;> simp [hf]

theorem used_supersede (s : St) (x : Session) (a : Action) : used (supersede s x a) = used s := by
  cases a <;> rfl

theorem used_onSession (s : St) (i : Info) (x : Session) (r : Req) :
    used (onSession s i x r).1 = used s := by
  cases r <;> simp only [onSession] <;> (try split)
  all_goals first | rfl | exact used_setInfo _ _ _ (fun _ => rfl) | exact used_supersede ..

/-- The issued ids only ever grow by one id that was never issued before. -/
theorem handle_used (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    used (handle h w cx s r).1 = used s ∨
      ∃ v, v ∉ used s ∧ used (handle h w cx s r).1 = v :: used s := by
  cases r
  case create c =>
    simp only [handle, handleCreate]
    split
    · exact .inl rfl
    · split
      · exact .inl rfl
      · rename_i hfresh
        split
        · exact .inl rfl
        · exact .inr ⟨_, hfresh, rfl⟩
  all_goals
    simp only [handle, Req.sid?]
    split
    · exact .inl rfl
    · exact .inl (used_onSession ..)

theorem used_hostEvent (s : St) (i : Info) (x : Session) (ev : String) (args : Json) :
    used (hostEvent s i x ev args).1 = used s := by
  unfold hostEvent
  split <;> (try split) <;> (try split)
  all_goals first | rfl | exact used_setInfo _ _ _ (fun _ => rfl) | exact used_supersede ..

theorem onEvent_used (h : Host) (w : World) (s : St) (e : HostEvent) :
    used (onEvent h w s e).1 = used s := by
  unfold onEvent
  split
  · split
    · rfl
    · split
      · rfl
      · exact used_hostEvent ..
  · rfl

theorem drop_used (s : St) (p : PortId) : used (drop s p).1 = used s := rfl

/-! #### Retired and unknown sessions are silent -/

theorem lookup_some {s : St} {w : String} {i : Info} {x : Session} (h : lookup s w = some (i, x)) :
    infoOf s w = some i ∧ find s.core i.n = some x := by
  unfold lookup at h
  split at h
  · simp at h
  · rename_i i' hi'
    cases hf : find s.core i'.n with
    | none => simp [hf] at h
    | some y => simp [hf] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hi', hf⟩

theorem owned_some {s : St} {p : PortId} {w : String} {i : Info} {x : Session}
    (h : owned s p w = some (i, x)) : lookup s w = some (i, x) ∧ x.endpoint = p := by
  unfold owned at h
  split at h
  · split at h
    · simp at h; obtain ⟨rfl, rfl⟩ := h; rename_i hl he; exact ⟨hl, he⟩
    · simp at h
  · simp at h

/-- A retired id names no live session (`NapMedia.find_retired`). -/
theorem lookup_retired {s : St} (hi : Inv s) {w : String} {i : Info} (hw : infoOf s w = some i)
    (hr : i.n ∈ s.core.retired) : lookup s w = none := by
  simp [lookup, hw, find_retired hi hr]

/-- Messages naming an unknown or retired session do nothing (NAP-MEDIA: "MUST be
silently ignored"; a stale `play` cannot reacquire output). -/
theorem handle_unknown_silent (h : Host) (w' : World) (cx : Ctx) (s : St) (r : Req) {w : String}
    (hr : r.sid? = some w) (hl : lookup s w = none) : handle h w' cx s r = (s, []) := by
  cases r <;> simp only [Req.sid?, reduceCtorEq, Option.some.injEq] at hr <;> subst hr <;>
    simp [handle, Req.sid?, owned, hl]

theorem onEvent_unknown_silent (h : Host) (w' : World) (s : St) (ev : String) (args : Json)
    {w : String} (ha : args.getStr? "sessionId" = some w) (hl : lookup s w = none) :
    onEvent h w' s (.nap .media ev args) = (s, []) := by
  simp [onEvent, ha, hl]

/-- `media.session.ended` is sent at most once: a second destroy of the same id does
nothing (`NapMedia.retire_once`). -/
theorem destroy_once (h : Host) (w : World) (cx : Ctx) (s : St) (sid : String) :
    (handle h w cx (handle h w cx s (.destroy sid)).1 (.destroy sid)).2 = [] := by
  cases ho : owned s cx.port sid with
  | none => simp [handle, Req.sid?, ho]
  | some ix =>
    obtain ⟨i, x⟩ := ix
    obtain ⟨hl, -⟩ := owned_some ho
    obtain ⟨hinfo, hfind⟩ := lookup_some hl
    have hxid := (find_some hfind).2
    have hnone : lookup (retireWith s i x .destroyed true).1 sid = none := by
      simp only [lookup, retireWith]
      have : infoOf { s with core := (retire s.core x.id .destroyed).1 } sid = infoOf s sid := rfl
      rw [this, hinfo]
      simp only
      rw [← hxid, find_retire_none]
      rfl
    have e1 : handle h w cx s (.destroy sid) = retireWith s i x .destroyed true := by
      simp only [handle, Req.sid?, ho, onSession]
    rw [e1]
    simp only [handle, Req.sid?, owned, hnone]

/-! #### Focus and ownership -/

/-- Focus regain resumes only a session that focus loss paused
(`NapMedia.resume_only_after_focus_pause`). -/
theorem focusGained_only_after_focus_pause (h : Host) (w' : World) (s : St) (args : Json) {w : String}
    (ha : args.getStr? "sessionId" = some w)
    (hne : (onEvent h w' s (.nap .media "focusGained" args)).2 ≠ []) :
    ∃ i x, lookup s w = some (i, x) ∧ x.pausedByFocus = true := by
  cases hl : lookup s w with
  | none => simp [onEvent, ha, hl] at hne
  | some ix =>
    obtain ⟨i, x⟩ := ix
    refine ⟨i, x, rfl, ?_⟩
    have hfind := (lookup_some hl).2
    have hxid := (find_some hfind).2
    simp only [onEvent, ha, hl, hostEvent] at hne
    obtain ⟨o, ho⟩ : ∃ o, o ∈ (focusGained s.core x.id).2 := by
      cases hfo : (focusGained s.core x.id).2 with
      | nil => simp [hfo] at hne
      | cons o _ => exact ⟨o, by simp⟩
    obtain ⟨y, hy, hp⟩ := resume_only_after_focus_pause ho
    rw [hxid, hfind] at hy
    cases hy
    exact hp

theorem realizeCreate_open {cx : Ctx} {s : St} {c : Create} {w : String} {o : MediaOut} {a : Json}
    (h : Eff.effect (.nap .media "open" a) ∈ realizeCreate cx s c w o) : ∃ n, o = .fetchSource n := by
  cases o with
  | createResult to id sid e => cases sid <;> simp [realizeCreate] at h
  | fetchSource n => exact ⟨n, rfl⟩
  | ended => simp [realizeCreate] at h
  | state => simp [realizeCreate] at h
  | command => simp [realizeCreate] at h

/-- The shell fetches and plays a source only for a shell-owned session whose napplet
supplied one; napplet-owned `source` is never fetched (`NapMedia.fetch_only_shell_owned`). -/
theorem open_only_shell_owned (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (a : Json)
    (hm : Eff.effect (.nap .media "open" a) ∈ (handle h w cx s r).2) :
    ∃ c, r = .create c ∧ c.owner = .shell ∧ c.source.isSome = true := by
  cases r
  case create c =>
    refine ⟨c, rfl, ?_⟩
    simp only [handle, handleCreate] at hm
    split at hm
    · simp at hm
    · split at hm
      · simp at hm
      · have key : Eff.effect (.nap .media "open" a) ∈
            (NapMedia.create s.core cx.port c.id c.owner c.source.isSome
              (!(c.owner = .shell && c.autoplay = some true && !s.cfg.autoplay))).2.flatMap
              (realizeCreate cx s c (canonical s c.hint)) := by
          split at hm
          · exact hm
          · rcases List.mem_append.mp hm with hm | hm
            · exact hm
            · split at hm <;> simp [hostEff] at hm
        obtain ⟨o, ho, he⟩ := List.mem_flatMap.mp key
        obtain ⟨n, rfl⟩ := realizeCreate_open he
        exact fetch_only_shell_owned ho
  all_goals
    simp only [handle, Req.sid?] at hm
    split at hm
    · simp at hm
    · simp only [onSession] at hm
      first
        | (simp only [retireWith] at hm
           rcases List.mem_append.mp hm with hm | hm
           · simp [closeEff, hostEff] at hm
           · obtain ⟨o, -, he⟩ := List.mem_flatMap.mp hm
             cases o <;> simp at he)
        | (split at hm <;> simp [hostEff] at hm)


/-! ### Vectors (upstream examples) -/

def sampleHost : Host :=
  { crypto := ⟨fun _ => "", fun _ => true⟩, verifyEvent := fun _ => true,
    sniff := fun _ => "application/octet-stream", rasterize := fun _ => none,
    looksCiphertext := fun _ => false, encryptedWith := fun _ => none, transform := id }

def sampleCtx : Ctx :=
  { port := 3, window := 1, identity := { dTag := some "player", artifactHash := "aa", publisher := "pk" },
    exposed := [.media], inst := 0 }

def sampleWorld : World := { now := 0, live := [sampleCtx], user := "" }

def run (j : Json) (s : St := .init) : St × List Eff :=
  match decode j with
  | .ok r => handle sampleHost sampleWorld sampleCtx s r
  | .reject rs => (s, rs.map (.send sampleCtx.port))
  | .unknown => (s, [])

def ev (s : St) (name : String) (args : String) : St × List Eff :=
  onEvent sampleHost sampleWorld s (.nap .media name (Json.parse! args))

/-- The messages sent to the sample endpoint. -/
def sent (es : List Eff) : List Json := es.filterMap fun | .send 3 m => some m | _ => none

def ops (es : List Eff) : List String := es.filterMap fun | .effect (.nap .media op _) => some op | _ => none

def dec? (j : Json) : Option Req :=
  match decode j with
  | .ok r => some r
  | _ => none

def ex1 := "{ \"type\": \"media.session.create\", \"id\": \"m1\", \"owner\": \"napplet\", \"sessionId\": \"s1\", \"metadata\": { \"title\": \"My Song\", \"artist\": \"The Artist\" } }"
def ex2 := "{ \"type\": \"media.session.create\", \"id\": \"m2\", \"owner\": \"shell\", \"source\": { \"url\": \"https://example.com/live.mp3\", \"mimeType\": \"audio/mpeg\" }, \"metadata\": { \"title\": \"Live Stream\" }, \"autoplay\": true, \"live\": true }"
def ex3 := "{ \"type\": \"media.session.create\", \"id\": \"m3\", \"owner\": \"shell\", \"source\": { \"url\": \"https://example.com/live.mp3\", \"mimeType\": \"audio/mpeg\" }, \"metadata\": { \"title\": \"Live Stream\" }, \"context\": { \"links\": [{ \"rel\": \"live-chat\", \"title\": \"Live Stream\", \"nostr\": { \"address\": \"30311:pubkey:d-tag\" } }] }, \"autoplay\": true, \"live\": true }"

-- decode of every upstream request example
#guard decode (Json.parse! ex1) matches .ok (.create { id := "m1", owner := .napplet, hint := some "s1", .. })
#guard decode (Json.parse! ex2) matches .ok (.create { id := "m2", owner := .shell, autoplay := some true, live := some true, .. })
#guard decode (Json.parse! ex3) matches .ok (.create { id := "m3", owner := .shell, context := some _, .. })
#guard decode (Json.parse! "{ \"type\": \"media.session.update\", \"sessionId\": \"s1\", \"metadata\": { \"title\": \"Updated Title\" } }") matches .ok (.update "s1" _)
#guard dec? (Json.parse! "{ \"type\": \"media.state\", \"sessionId\": \"s1\", \"status\": \"playing\", \"position\": 42.5, \"duration\": 240, \"volume\": 0.8 }")
  == some (.state "s1" { status := .playing, position := some ⟨425, -1⟩, duration := some ⟨24, 1⟩, volume := some ⟨8, -1⟩ })
#guard dec? (Json.parse! "{ \"type\": \"media.capabilities\", \"sessionId\": \"s1\", \"actions\": [\"play\", \"pause\", \"seek\", \"volume\"] }")
  == some (.capabilities "s1" [.play, .pause, .seek, .volume])
#guard dec? (Json.parse! "{ \"type\": \"media.command\", \"sessionId\": \"shell-7\", \"action\": \"pause\" }")
  == some (.command "shell-7" { action := .pause })
#guard dec? (Json.parse! "{ \"type\": \"media.session.destroy\", \"sessionId\": \"s1\" }") == some (.destroy "s1")
#guard dec? (Json.parse! "{ \"type\": \"media.state\", \"sessionId\": \"s2\", \"status\": \"paused\", \"reason\": \"focus-lost\" }")
  == some (.state "s2" { status := .paused, reason := some "focus-lost" })
-- shell → napplet types and unknown types are ignored
#guard decode (Json.parse! "{ \"type\": \"media.session.ended\", \"sessionId\": \"s1\", \"reason\": \"destroyed\" }") matches .unknown
#guard decode (Json.parse! "{ \"type\": \"media.play\", \"sessionId\": \"s1\" }") matches .unknown
-- malformed
#guard match decode (Json.parse! "{ \"type\": \"media.session.create\", \"id\": \"m9\" }") with
  | .reject [m] => Json.same m (Json.parse! "{\"type\":\"media.session.create.result\",\"id\":\"m9\",\"error\":\"invalid request\"}")
  | _ => false
#guard match decode (Json.parse! "{ \"type\": \"media.session.create\", \"id\": \"m9\", \"owner\": \"napplet\", \"sessionId\": 4 }") with
  | .reject [m] => Json.same m (Json.parse! "{\"type\":\"media.session.create.result\",\"id\":\"m9\",\"error\":\"invalid session ID\"}")
  | _ => false
#guard decode (Json.parse! "{ \"type\": \"media.session.create\", \"owner\": \"napplet\" }") matches .reject []
#guard decode (Json.parse! "{ \"type\": \"media.command\", \"sessionId\": \"s1\", \"action\": \"rewind\" }") matches .reject []

-- Create a session (napplet-owned, preferred id honoured)
def afterEx1 := run (Json.parse! ex1)
#guard match sent afterEx1.2 with
  | r :: _ => Json.same r (Json.parse! "{ \"type\": \"media.session.create.result\", \"id\": \"m1\", \"sessionId\": \"s1\", \"owner\": \"napplet\" }")
  | _ => false
#guard ops afterEx1.2 == ["register"]

-- Create a shell-owned playback session (`shell-7` when seven ids were issued before)
def st7 : St := { St.init with core := ⟨[], [0, 1, 2, 3, 4, 5, 6], 7⟩ }
def afterEx2 := run (Json.parse! ex2) st7
#guard match sent afterEx2.2 with
  | r :: _ => Json.same r (Json.parse! "{ \"type\": \"media.session.create.result\", \"id\": \"m2\", \"sessionId\": \"shell-7\", \"owner\": \"shell\" }")
  | _ => false
#guard ops afterEx2.2 == ["open"]
#guard match run (Json.parse! ex3) { st7 with core := ⟨[], [], 8⟩ } |>.2 |> sent with
  | r :: _ => Json.same r (Json.parse! "{ \"type\": \"media.session.create.result\", \"id\": \"m3\", \"sessionId\": \"shell-8\", \"owner\": \"shell\" }")
  | _ => false
-- shell-owned without source
#guard match sent (run (Json.parse! "{ \"type\": \"media.session.create\", \"id\": \"m4\", \"owner\": \"shell\" }")).2 with
  | [r] => Json.same r (Json.parse! "{ \"type\": \"media.session.create.result\", \"id\": \"m4\", \"error\": \"missing source\" }")
  | _ => false
-- session limit: upstream's example, verbatim (the preferred id is echoed; no session exists)
#guard match sent (run (Json.parse! ex1) { St.init with cfg := { maxSessions := 0 } }).2 with
  | [r] => Json.same r (Json.parse! "{ \"type\": \"media.session.create.result\", \"id\": \"m1\", \"sessionId\": \"s1\", \"error\": \"session limit exceeded\" }")
  | _ => false
-- a reused preferred id is rewritten
#guard match sent (run (Json.parse! ex1) afterEx1.1).2 with
  | r :: _ => Json.same r (Json.parse! "{ \"type\": \"media.session.create.result\", \"id\": \"m1\", \"sessionId\": \"shell-1\", \"owner\": \"napplet\" }")
  | _ => false

-- Update metadata, report state and capabilities: host instructions, nothing sent back
#guard ops (run (Json.parse! "{ \"type\": \"media.session.update\", \"sessionId\": \"s1\", \"metadata\": { \"title\": \"Updated Title\" } }") afterEx1.1).2 == ["update"]
#guard ops (run (Json.parse! "{ \"type\": \"media.state\", \"sessionId\": \"s1\", \"status\": \"playing\", \"position\": 42.5, \"duration\": 240, \"volume\": 0.8 }") afterEx1.1).2 == ["state"]
def withCaps := run (Json.parse! "{ \"type\": \"media.capabilities\", \"sessionId\": \"s1\", \"actions\": [\"play\", \"pause\", \"seek\", \"volume\"] }") afterEx1.1
#guard ops withCaps.2 == ["capabilities"]

-- Shell sends commands (user controls in the shell)
#guard match sent (ev withCaps.1 "command" "{\"sessionId\": \"s1\", \"action\": \"pause\"}").2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.command\", \"sessionId\": \"s1\", \"action\": \"pause\" }")
  | _ => false
#guard match sent (ev withCaps.1 "command" "{\"sessionId\": \"s1\", \"action\": \"seek\", \"value\": 120}").2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.command\", \"sessionId\": \"s1\", \"action\": \"seek\", \"value\": 120 }")
  | _ => false
#guard match sent (ev withCaps.1 "command" "{\"sessionId\": \"s1\", \"action\": \"volume\", \"value\": 0.5}").2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.command\", \"sessionId\": \"s1\", \"action\": \"volume\", \"value\": 0.5 }")
  | _ => false
-- `next` is not a declared capability
#guard (ev withCaps.1 "command" "{\"sessionId\": \"s1\", \"action\": \"next\"}").2 == []

-- Shell sends control list
#guard match sent (ev afterEx1.1 "controls" "{\"sessionId\": \"s1\", \"controls\": [\"play\", \"pause\", \"stop\", \"next\", \"prev\", \"seek\", \"volume\"]}").2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.controls\", \"sessionId\": \"s1\", \"controls\": [\"play\", \"pause\", \"stop\", \"next\", \"prev\", \"seek\", \"volume\"] }")
  | _ => false

-- Destroy a session
def destroyed := run (Json.parse! "{ \"type\": \"media.session.destroy\", \"sessionId\": \"s1\" }") afterEx1.1
#guard match sent destroyed.2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.session.ended\", \"sessionId\": \"s1\", \"reason\": \"destroyed\" }")
  | _ => false
#guard ops destroyed.2 == ["close"]
#guard (run (Json.parse! "{ \"type\": \"media.session.destroy\", \"sessionId\": \"s1\" }") destroyed.1).2 == []

-- Napplet command on shell-owned playback goes to the backend; backend state is reported
#guard ops (run (Json.parse! "{ \"type\": \"media.command\", \"sessionId\": \"shell-7\", \"action\": \"pause\" }") afterEx2.1).2 == ["command"]
#guard match sent (ev afterEx2.1 "state" "{\"sessionId\": \"shell-7\", \"status\": \"playing\", \"position\": 12.0, \"volume\": 0.7}").2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.state\", \"sessionId\": \"shell-7\", \"status\": \"playing\", \"position\": 12.0, \"volume\": 0.7 }")
  | _ => false
-- Track completes; the session remains usable
def completed := ev afterEx2.1 "state" "{\"sessionId\": \"shell-7\", \"status\": \"stopped\", \"reason\": \"ended\"}"
#guard match sent completed.2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.state\", \"sessionId\": \"shell-7\", \"status\": \"stopped\", \"reason\": \"ended\" }")
  | _ => false
#guard (lookup completed.1 "shell-7").isSome

-- Another session takes the shared player; the stale command is ignored
def preempted := ev afterEx2.1 "retire" "{\"sessionId\": \"shell-7\", \"reason\": \"preempted\"}"
#guard match sent preempted.2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.session.ended\", \"sessionId\": \"shell-7\", \"reason\": \"preempted\" }")
  | _ => false
#guard (run (Json.parse! "{ \"type\": \"media.command\", \"sessionId\": \"shell-7\", \"action\": \"play\" }") preempted.1).2 == []

-- Temporary focus loss and permitted resumption of napplet-owned playback (`s2`)
def s2 := (run (Json.parse! "{ \"type\": \"media.session.create\", \"id\": \"m5\", \"owner\": \"napplet\", \"sessionId\": \"s2\", \"capabilities\": [\"play\", \"pause\"] }")).1
def s2playing := (run (Json.parse! "{ \"type\": \"media.state\", \"sessionId\": \"s2\", \"status\": \"playing\" }") s2).1
def s2lost := ev s2playing "focusLost" "{\"sessionId\": \"s2\"}"
#guard match sent s2lost.2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.command\", \"sessionId\": \"s2\", \"action\": \"pause\", \"reason\": \"focus-lost\" }")
  | _ => false
def s2paused := (run (Json.parse! "{ \"type\": \"media.state\", \"sessionId\": \"s2\", \"status\": \"paused\", \"reason\": \"focus-lost\" }") s2lost.1).1
#guard match sent (ev s2paused "focusGained" "{\"sessionId\": \"s2\"}").2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.command\", \"sessionId\": \"s2\", \"action\": \"play\", \"reason\": \"focus-gained\" }")
  | _ => false
-- a user pause in between supersedes the focus pause: no resume
def s2user := (run (Json.parse! "{ \"type\": \"media.state\", \"sessionId\": \"s2\", \"status\": \"paused\", \"reason\": \"user\" }") s2lost.1).1
#guard (ev s2user "focusGained" "{\"sessionId\": \"s2\"}").2 == []
-- a napplet-owned session that cannot pause is retired on focus loss
def s3 := (run (Json.parse! "{ \"type\": \"media.session.create\", \"id\": \"m6\", \"owner\": \"napplet\", \"sessionId\": \"s3\" }")).1
def s3playing := (run (Json.parse! "{ \"type\": \"media.state\", \"sessionId\": \"s3\", \"status\": \"playing\" }") s3).1
#guard match sent (ev s3playing "focusLost" "{\"sessionId\": \"s3\"}").2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"media.session.ended\", \"sessionId\": \"s3\", \"reason\": \"policy\" }")
  | _ => false

-- Teardown stops the endpoint's sessions without notifying it
#guard (drop afterEx2.1 3).2.length == 1 && ops (drop afterEx2.1 3).2 == ["close"]
#guard mentions (drop afterEx2.1 3).1 3 == false

end Napplet.Run.Media

