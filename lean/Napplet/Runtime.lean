/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Run.Shell
import Napplet.Run.Theme
import Napplet.Run.Identity
import Napplet.Run.Storage
import Napplet.Run.Inc
import Napplet.Run.Intent
import Napplet.Run.Notify
import Napplet.Run.Display
import Napplet.Run.Keys
import Napplet.Run.Relay
import Napplet.Run.Outbox
import Napplet.Run.Media
import Napplet.Run.Config
import Napplet.Run.Resource
import Napplet.Run.Upload
import Napplet.Run.Link

/-!
# The composed runtime

`Runtime.step` is the whole shell: one input in (a browser event, a JSON message on
a port, a host reply or event, a clock tick), a list of outputs out (JSON messages
on ports, browser actions, host calls and effects). This file is generated from
the component table (one component per NAP, `Napplet/Run/*.lean`).

* Browser events go to `Shell.step` (NIP-5D transport and identity).
* A JSON message on port `p` becomes an envelope `{type, id}`; `Shell.step` decides
  whether it is processed at all (bound port, known and exposed domain). If it is,
  the domain's component decodes the full JSON and handles it with the endpoint
  context `Ctx.ofBinding` derived from the binding.
* Every `closePort` the shell emits tears the endpoint down in every component;
  then retained intent deliveries are flushed to newly ready targets.
* Host replies are routed by the call tag's domain; host events go to every
  component.

Main results (over every reachable state, `Runtime.Reachable`):
* `shell_inv`: the NIP-5D shell invariant (`Shell.Inv`) holds;
* `teardown_clears`: no component holds state for a port that is not bound, so
  teardown clears every NAP's per-endpoint state and a later binding of the same
  port starts clean; `port_closed_teardown`;
* `message_unbound_silent`, `message_unexposed_silent`: JSON on an unbound port, or
  of an unknown or unexposed domain, produces nothing.
-/

namespace Napplet.Runtime

/-- Shell policy and per-NAP configuration. -/
structure Config where
  shell : ShellConfig
  storageQuota : Nat := NapStorage.defaultQuota
  incCfg : Run.Inc.Cfg := {}
  intentCfg : Run.Intent.Cfg := {}
  notifyCfg : Run.Notify.Cfg := {}
  displayCfg : Run.Display.Cfg := {}
  relayCfg : Run.Relay.Cfg := {}
  outboxCfg : Run.Outbox.Cfg := {}
  mediaCfg : Run.Media.Cfg := {}
  resourceCfg : Run.Resource.Cfg := {}
  uploadCfg : Run.Upload.Cfg := {}
  linkCfg : Run.Link.Cfg := {}

structure RtState where
  shell : ShellState
  /-- Host-chosen instance id per window (from `Input.create`). -/
  inst : WindowId → Nat
  /-- Every port ever bound, so the bound endpoints can be listed. -/
  ports : List PortId
  now : Nat
  /-- The shell user's pubkey, `""` when none. -/
  user : String
  shellNap : Run.Shell.St
  theme : Run.Theme.St
  identity : Run.Identity.St
  storage : Run.Storage.St
  inc : Run.Inc.St
  intent : Run.Intent.St
  notify : Run.Notify.St
  display : Run.Display.St
  keys : Run.Keys.St
  relay : Run.Relay.St
  outbox : Run.Outbox.St
  media : Run.Media.St
  config : Run.Config.St
  resource : Run.Resource.St
  upload : Run.Upload.St
  link : Run.Link.St

def RtState.init (cfg : Config) : RtState where
  shell := .init
  inst := fun _ => 0
  ports := []
  now := 0
  user := ""
  shellNap := Run.Shell.St.init
  theme := Run.Theme.St.init
  identity := Run.Identity.St.init
  storage := Run.Storage.St.init cfg.storageQuota
  inc := Run.Inc.St.init cfg.incCfg
  intent := Run.Intent.St.init cfg.intentCfg
  notify := Run.Notify.St.init cfg.notifyCfg
  display := Run.Display.St.init cfg.displayCfg
  keys := Run.Keys.St.init
  relay := Run.Relay.St.init cfg.relayCfg
  outbox := Run.Outbox.St.init cfg.outboxCfg
  media := Run.Media.St.init cfg.mediaCfg
  config := Run.Config.St.init
  resource := Run.Resource.St.init cfg.resourceCfg
  upload := Run.Upload.St.init cfg.uploadCfg
  link := Run.Link.St.init cfg.linkCfg

inductive Input where
  /-- Run manifest `m` with fetched artifact `bytes` in new window `w` (NIP-5D
  §Identity step 2); `inst` is the host's stable instance id for this window. -/
  | create (w : WindowId) (m : ManifestEvent) (bytes : Bytes) (inst : Nat)
  /-- The iframe's `load` event. -/
  | load (w : WindowId)
  /-- `{type: "napplet.hello"}` from window `w` with these transferred ports. -/
  | hello (w : WindowId) (ports : List PortId)
  /-- Any other window-level message from window `w`. -/
  | windowMsg (w : WindowId)
  /-- The port closed or errored. -/
  | portClosed (p : PortId)
  /-- Shell policy attaches a grant to the session on port `p`. -/
  | grant (p : PortId) (g : Grant)
  /-- A message posted on port `p` (structured clone of a JSON value). -/
  | message (p : PortId) (msg : Json)
  | reply (tag : CallTag) (r : Reply)
  | event (e : HostEvent)
  | tick (now : Nat)

inductive Output where
  /-- Post this JSON message on port `to`. -/
  | send (to : PortId) (msg : Json)
  | rejected (w : WindowId) (e : ManifestError)
  /-- Create the `srcdoc` iframe for `w` with `sandbox="allow-scripts"`, the verified
  bytes, the bootstrap, and a `window.napplet` namespace holding exactly `exposed`. -/
  | iframeCreated (w : WindowId) (id : Identity) (exposed : List Domain)
  | bound (w : WindowId) (p : PortId) (id : Identity)
  /-- Call `close()` on the port. -/
  | closePort (p : PortId)
  | removeFrame (w : WindowId)
  | call (tag : CallTag) (c : Call)
  | effect (e : Effect)
  deriving DecidableEq, Repr

def ofEff : Eff → Output
  | .send p m => .send p m
  | .call t c => .call t c
  | .effect e => .effect e

def ofShell : Napplet.Output → List Output
  | .rejected w e => [.rejected w e]
  | .iframeCreated w id ex => [.iframeCreated w id ex]
  | .bound w p id => [.bound w p id]
  | .closePort p => [.closePort p]
  | .removeFrame w => [.removeFrame w]
  | .dispatch .. => []

/-! ### Views -/

def ctxOf (s : RtState) (p : PortId) : Option Ctx :=
  (s.shell.bindings p).map fun b => Ctx.ofBinding p b (s.inst b.window)

def world (s : RtState) : World :=
  { now := s.now, live := s.ports.filterMap (ctxOf s), user := s.user }

/-- An envelope's routing fields. A message without a string `type` is not a
NIP-5D message and is dropped. -/
def envOf? (j : Json) : Option Envelope :=
  (j.getStr? "type").map fun t => { type := t, id := j.getStr? "id" }

/-- Per-component: does it hold state for port `p`? -/
def mentionsList (s : RtState) (p : PortId) : List Bool :=
  [Run.Shell.mentions s.shellNap p,
   Run.Theme.mentions s.theme p,
   Run.Identity.mentions s.identity p,
   Run.Storage.mentions s.storage p,
   Run.Inc.mentions s.inc p,
   Run.Intent.mentions s.intent p,
   Run.Notify.mentions s.notify p,
   Run.Display.mentions s.display p,
   Run.Keys.mentions s.keys p,
   Run.Relay.mentions s.relay p,
   Run.Outbox.mentions s.outbox p,
   Run.Media.mentions s.media p,
   Run.Config.mentions s.config p,
   Run.Resource.mentions s.resource p,
   Run.Upload.mentions s.upload p,
   Run.Link.mentions s.link p]

/-- Any component holds state for port `p`. -/
def mentions (s : RtState) (p : PortId) : Bool := (mentionsList s p).any id

/-! ### Steps -/

def lift {α σ : Type} (dec : Decoded α) (port : PortId) (run : α → σ × List Eff)
    (set : σ → RtState) (s : RtState) : RtState × List Output :=
  match dec with
  | .ok r => let (st, effs) := run r; (set st, effs.map ofEff)
  | .reject rs => (s, rs.map (.send port))
  | .unknown => (s, [])

/-- Hand a JSON message to domain `d`'s component. -/
def napStep (h : Host) (w : World) (cx : Ctx) (s : RtState) (j : Json) : Domain → RtState × List Output
  | .shell => lift (Run.Shell.decode j) cx.port (Run.Shell.handle h w cx s.shellNap)
      (fun st => { s with shellNap := st }) s
  | .theme => lift (Run.Theme.decode j) cx.port (Run.Theme.handle h w cx s.theme)
      (fun st => { s with theme := st }) s
  | .identity => lift (Run.Identity.decode j) cx.port (Run.Identity.handle h w cx s.identity)
      (fun st => { s with identity := st }) s
  | .storage => lift (Run.Storage.decode j) cx.port (Run.Storage.handle h w cx s.storage)
      (fun st => { s with storage := st }) s
  | .inc => lift (Run.Inc.decode j) cx.port (Run.Inc.handle h w cx s.inc)
      (fun st => { s with inc := st }) s
  | .intent => lift (Run.Intent.decode j) cx.port (Run.Intent.handle h w cx s.intent)
      (fun st => { s with intent := st }) s
  | .notify => lift (Run.Notify.decode j) cx.port (Run.Notify.handle h w cx s.notify)
      (fun st => { s with notify := st }) s
  | .display => lift (Run.Display.decode j) cx.port (Run.Display.handle h w cx s.display)
      (fun st => { s with display := st }) s
  | .keys => lift (Run.Keys.decode j) cx.port (Run.Keys.handle h w cx s.keys)
      (fun st => { s with keys := st }) s
  | .relay => lift (Run.Relay.decode j) cx.port (Run.Relay.handle h w cx s.relay)
      (fun st => { s with relay := st }) s
  | .outbox => lift (Run.Outbox.decode j) cx.port (Run.Outbox.handle h w cx s.outbox)
      (fun st => { s with outbox := st }) s
  | .media => lift (Run.Media.decode j) cx.port (Run.Media.handle h w cx s.media)
      (fun st => { s with media := st }) s
  | .config => lift (Run.Config.decode j) cx.port (Run.Config.handle h w cx s.config)
      (fun st => { s with config := st }) s
  | .resource => lift (Run.Resource.decode j) cx.port (Run.Resource.handle h w cx s.resource)
      (fun st => { s with resource := st }) s
  | .upload => lift (Run.Upload.decode j) cx.port (Run.Upload.handle h w cx s.upload)
      (fun st => { s with upload := st }) s
  | .link => lift (Run.Link.decode j) cx.port (Run.Link.handle h w cx s.link)
      (fun st => { s with link := st }) s
  | _ => (s, [])

/-- Tear endpoint `p` down in every component. -/
def dropAll (s : RtState) (p : PortId) : RtState × List Output :=
  let (c0, e0) := Run.Shell.drop s.shellNap p
  let (c1, e1) := Run.Theme.drop s.theme p
  let (c2, e2) := Run.Identity.drop s.identity p
  let (c3, e3) := Run.Storage.drop s.storage p
  let (c4, e4) := Run.Inc.drop s.inc p
  let (c5, e5) := Run.Intent.drop s.intent p
  let (c6, e6) := Run.Notify.drop s.notify p
  let (c7, e7) := Run.Display.drop s.display p
  let (c8, e8) := Run.Keys.drop s.keys p
  let (c9, e9) := Run.Relay.drop s.relay p
  let (c10, e10) := Run.Outbox.drop s.outbox p
  let (c11, e11) := Run.Media.drop s.media p
  let (c12, e12) := Run.Config.drop s.config p
  let (c13, e13) := Run.Resource.drop s.resource p
  let (c14, e14) := Run.Upload.drop s.upload p
  let (c15, e15) := Run.Link.drop s.link p
  ({ s with shellNap := c0, theme := c1, identity := c2, storage := c3, inc := c4, intent := c5, notify := c6, display := c7, keys := c8, relay := c9, outbox := c10, media := c11, config := c12, resource := c13, upload := c14, link := c15 },
   (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15).map ofEff)

def closedPorts : List Napplet.Output → List PortId
  | [] => []
  | .closePort p :: os => p :: closedPorts os
  | _ :: os => closedPorts os

def dropPorts (s : RtState) : List PortId → RtState × List Output
  | [] => (s, [])
  | p :: ps =>
    let (s1, o1) := dropAll s p
    let (s2, o2) := dropPorts s1 ps
    (s2, o1 ++ o2)

def boundPorts : List Napplet.Output → List PortId
  | [] => []
  | .bound _ p _ :: os => p :: boundPorts os
  | _ :: os => boundPorts os

/-- Deliver retained intent deliveries to targets that are now ready. -/
def flushStep (h : Host) (s : RtState) : RtState × List Output :=
  let (st, effs) := Run.Intent.flush h (world s) s.intent
  ({ s with intent := st }, effs.map ofEff)

/-- A browser event: the NIP-5D shell, teardown of every closed port, then flush. -/
def browserStep (h : Host) (cfg : Config) (s : RtState) (e : Event) : RtState × List Output :=
  let (sh, outs) := Napplet.step h.crypto cfg.shell s.shell e
  let s1 := { s with shell := sh, ports := boundPorts outs ++ s.ports }
  let (s2, drops) := dropPorts s1 (closedPorts outs)
  let (s3, fl) := flushStep h s2
  (s3, outs.flatMap ofShell ++ drops ++ fl)

def replyStep (h : Host) (s : RtState) (tag : CallTag) (r : Reply) : RtState × List Output :=
  let w := world s
  match tag.domain with
  | .shell =>
    let (st, effs) := Run.Shell.onReply h w s.shellNap tag.n r
    ({ s with shellNap := st }, effs.map ofEff)
  | .theme =>
    let (st, effs) := Run.Theme.onReply h w s.theme tag.n r
    ({ s with theme := st }, effs.map ofEff)
  | .identity =>
    let (st, effs) := Run.Identity.onReply h w s.identity tag.n r
    ({ s with identity := st }, effs.map ofEff)
  | .storage =>
    let (st, effs) := Run.Storage.onReply h w s.storage tag.n r
    ({ s with storage := st }, effs.map ofEff)
  | .inc =>
    let (st, effs) := Run.Inc.onReply h w s.inc tag.n r
    ({ s with inc := st }, effs.map ofEff)
  | .intent =>
    let (st, effs) := Run.Intent.onReply h w s.intent tag.n r
    ({ s with intent := st }, effs.map ofEff)
  | .notify =>
    let (st, effs) := Run.Notify.onReply h w s.notify tag.n r
    ({ s with notify := st }, effs.map ofEff)
  | .display =>
    let (st, effs) := Run.Display.onReply h w s.display tag.n r
    ({ s with display := st }, effs.map ofEff)
  | .keys =>
    let (st, effs) := Run.Keys.onReply h w s.keys tag.n r
    ({ s with keys := st }, effs.map ofEff)
  | .relay =>
    let (st, effs) := Run.Relay.onReply h w s.relay tag.n r
    ({ s with relay := st }, effs.map ofEff)
  | .outbox =>
    let (st, effs) := Run.Outbox.onReply h w s.outbox tag.n r
    ({ s with outbox := st }, effs.map ofEff)
  | .media =>
    let (st, effs) := Run.Media.onReply h w s.media tag.n r
    ({ s with media := st }, effs.map ofEff)
  | .config =>
    let (st, effs) := Run.Config.onReply h w s.config tag.n r
    ({ s with config := st }, effs.map ofEff)
  | .resource =>
    let (st, effs) := Run.Resource.onReply h w s.resource tag.n r
    ({ s with resource := st }, effs.map ofEff)
  | .upload =>
    let (st, effs) := Run.Upload.onReply h w s.upload tag.n r
    ({ s with upload := st }, effs.map ofEff)
  | .link =>
    let (st, effs) := Run.Link.onReply h w s.link tag.n r
    ({ s with link := st }, effs.map ofEff)
  | _ => (s, [])

def newUser (s : RtState) : HostEvent → String
  | .userChanged pk => pk
  | _ => s.user

def eventStep (h : Host) (s : RtState) (e : HostEvent) : RtState × List Output :=
  let w := world s
  let (c0, e0) := Run.Shell.onEvent h w s.shellNap e
  let (c1, e1) := Run.Theme.onEvent h w s.theme e
  let (c2, e2) := Run.Identity.onEvent h w s.identity e
  let (c3, e3) := Run.Storage.onEvent h w s.storage e
  let (c4, e4) := Run.Inc.onEvent h w s.inc e
  let (c5, e5) := Run.Intent.onEvent h w s.intent e
  let (c6, e6) := Run.Notify.onEvent h w s.notify e
  let (c7, e7) := Run.Display.onEvent h w s.display e
  let (c8, e8) := Run.Keys.onEvent h w s.keys e
  let (c9, e9) := Run.Relay.onEvent h w s.relay e
  let (c10, e10) := Run.Outbox.onEvent h w s.outbox e
  let (c11, e11) := Run.Media.onEvent h w s.media e
  let (c12, e12) := Run.Config.onEvent h w s.config e
  let (c13, e13) := Run.Resource.onEvent h w s.resource e
  let (c14, e14) := Run.Upload.onEvent h w s.upload e
  let (c15, e15) := Run.Link.onEvent h w s.link e
  ({ s with shellNap := c0, theme := c1, identity := c2, storage := c3, inc := c4, intent := c5, notify := c6, display := c7, keys := c8, relay := c9, outbox := c10, media := c11, config := c12, resource := c13, upload := c14, link := c15, user := newUser s e },
   (e0 ++ e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7 ++ e8 ++ e9 ++ e10 ++ e11 ++ e12 ++ e13 ++ e14 ++ e15).map ofEff)

/-- The composed transition function: the whole shell. -/
def step (h : Host) (cfg : Config) (s : RtState) : Input → RtState × List Output
  | .create w m bytes inst =>
    let s' := if (s.shell.frames w).isNone then { s with inst := upd s.inst w inst } else s
    browserStep h cfg s' (.create w m bytes)
  | .load w => browserStep h cfg s (.load w)
  | .hello w ports => browserStep h cfg s (.hello w ports)
  | .windowMsg w => browserStep h cfg s (.windowMsg w)
  | .portClosed p => browserStep h cfg s (.portClosed p)
  | .grant p g => browserStep h cfg s (.grant p g)
  | .message p j =>
    match envOf? j with
    | none => (s, [])
    | some env =>
      match Napplet.step h.crypto cfg.shell s.shell (.nap p env) with
      | (_, [.dispatch _ _ d _]) =>
        match ctxOf s p with
        | some cx => napStep h (world s) cx s j d
        | none => (s, [])
      | _ => (s, [])
  | .reply tag r => replyStep h s tag r
  | .event e => eventStep h s e
  | .tick now => ({ s with now }, [])

inductive Reachable (h : Host) (cfg : Config) : RtState → Prop where
  | init : Reachable h cfg (.init cfg)
  | step {s : RtState} (i : Input) : Reachable h cfg s → Reachable h cfg (step h cfg s i).1

/-! ### Local properties -/

section local_props
variable {h : Host} {cfg : Config} {s : RtState}

/-- JSON on a port with no binding produces nothing and changes nothing (NIP-5D
§Identity: "MUST NOT process NAP messages from any source other than the bound port"). -/
theorem message_unbound_silent {p : PortId} {j : Json} (hb : s.shell.bindings p = none) :
    step h cfg s (.message p j) = (s, []) := by
  simp only [step]
  split
  · rfl
  · rw [nap_unbound_dropped hb]

/-- A message whose domain is unknown or not exposed to the endpoint produces
nothing (NIP-5D §Wire Format, and no capability probing). -/
theorem message_unexposed_silent {p : PortId} {j : Json} {env : Envelope} {b : Binding}
    (he : envOf? j = some env) (hb : s.shell.bindings p = some b)
    (hd : ∀ d, env.domain? = some d → d ∉ b.exposed) :
    step h cfg s (.message p j) = (s, []) := by
  simp only [step, he]
  have : Napplet.step h.crypto cfg.shell s.shell (.nap p env) = (s.shell, []) := by
    simp only [Napplet.step, hb]
    split
    · rename_i d hd'
      simp [hd d hd']
    · rfl
  rw [this]

end local_props

/-! ### The composed invariant -/

/-- Composed runtime invariant. -/
structure Inv (h : Host) (cfg : Config) (s : RtState) : Prop where
  shell : Napplet.Inv h.crypto cfg.shell s.shell
  /-- Every bound port is listed. -/
  ports : ∀ p b, s.shell.bindings p = some b → p ∈ s.ports
  /-- No component holds state for a port that is not bound. -/
  clean : ∀ p, s.shell.bindings p = none → mentions s p = false

theorem world_bound {s : RtState} {q : PortId} (hq : (world s).bound q) :
    ∃ b, s.shell.bindings q = some b := by
  obtain ⟨c, hc, rfl⟩ := hq
  simp only [world, List.mem_filterMap, ctxOf, Option.map_eq_some_iff] at hc
  obtain ⟨p, -, b, hb, rfl⟩ := hc
  exact ⟨b, hb⟩

theorem ctxOf_live {s : RtState} {p : PortId} {cx : Ctx}
    (hi : ∀ p b, s.shell.bindings p = some b → p ∈ s.ports)
    (h : ctxOf s p = some cx) : cx ∈ (world s).live := by
  simp only [world, List.mem_filterMap]
  simp only [ctxOf, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, _⟩ := h
  exact ⟨p, hi p b hb, by simp [ctxOf, hb]; assumption⟩

/-- Pointwise relation between two lists of the same length. -/
def Pw (R : Bool → Bool → Prop) : List Bool → List Bool → Prop
  | [], [] => True
  | a :: l, b :: l' => R a b ∧ Pw R l l'
  | _, _ => False

/-- Monotonicity of `any` along a pointwise implication. -/
theorem any_imp {P : Prop} : ∀ {l l' : List Bool},
    Pw (fun a b => a = true → b = true ∨ P) l' l → l'.any id = true → l.any id = true ∨ P
  | [], [], _, h => by simp at h
  | [], _ :: _, hf, _ => hf.elim
  | _ :: _, [], hf, _ => hf.elim
  | b :: l, a :: l', hf, h => by
    rcases hf with ⟨h1, h2⟩
    simp only [List.any_cons, id, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases h1 h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases any_imp h2 h with h | h
      · exact .inl (.inr h)
      · exact .inr h

/-- A state change whose new mentions are old ones or bound ports keeps `Inv`. -/
theorem Inv.of_mentions {h : Host} {cfg : Config} {s s' : RtState} (hi : Inv h cfg s)
    (hsh : s'.shell = s.shell) (hpo : s'.ports = s.ports)
    (hm : ∀ q, Pw (fun a b => a = true → b = true ∨ (world s).bound q)
      (mentionsList s' q) (mentionsList s q)) : Inv h cfg s' := by
  refine ⟨hsh ▸ hi.shell, hsh ▸ hpo ▸ hi.ports, ?_⟩
  intro q hq
  rw [hsh] at hq
  cases hmq : mentions s' q
  · rfl
  · rcases any_imp (hm q) hmq with h1 | h1
    · have := hi.clean q hq; simp only [mentions] at this; rw [this] at h1; simp at h1
    · obtain ⟨b, hb⟩ := world_bound h1; rw [hq] at hb; simp at hb

theorem Inv.message {h : Host} {cfg : Config} {s : RtState} (hi : Inv h cfg s) (p : PortId)
    (j : Json) : Inv h cfg (step h cfg s (.message p j)).1 := by
  simp only [step]
  split
  · exact hi
  · split
    · rename_i env sh d _ heq
      split
      · rename_i cx hcx
        have hlive := ctxOf_live hi.ports hcx
        cases d
        case shell =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => Run.Shell.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case intent =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Intent.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case inc =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Inc.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case theme =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => Run.Theme.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case identity =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Identity.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case relay =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Relay.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case storage =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Storage.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case keys =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Keys.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case media =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Media.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case notify =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Notify.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case resource =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Resource.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case config =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Config.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case upload =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Upload.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case value => exact hi
        case outbox =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Outbox.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
        case cvm => exact hi
        case link =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Link.handle_mentions _ _ _ _ _ _ hlive h1, trivial⟩
          · exact hi
          · exact hi
        case pow => exact hi
        case display =>
          simp only [napStep, lift]
          split
          · apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
            exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Display.handle_mentions _ _ _ _ _ _ hlive h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
          · exact hi
          · exact hi
      · exact hi
    · exact hi

/-! ### Teardown lemmas -/

theorem dropAll_shell (s : RtState) (p : PortId) :
    (dropAll s p).1.shell = s.shell ∧ (dropAll s p).1.ports = s.ports ∧
    (dropAll s p).1.inst = s.inst := ⟨rfl, rfl, rfl⟩

theorem any_imp_and {q p : PortId} : ∀ {l l' : List Bool},
    Pw (fun a b => a = true → b = true ∧ q ≠ p) l' l → l'.any id = true →
    l.any id = true ∧ q ≠ p
  | [], [], _, h => by simp at h
  | [], _ :: _, hf, _ => hf.elim
  | _ :: _, [], hf, _ => hf.elim
  | b :: l, a :: l', hf, h => by
    rcases hf with ⟨h1, h2⟩
    simp only [List.any_cons, id, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact ⟨.inl (h1 h).1, (h1 h).2⟩
    · exact ⟨.inr (any_imp_and h2 h).1, (any_imp_and h2 h).2⟩

theorem dropAll_mentions (s : RtState) (p q : PortId) (h : mentions (dropAll s p).1 q = true) :
    mentions s q = true ∧ q ≠ p := by
  apply any_imp_and _ h
  simp only [mentionsList, dropAll, Pw]
  exact ⟨fun h1 => ⟨Run.Shell.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Shell.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Theme.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Theme.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Identity.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Identity.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Storage.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Storage.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Inc.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Inc.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Intent.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Intent.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Notify.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Notify.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Display.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Display.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Keys.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Keys.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Relay.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Relay.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Outbox.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Outbox.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Media.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Media.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Config.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Config.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Resource.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Resource.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Upload.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Upload.drop_clears] at h1; simp at h1⟩,
    fun h1 => ⟨Run.Link.drop_mentions _ _ _ h1, by rintro rfl; rw [Run.Link.drop_clears] at h1; simp at h1⟩, trivial⟩

theorem dropPorts_shell (s : RtState) (ps : List PortId) :
    (dropPorts s ps).1.shell = s.shell ∧ (dropPorts s ps).1.ports = s.ports := by
  induction ps generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons p ps ih =>
    simp only [dropPorts]
    obtain ⟨h1, h2⟩ := ih (dropAll s p).1
    exact ⟨h1.trans rfl, h2.trans rfl⟩

theorem dropPorts_mentions (s : RtState) (ps : List PortId) (q : PortId)
    (h : mentions (dropPorts s ps).1 q = true) : mentions s q = true ∧ q ∉ ps := by
  induction ps generalizing s with
  | nil => exact ⟨h, by simp⟩
  | cons p ps ih =>
    simp only [dropPorts] at h
    obtain ⟨h1, h2⟩ := ih _ h
    obtain ⟨h3, h4⟩ := dropAll_mentions _ _ _ h1
    exact ⟨h3, by simp [h4, h2]⟩

theorem mem_closedPorts {os : List Napplet.Output} {p : PortId} (h : Napplet.Output.closePort p ∈ os) :
    p ∈ closedPorts os := by
  induction os with
  | nil => simp at h
  | cons o os ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [closedPorts]
    · have := ih h'; cases o <;> simp [closedPorts, this]

theorem mem_boundPorts {os : List Napplet.Output} {w : WindowId} {p : PortId} {id : Identity}
    (h : Napplet.Output.bound w p id ∈ os) : p ∈ boundPorts os := by
  induction os with
  | nil => simp at h
  | cons o os ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [boundPorts]
    · have := ih h'; cases o <;> simp [boundPorts, this]

theorem Inv.flush {h : Host} {cfg : Config} {s : RtState} (hi : Inv h cfg s) :
    Inv h cfg (flushStep h s).1 := by
  simp only [flushStep]
  apply Inv.of_mentions hi; rfl; rfl
  intro q; simp only [mentionsList, Pw]
  exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Intent.flush_mentions _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩

theorem Inv.browser {h : Host} {cfg : Config} {s : RtState} (hi : Inv h cfg s) (e : Event) :
    Inv h cfg (browserStep h cfg s e).1 := by
  simp only [browserStep]
  generalize hst : Napplet.step h.crypto cfg.shell s.shell e = r
  obtain ⟨sh, outs⟩ := r
  apply Inv.flush
  obtain ⟨hs1, hs2⟩ := dropPorts_shell { s with shell := sh, ports := boundPorts outs ++ s.ports } (closedPorts outs)
  have hsh : sh = (Napplet.step h.crypto cfg.shell s.shell e).1 := by rw [hst]
  have hout : outs = (Napplet.step h.crypto cfg.shell s.shell e).2 := by rw [hst]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs1, hsh]; exact hi.shell.step e
  · intro p b hb
    rw [hs1] at hb; rw [hs2]
    simp only at hb ⊢
    rw [hsh] at hb
    rcases Napplet.step_bind e hb with hb | ⟨w, id, hm⟩
    · exact List.mem_append_right _ (hi.ports p b hb)
    · exact List.mem_append_left _ (mem_boundPorts (hout ▸ hm))
  · intro q hq
    rw [hs1] at hq
    simp only at hq
    cases hm : mentions (dropPorts { s with shell := sh, ports := boundPorts outs ++ s.ports } (closedPorts outs)).1 q
    · rfl
    · obtain ⟨h1, h2⟩ := dropPorts_mentions _ _ _ hm
      rw [hsh] at hq
      rcases Napplet.step_unbind e hq with hq | hc
      · have : mentions s q = true := h1
        rw [hi.clean q hq] at this; exact absurd this (by simp)
      · exact absurd (mem_closedPorts (hout ▸ hc)) h2

theorem Inv.reply {h : Host} {cfg : Config} {s : RtState} (hi : Inv h cfg s) (tag : CallTag)
    (r : Reply) : Inv h cfg (replyStep h s tag r).1 := by
  simp only [replyStep]
  generalize tag.domain = d
  cases d
  case shell =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => Run.Shell.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case intent =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Intent.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case inc =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Inc.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case theme =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => Run.Theme.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case identity =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Identity.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case relay =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Relay.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case storage =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Storage.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case keys =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Keys.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case media =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Media.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case notify =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Notify.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case resource =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Resource.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case config =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Config.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case upload =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Upload.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, trivial⟩
  case value => exact hi
  case outbox =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Outbox.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩
  case cvm => exact hi
  case link =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Link.onReply_mentions _ _ _ _ _ _ h1, trivial⟩
  case pow => exact hi
  case display =>
    apply Inv.of_mentions hi; rfl; rfl; intro q; simp only [mentionsList, Pw]
    exact ⟨fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => Run.Display.onReply_mentions _ _ _ _ _ _ h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, fun h1 => .inl h1, trivial⟩

theorem Inv.event {h : Host} {cfg : Config} {s : RtState} (hi : Inv h cfg s) (e : HostEvent) :
    Inv h cfg (eventStep h s e).1 := by
  apply Inv.of_mentions hi; rfl; rfl
  intro q
  simp only [mentionsList, eventStep, Pw]
  exact ⟨fun h1 => Run.Shell.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Theme.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Identity.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Storage.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Inc.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Intent.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Notify.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Display.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Keys.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Relay.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Outbox.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Media.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Config.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Resource.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Upload.onEvent_mentions _ _ _ _ _ h1, fun h1 => Run.Link.onEvent_mentions _ _ _ _ _ h1, trivial⟩

theorem Inv.init (h : Host) (cfg : Config) : Inv h cfg (.init cfg) where
  shell := Napplet.Inv.init _ _
  ports := by simp [RtState.init, ShellState.init]
  clean := by
    intro p _
    simp [mentions, mentionsList, RtState.init, Run.Shell.St.init, Run.Shell.mentions, Run.Theme.St.init, Run.Theme.mentions, Run.Identity.St.init, Run.Identity.mentions, Run.Storage.St.init, Run.Storage.mentions, Run.Inc.St.init, Run.Inc.mentions, Run.Intent.St.init, Run.Intent.mentions, Run.Notify.St.init, Run.Notify.mentions, Run.Notify.ports, Run.Display.St.init, Run.Display.mentions, Run.Keys.St.init, Run.Keys.mentions, Run.Relay.St.init, Run.Relay.mentions, Run.Outbox.St.init, Run.Outbox.mentions, Run.Media.St.init, Run.Media.mentions, Run.Config.St.init, Run.Config.mentions, Run.Resource.St.init, Run.Resource.mentions, Run.Upload.St.init, Run.Upload.mentions, Run.Link.St.init, Run.Link.mentions]

theorem Inv.step {h : Host} {cfg : Config} {s : RtState} (hi : Inv h cfg s) (i : Input) :
    Inv h cfg (step h cfg s i).1 := by
  cases i with
  | create w m bytes inst =>
    apply Inv.browser
    split
    · exact ⟨hi.shell, hi.ports, hi.clean⟩
    · exact hi
  | load w => exact hi.browser _
  | hello w ports => exact hi.browser _
  | windowMsg w => exact hi.browser _
  | portClosed p => exact hi.browser _
  | grant p g => exact hi.browser _
  | message p j => exact hi.message p j
  | reply tag r => exact hi.reply tag r
  | event e => exact hi.event e
  | tick now => exact ⟨hi.shell, hi.ports, hi.clean⟩

theorem Reachable.inv {h : Host} {cfg : Config} {s : RtState} (hr : Reachable h cfg s) :
    Inv h cfg s := by
  induction hr with
  | init => exact Inv.init h cfg
  | step i _ ih => exact ih.step i

/-! ### Headline properties over the composed machine -/

/-- Teardown clears every NAP's per-endpoint state: in every reachable state no
component holds anything for a port that is not bound. -/
theorem teardown_clears {h : Host} {cfg : Config} {s : RtState} (hr : Reachable h cfg s)
    {p : PortId} (hb : s.shell.bindings p = none) : mentions s p = false :=
  hr.inv.clean p hb

/-- The NIP-5D shell invariant holds in every reachable composed state. -/
theorem shell_inv {h : Host} {cfg : Config} {s : RtState} (hr : Reachable h cfg s) :
    Napplet.Inv h.crypto cfg.shell s.shell :=
  hr.inv.shell

theorem flushStep_shell (h : Host) (s : RtState) : (flushStep h s).1.shell = s.shell := by
  simp only [flushStep]

/-- A port closing tears the endpoint down everywhere: the binding and grants are
gone, the frame is removed, `closePort` is emitted, and no component keeps state
for the port. -/
theorem port_closed_teardown {h : Host} {cfg : Config} {s : RtState} (hr : Reachable h cfg s)
    {p : PortId} {b : Binding} (hb : s.shell.bindings p = some b) :
    let r := step h cfg s (.portClosed p)
    r.1.shell.bindings p = none ∧ r.1.shell.grants p = [] ∧
    r.1.shell.frames b.window = some .removed ∧ Output.closePort p ∈ r.2 ∧
    mentions r.1 p = false := by
  have hr' := Reachable.step (.portClosed p) hr
  obtain ⟨ld, hf⟩ := (shell_inv hr).bind_frame p b hb
  have hsh : (step h cfg s (.portClosed p)).1.shell =
      (Napplet.step h.crypto cfg.shell s.shell (.portClosed p)).1 := by
    simp only [step, browserStep]
    rw [flushStep_shell]
    exact (dropPorts_shell _ _).1
  have hout : Output.closePort p ∈ (step h cfg s (.portClosed p)).2 := by
    simp [step, browserStep, Napplet.step, hb, revoke, hf, ofShell]
  have hn : (step h cfg s (.portClosed p)).1.shell.bindings p = none := by
    rw [hsh]; simp [Napplet.step, hb, revoke, hf]
  refine ⟨hn, ?_, ?_, hout, teardown_clears hr' hn⟩
  · rw [hsh]; simp [Napplet.step, hb, revoke, hf]
  · rw [hsh]; simp [Napplet.step, hb, revoke, hf]

end Napplet.Runtime
