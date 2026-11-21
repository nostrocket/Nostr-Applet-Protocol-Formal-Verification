/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Run.Shell
import Napplet.Run.Theme
import Napplet.Run.Identity
import Napplet.Run.Storage

/-!
# The composed runtime

`Runtime.step` is the whole shell: one input in (a browser event, a JSON message on
a port, a host reply or event, a clock tick), a list of outputs out (JSON messages
on ports, browser actions, host calls and effects).

* Browser events go to `Shell.step` (NIP-5D transport and identity).
* A JSON message on port `p` becomes an envelope `{type, id}`; `Shell.step` decides
  whether it is processed at all (bound port, known and exposed domain). If it is,
  the domain's component decodes the full JSON and handles it with the endpoint
  context `Ctx.ofBinding` derived from the binding.
* Every `closePort` the shell emits tears the endpoint down in every component.
* Host replies are routed by the call tag's domain; host events go to every
  component.

Main results (`Runtime.Inv`, over every reachable state):
* the NIP-5D shell invariant (`Shell.Inv`) holds;
* no component holds state for a port that is not bound, so teardown clears every
  NAP's per-endpoint state and a later binding of the same port starts clean;
* JSON on an unbound port, or with an unknown or unexposed type, produces nothing.
-/

namespace Napplet.Runtime

/-- Shell policy and per-NAP configuration. -/
structure Config where
  shell : ShellConfig
  storageQuota : Nat := NapStorage.defaultQuota

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

def RtState.init (cfg : Config) : RtState where
  shell := .init
  inst := fun _ => 0
  ports := []
  now := 0
  user := ""
  shellNap := .init
  theme := .init
  identity := .init
  storage := .init cfg.storageQuota

inductive Input where
  /-- Run manifest `m` with fetched artifact `bytes` in new window `w` (NIP-5D
  §Identity step 2); `inst` is the host's stable instance id for this window. -/
  | create (w : WindowId) (m : ManifestEvent) (bytes : Bytes) (inst : Nat)
  | load (w : WindowId)
  /-- `{type: "napplet.hello"}` from window `w` with these transferred ports. -/
  | hello (w : WindowId) (ports : List PortId)
  /-- Any other window-level message from window `w`. -/
  | windowMsg (w : WindowId)
  | portClosed (p : PortId)
  | grant (p : PortId) (g : Grant)
  /-- A message posted on port `p` (structured clone of a JSON value). -/
  | message (p : PortId) (msg : Json)
  | reply (tag : CallTag) (r : Reply)
  | event (e : HostEvent)
  | tick (now : Nat)

inductive Output where
  | send (to : PortId) (msg : Json)
  | rejected (w : WindowId) (e : ManifestError)
  /-- Create the `srcdoc` iframe for `w` with `sandbox="allow-scripts"`, the verified
  bytes, the bootstrap, and a `window.napplet` namespace holding exactly `exposed`. -/
  | iframeCreated (w : WindowId) (id : Identity) (exposed : List Domain)
  | bound (w : WindowId) (p : PortId) (id : Identity)
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

/-- Any component holds state for port `p`. -/
def mentions (s : RtState) (p : PortId) : Bool :=
  Run.Shell.mentions s.shellNap p || Run.Theme.mentions s.theme p ||
  Run.Identity.mentions s.identity p || Run.Storage.mentions s.storage p

/-! ### Steps -/

def lift {α σ : Type} (dec : Decoded α) (port : PortId) (run : α → σ × List Eff)
    (set : σ → RtState) (s : RtState) : RtState × List Output :=
  match dec with
  | .ok r => let (st, effs) := run r; (set st, effs.map ofEff)
  | .reject rs => (s, rs.map (.send port))
  | .unknown => (s, [])

/-- Hand a decoded JSON message to domain `d`'s component. -/
def napStep (h : Host) (w : World) (cx : Ctx) (s : RtState) (j : Json) : Domain → RtState × List Output
  | .shell => lift (Run.Shell.decode j) cx.port (Run.Shell.handle h w cx s.shellNap)
      (fun st => { s with shellNap := st }) s
  | .theme => lift (Run.Theme.decode j) cx.port (Run.Theme.handle h w cx s.theme)
      (fun st => { s with theme := st }) s
  | .identity => lift (Run.Identity.decode j) cx.port (Run.Identity.handle h w cx s.identity)
      (fun st => { s with identity := st }) s
  | .storage => lift (Run.Storage.decode j) cx.port (Run.Storage.handle h w cx s.storage)
      (fun st => { s with storage := st }) s
  | _ => (s, [])

/-- Tear endpoint `p` down in every component. -/
def dropAll (s : RtState) (p : PortId) : RtState × List Output :=
  let (a, ea) := Run.Shell.drop s.shellNap p
  let (b, eb) := Run.Theme.drop s.theme p
  let (c, ec) := Run.Identity.drop s.identity p
  let (d, ed) := Run.Storage.drop s.storage p
  ({ s with shellNap := a, theme := b, identity := c, storage := d },
   (ea ++ eb ++ ec ++ ed).map ofEff)

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

/-- A browser event: the NIP-5D shell, then teardown of every closed port. -/
def browserStep (h : Host) (cfg : Config) (s : RtState) (e : Event) : RtState × List Output :=
  let (sh, outs) := Napplet.step h.crypto cfg.shell s.shell e
  let s1 := { s with shell := sh, ports := boundPorts outs ++ s.ports }
  let (s2, drops) := dropPorts s1 (closedPorts outs)
  (s2, outs.flatMap ofShell ++ drops)

def replyStep (h : Host) (s : RtState) (tag : CallTag) (r : Reply) : RtState × List Output :=
  let w := world s
  match tag.domain with
  | .identity =>
    let (st, effs) := Run.Identity.onReply h w s.identity tag.n r
    ({ s with identity := st }, effs.map ofEff)
  | _ => (s, [])

def newUser (s : RtState) : HostEvent → String
  | .userChanged pk => pk
  | _ => s.user

def eventStep (h : Host) (s : RtState) (e : HostEvent) : RtState × List Output :=
  let w := world s
  let (th, e1) := Run.Theme.onEvent h w s.theme e
  let (idn, e2) := Run.Identity.onEvent h w s.identity e
  ({ s with theme := th, identity := idn, user := newUser s e }, (e1 ++ e2).map ofEff)

/-- The composed transition function. -/
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

theorem ctxOf_live {s : RtState} {p : PortId} {cx : Ctx} (hi : ∀ p b, s.shell.bindings p = some b → p ∈ s.ports)
    (h : ctxOf s p = some cx) : cx ∈ (world s).live := by
  simp only [world, List.mem_filterMap]
  simp only [ctxOf, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, _⟩ := h
  exact ⟨p, hi p b hb, by simp [ctxOf, hb]; assumption⟩

theorem ctxOf_port {s : RtState} {p : PortId} {cx : Ctx} (h : ctxOf s p = some cx) : cx.port = p := by
  simp only [ctxOf, Option.map_eq_some_iff] at h
  obtain ⟨b, -, rfl⟩ := h
  rfl

/-- Clean after one component changes: its new mentions are old ones or bound ports. -/
theorem mentions_cases {s s' : RtState} {q : PortId}
    (h : mentions s' q = true)
    (hsh : Run.Shell.mentions s'.shellNap q = true → Run.Shell.mentions s.shellNap q = true ∨ (world s).bound q)
    (hth : Run.Theme.mentions s'.theme q = true → Run.Theme.mentions s.theme q = true ∨ (world s).bound q)
    (hid : Run.Identity.mentions s'.identity q = true → Run.Identity.mentions s.identity q = true ∨ (world s).bound q)
    (hst : Run.Storage.mentions s'.storage q = true → Run.Storage.mentions s.storage q = true ∨ (world s).bound q) :
    mentions s q = true ∨ (world s).bound q := by
  simp only [mentions, Bool.or_eq_true] at h ⊢
  rcases h with ((h | h) | h) | h
  · rcases hsh h with h | h
    · exact .inl (.inl (.inl (.inl h)))
    · exact .inr h
  · rcases hth h with h | h
    · exact .inl (.inl (.inl (.inr h)))
    · exact .inr h
  · rcases hid h with h | h
    · exact .inl (.inl (.inr h))
    · exact .inr h
  · rcases hst h with h | h
    · exact .inl (.inr h)
    · exact .inr h

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
        have hport := ctxOf_port hcx
        -- only one component changes, and shell state is untouched
        have key : ∀ s' : RtState, s'.shell = s.shell → s'.ports = s.ports →
            (∀ q, mentions s' q = true → mentions s q = true ∨ (world s).bound q) → Inv h cfg s' := by
          intro s' hsh hpo hm
          refine ⟨hsh ▸ hi.shell, hsh ▸ hpo ▸ hi.ports, ?_⟩
          intro q hq
          rw [hsh] at hq
          cases hmq : mentions s' q
          · rfl
          · rcases hm q hmq with h1 | h1
            · rw [hi.clean q hq] at h1; exact absurd h1 (by simp)
            · obtain ⟨b, hb⟩ := world_bound h1; rw [hq] at hb; simp at hb
        apply key
        · cases d <;> simp only [napStep, lift] <;> split <;> rfl
        · cases d <;> simp only [napStep, lift] <;> split <;> rfl
        · intro q hq
          cases d <;> simp only [napStep, lift] at hq
          all_goals first
            | exact .inl hq
            | (split at hq
               · exact mentions_cases hq
                  (fun h1 => Run.Shell.handle_mentions _ _ _ _ _ _ hlive h1)
                  (fun h1 => .inl h1) (fun h1 => .inl h1) (fun h1 => .inl h1)
               · exact .inl hq
               · exact .inl hq)
            | (split at hq
               · exact mentions_cases hq (fun h1 => .inl h1)
                  (fun h1 => by simp [Run.Theme.mentions] at h1) (fun h1 => .inl h1) (fun h1 => .inl h1)
               · exact .inl hq
               · exact .inl hq)
            | (split at hq
               · exact mentions_cases hq (fun h1 => .inl h1) (fun h1 => .inl h1)
                  (fun h1 => Run.Identity.handle_mentions _ _ _ _ _ _ hlive h1) (fun h1 => .inl h1)
               · exact .inl hq
               · exact .inl hq)
            | (split at hq
               · exact mentions_cases hq (fun h1 => .inl h1) (fun h1 => .inl h1) (fun h1 => .inl h1)
                  (fun h1 => by simp [Run.Storage.mentions] at h1)
               · exact .inl hq
               · exact .inl hq)
      · exact hi
    · exact hi

/-! ### Teardown lemmas -/

theorem dropAll_shell (s : RtState) (p : PortId) :
    (dropAll s p).1.shell = s.shell ∧ (dropAll s p).1.ports = s.ports ∧
    (dropAll s p).1.inst = s.inst := ⟨rfl, rfl, rfl⟩

theorem dropAll_mentions (s : RtState) (p q : PortId) (h : mentions (dropAll s p).1 q = true) :
    mentions s q = true ∧ q ≠ p := by
  have a := Run.Shell.drop_mentions s.shellNap p q
  have b := Run.Identity.drop_mentions s.identity p q
  have c := Run.Shell.drop_clears s.shellNap p
  have d := Run.Identity.drop_clears s.identity p
  simp only [dropAll, mentions, Run.Theme.mentions, Run.Storage.mentions, Bool.or_false,
    Bool.false_or, Bool.or_eq_true] at h a b c d ⊢
  rcases h with h | h
  · exact ⟨.inl (a h), by rintro rfl; rw [c] at h; simp at h⟩
  · exact ⟨.inr (b h), by rintro rfl; rw [d] at h; simp at h⟩

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

theorem Inv.browser {h : Host} {cfg : Config} {s : RtState} (hi : Inv h cfg s) (e : Event) :
    Inv h cfg (browserStep h cfg s e).1 := by
  simp only [browserStep]
  generalize hst : Napplet.step h.crypto cfg.shell s.shell e = r
  obtain ⟨sh, outs⟩ := r
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
  split
  · refine ⟨hi.shell, hi.ports, ?_⟩
    intro q hq
    cases hm : mentions { s with identity := (Run.Identity.onReply h (world s) s.identity tag.n r).1 } q
    · rfl
    · rcases mentions_cases (s := s) hm (fun h1 => .inl h1) (fun h1 => .inl h1)
        (fun h1 => Run.Identity.onReply_mentions _ _ _ _ _ _ h1) (fun h1 => .inl h1) with h1 | h1
      · rw [hi.clean q hq] at h1; simp at h1
      · obtain ⟨b, hb⟩ := world_bound h1; simp_all
  · exact hi

theorem Inv.event {h : Host} {cfg : Config} {s : RtState} (hi : Inv h cfg s) (e : HostEvent) :
    Inv h cfg (eventStep h s e).1 := by
  refine ⟨hi.shell, hi.ports, ?_⟩
  intro q hq
  have hq' : s.shell.bindings q = none := hq
  cases hm : mentions (eventStep h s e).1 q
  · rfl
  · simp only [eventStep] at hm
    rcases mentions_cases (s := s) hm
        (fun h1 => .inl h1) (fun h1 => by simp [Run.Theme.mentions] at h1)
        (fun h1 => Run.Identity.onEvent_mentions _ _ _ _ _ h1) (fun h1 => .inl h1) with h1 | h1
    · rw [hi.clean q hq'] at h1; simp at h1
    · obtain ⟨b, hb⟩ := world_bound h1; rw [hq'] at hb; simp at hb

theorem Inv.init (h : Host) (cfg : Config) : Inv h cfg (.init cfg) where
  shell := Napplet.Inv.init _ _
  ports := by simp [RtState.init, ShellState.init]
  clean := by
    intro p _
    simp [mentions, RtState.init, Run.Shell.St.init, Run.Shell.mentions, Run.Theme.mentions,
      Run.Identity.St.init, Run.Identity.mentions, Run.Storage.mentions]

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
    exact (dropPorts_shell _ _).1
  have hout : Output.closePort p ∈ (step h cfg s (.portClosed p)).2 := by
    simp [step, browserStep, Napplet.step, hb, revoke, hf, ofShell]
  have hn : (step h cfg s (.portClosed p)).1.shell.bindings p = none := by
    rw [hsh]; simp [Napplet.step, hb, revoke, hf]
  refine ⟨hn, ?_, ?_, hout, teardown_clears hr' hn⟩
  · rw [hsh]; simp [Napplet.step, hb, revoke, hf]
  · rw [hsh]; simp [Napplet.step, hb, revoke, hf]

end Napplet.Runtime
