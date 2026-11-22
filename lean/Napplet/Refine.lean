/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Runtime
import Napplet.FMap

/-!
# The finite representation ports copy (`RtState'`)

`Runtime.RtState` uses functions for its maps (`frames`, `bindings`, `grants`, `inst`,
`names`, NAP-STORAGE's store, NAP-CONFIG's schemas and values, NAP-DISPLAY's
framebuffer). A shell cannot store a function, so this file gives the representation an
implementation should copy, `RtState'`, in which every one of them is finite:

* `FMap` (an association list with a default) for every map;
* the shell's removed windows as canonical intervals (`Ivs`), live frames in an `FMap`;
* every other field exactly as in `RtState` (lists, numbers and the components' static
  configuration).

`abs : RtState' → RtState` reads the finite maps as functions. `step'` runs one input:
it applies `Runtime.step` to `abs s` and re-tabulates every map on the keys the input
can touch (the old keys, the windows and ports the input and the shell's outputs name,
the scopes of the endpoint the message came from, and the pixels of a `display.push`).
Main results:

* `abs_step'`: `abs (step' s i).1 = (Runtime.step (abs s) i).1`, and `step'_outputs`:
  the outputs are the same, so every theorem about `Runtime.step` holds of `step'`;
* `WF.step'`: the representation stays canonical (distinct keys, no default-valued
  entries, canonical intervals);
* `Reachable'.abs`: every state `step'` reaches from `init'` is `abs` of a reachable
  `RtState`, so `Runtime.Reachable.inv` and every headline theorem apply;
* `live_keys`, `bindings_keys`, `grants_keys`, `inst_keys`, `ports_bound`,
  `removed_length_le`: memory follows live state. Every key of a per-window or per-port
  map is a live window or a bound port, `ports` lists bound ports without repetition,
  and the removed windows take at most one interval more than there are live windows
  when the host numbers windows consecutively.

The frame lemmas in the first half are the proof obligations: each says a field of the
state changes only at the keys `step'` re-tabulates.
-/

namespace Napplet

/-! ## Shell frame lemmas -/

section shell
variable {c : Crypto} {cfg : ShellConfig} {s : ShellState}

/-- Windows an event names. -/
def Event.wins : Event → List WindowId
  | .create w _ _ | .load w | .hello w _ | .windowMsg w => [w]
  | _ => []

/-- Ports an event names. -/
def Event.ports : Event → List PortId
  | .hello _ ps => ps
  | .portClosed p | .grant p _ | .nap p _ => [p]
  | _ => []

theorem revoke_frames_frame (w w' : WindowId) :
    (revoke s w').1.frames w = s.frames w ∨ Output.removeFrame w ∈ (revoke s w').2 := by
  unfold revoke
  split
  · by_cases hw : w = w'
    · subst hw; simp
    · simp [upd, hw]
  · by_cases hw : w = w'
    · subst hw; simp
    · simp [upd, hw]
  · exact .inl rfl

theorem revoke_grants_frame (q : PortId) (w' : WindowId) :
    (revoke s w').1.grants q = s.grants q ∨ Output.closePort q ∈ (revoke s w').2 := by
  unfold revoke
  split
  · rename_i p _ _
    by_cases hq : q = p
    · subst hq; simp
    · simp [upd, hq]
  · exact .inl rfl
  · exact .inl rfl

/-- A frame changes only at a window the event names or one the shell removes. -/
theorem step_frames_frame (e : Event) (w : WindowId) :
    (step c cfg s e).1.frames w = s.frames w ∨ w ∈ e.wins ∨
      Output.removeFrame w ∈ (step c cfg s e).2 := by
  cases e with
  | create w' m bytes =>
    simp only [step]
    split
    · exact .inl rfl
    · split
      · exact .inl rfl
      · by_cases hw : w = w'
        · subst hw; exact .inr (.inl (by simp [Event.wins]))
        · simp [upd, hw]
  | load w' =>
    by_cases hw : w = w'
    · subst hw; exact .inr (.inl (by simp [Event.wins]))
    simp only [step]
    split
    · simp [upd, hw]
    · rcases revoke_frames_frame (s := s) w w' with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · exact .inl rfl
  | hello w' ports =>
    by_cases hw : w = w'
    · subst hw; exact .inr (.inl (by simp [Event.wins]))
    simp only [step]
    split
    · split
      · split
        · simp [upd, hw]
        · exact .inl rfl
      · exact .inl rfl
    · rcases revoke_frames_frame (s := s) w w' with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · exact .inl rfl
  | windowMsg w' =>
    simp only [step]
    split
    · rcases revoke_frames_frame (s := s) w w' with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · exact .inl rfl
  | portClosed p =>
    simp only [step]
    split
    · rename_i b _
      rcases revoke_frames_frame (s := s) w b.window with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · exact .inl rfl
  | nap p env => exact .inl (by rw [step_nap_state])
  | grant p g =>
    simp only [step]
    split <;> exact .inl rfl

/-- A binding changes only at a port the shell binds or closes. -/
theorem step_bindings_frame (e : Event) (q : PortId) :
    (step c cfg s e).1.bindings q = s.bindings q ∨ Output.closePort q ∈ (step c cfg s e).2 ∨
      ∃ w id, Output.bound w q id ∈ (step c cfg s e).2 := by
  cases hq : (step c cfg s e).1.bindings q with
  | none =>
    rcases step_unbind e hq with h | h
    · exact .inl h.symm
    · exact .inr (.inl h)
  | some b =>
    rcases step_bind e hq with h | h
    · exact .inl h.symm
    · exact .inr (.inr h)

/-- Grants change only at a port the event names or the shell closes. -/
theorem step_grants_frame (e : Event) (q : PortId) :
    (step c cfg s e).1.grants q = s.grants q ∨ q ∈ e.ports ∨
      Output.closePort q ∈ (step c cfg s e).2 := by
  cases e with
  | create w' m bytes =>
    simp only [step]
    split
    · exact .inl rfl
    · split <;> exact .inl rfl
  | load w' =>
    simp only [step]
    split
    · exact .inl rfl
    · rcases revoke_grants_frame (s := s) q w' with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · exact .inl rfl
  | hello w' ports =>
    simp only [step]
    split
    · split
      · split <;> exact .inl rfl
      · exact .inl rfl
    · rcases revoke_grants_frame (s := s) q w' with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · exact .inl rfl
  | windowMsg w' =>
    simp only [step]
    split
    · rcases revoke_grants_frame (s := s) q w' with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · exact .inl rfl
  | portClosed p =>
    simp only [step]
    split
    · rename_i b _
      rcases revoke_grants_frame (s := s) q b.window with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · exact .inl rfl
  | nap p env => exact .inl (by rw [step_nap_state])
  | grant p g =>
    by_cases hq : q = p
    · subst hq; exact .inr (.inl (by simp [Event.ports]))
    simp only [step]
    split
    · simp [upd, hq]
    · exact .inl rfl

end shell

/-! ## Component frame lemmas -/

namespace Run.Config

theorem handle_frame (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) {sc : NapStorage.Scope}
    (hsc : sc ≠ scopeOf cx) :
    (handle h w cx s r).1.schemas sc = s.schemas sc ∧ (handle h w cx s r).1.values sc = s.values sc := by
  cases r with
  | registerSchema id schema version =>
    simp only [handle]
    split
    · exact ⟨rfl, rfl⟩
    · simp [upd, hsc]
  | get id => exact ⟨rfl, rfl⟩
  | subscribe => exact ⟨rfl, rfl⟩
  | unsubscribe => exact ⟨rfl, rfl⟩
  | openSettings sec =>
    simp only [handle]
    split <;> exact ⟨rfl, rfl⟩

theorem onEvent_schemas (h : Host) (w : World) (s : St) (e : HostEvent) :
    (onEvent h w s e).1.schemas = s.schemas := by
  simp only [onEvent]
  split
  · simp only [edited]
    split
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
    · rfl
  · rfl

theorem onEvent_frame (h : Host) (w : World) (s : St) (e : HostEvent) {sc : NapStorage.Scope}
    (hsc : sc ∉ w.live.map scopeOf) :
    (onEvent h w s e).1.schemas = s.schemas ∧ (onEvent h w s e).1.values sc = s.values sc := by
  simp only [onEvent]
  split
  · simp only [edited]
    split
    · split
      · exact ⟨rfl, rfl⟩
      · rename_i c hc
        have hm : c ∈ w.live := List.mem_of_find?_eq_some hc
        have hne : sc ≠ scopeOf c := fun he => hsc (he ▸ List.mem_map_of_mem hm)
        split
        · exact ⟨rfl, rfl⟩
        · split
          · exact ⟨rfl, rfl⟩
          · simp [upd, hne]
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

end Run.Config

namespace Run.Display

/-- The pixels a decoded request may write. -/
def touched : Req → List (String × (Nat × Nat))
  | .push _ did ps => ps.map fun p => (did, (p.x, p.y))
  | .list _ => []

theorem push_ok_fb {env : NapDisplay.DisplayEnv} {fb fb' : NapDisplay.Framebuffer} {sender : Endpoint}
    {did : String} {ps : List NapDisplay.Pixel} (h : NapDisplay.push env fb sender did ps = (fb', none)) :
    fb' = NapDisplay.applyPixels fb did ps := by
  unfold NapDisplay.push at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Prod.mk.injEq] at h; exact h.1.symm

theorem handle_fb_frame (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) {d : String}
    {xy : Nat × Nat} (hk : (d, xy) ∉ touched r) : (handle h w cx s r).1.fb d xy = s.fb d xy := by
  cases r with
  | list id => rfl
  | push id did ps =>
    by_cases hoff : (s.devices.any (·.id == did) && s.offline.contains did) = true
    · simp only [handle, hoff, ↓reduceIte]
    · rcases hpush : NapDisplay.push (env s cx) s.fb cx.port did ps with ⟨fb', _ | e⟩
      · simp only [handle, hoff, hpush, Bool.false_eq_true, ↓reduceIte]
        rw [push_ok_fb hpush]
        by_cases hd : d = did
        · subst hd
          apply NapDisplay.applyPixels_untouched
          intro hm
          apply hk
          simp only [touched, List.mem_map] at hm ⊢
          obtain ⟨p, hp, he⟩ := hm
          exact ⟨p, hp, by rw [he]⟩
        · rw [NapDisplay.applyPixels_other_display _ _ _ _ hd]
      · simp only [handle, hoff, hpush, Bool.false_eq_true, ↓reduceIte]

theorem onEvent_fb (h : Host) (w : World) (s : St) (e : HostEvent) :
    (onEvent h w s e).1.fb = s.fb := by
  simp only [onEvent]; split <;> rfl

end Run.Display

namespace Runtime

/-! ## Runtime frame lemmas -/

/-- The NIP-5D event a browser input carries. -/
def Input.event? : Input → Option Event
  | .create w m bytes _ => some (.create w m bytes)
  | .load w => some (.load w)
  | .hello w ps => some (.hello w ps)
  | .windowMsg w => some (.windowMsg w)
  | .portClosed p => some (.portClosed p)
  | .grant p g => some (.grant p g)
  | _ => none

/-- Windows an input names. -/
def Input.wins : Input → List WindowId
  | .create w .. | .load w | .hello w _ | .windowMsg w => [w]
  | _ => []

/-- Ports an input names. -/
def Input.ports : Input → List PortId
  | .hello _ ps => ps
  | .portClosed p | .grant p _ => [p]
  | _ => []

/-- Windows the outputs remove or refuse. -/
def outWins : List Output → List WindowId
  | [] => []
  | .removeFrame w :: os | .rejected w _ :: os => w :: outWins os
  | _ :: os => outWins os

/-- Ports the outputs bind or close. -/
def outPorts : List Output → List PortId
  | [] => []
  | .closePort p :: os | .bound _ p _ :: os => p :: outPorts os
  | _ :: os => outPorts os

theorem mem_outWins {os : List Output} {w : WindowId}
    (h : Output.removeFrame w ∈ os ∨ ∃ e, Output.rejected w e ∈ os) : w ∈ outWins os := by
  induction os with
  | nil => rcases h with h | ⟨_, h⟩ <;> simp at h
  | cons o os ih =>
    rcases h with h | ⟨e, h⟩
    · rcases List.mem_cons.mp h with rfl | h
      · simp [outWins]
      · have := ih (.inl h); cases o <;> simp [outWins, this]
    · rcases List.mem_cons.mp h with rfl | h
      · simp [outWins]
      · have := ih (.inr ⟨e, h⟩); cases o <;> simp [outWins, this]

theorem mem_outPorts {os : List Output} {p : PortId}
    (h : Output.closePort p ∈ os ∨ ∃ w id, Output.bound w p id ∈ os) : p ∈ outPorts os := by
  induction os with
  | nil => rcases h with h | ⟨_, _, h⟩ <;> simp at h
  | cons o os ih =>
    rcases h with h | ⟨w, id, h⟩
    · rcases List.mem_cons.mp h with rfl | h
      · simp [outPorts]
      · have := ih (.inl h); cases o <;> simp [outPorts, this]
    · rcases List.mem_cons.mp h with rfl | h
      · simp [outPorts]
      · have := ih (.inr ⟨w, id, h⟩); cases o <;> simp [outPorts, this]

/-- Scopes of the endpoint a message comes from (both selectors), or of every live
endpoint for a host event. -/
def scopesAt (s : RtState) : Input → List NapStorage.Scope
  | .message p _ =>
    match ctxOf s p with
    | some cx => [NapStorage.scopeFor cx.storage .shared, NapStorage.scopeFor cx.storage .inst]
    | none => []
  | .event _ => (world s).live.map Run.Config.scopeOf
  | _ => []

/-- Pixels a `display.push` message names. -/
def pixelsAt : Input → List (String × (Nat × Nat))
  | .message _ j =>
    match Run.Display.decode j with
    | .ok r => Run.Display.touched r
    | _ => []
  | _ => []

theorem clearInst_other (f : WindowId → Nat) : ∀ (ws : List WindowId) (w : WindowId),
    w ∉ ws → clearInst f ws w = f w
  | [], _, _ => rfl
  | v :: ws, w, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [clearInst]
    rw [clearInst_other _ ws w h.2]
    simp [upd, h.1]

theorem mem_removedFrames {os : List Napplet.Output} {w : WindowId} (h : w ∈ removedFrames os) :
    Napplet.Output.removeFrame w ∈ os ∨ ∃ e, Napplet.Output.rejected w e ∈ os := by
  induction os with
  | nil => simp [removedFrames] at h
  | cons o os ih =>
    cases o with
    | removeFrame v =>
      simp only [removedFrames, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · rcases ih h with h | ⟨e, h⟩
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr ⟨e, List.mem_cons_of_mem _ h⟩
    | rejected v e =>
      simp only [removedFrames, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inr ⟨e, by simp⟩
      · rcases ih h with h | ⟨e, h⟩
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr ⟨e, List.mem_cons_of_mem _ h⟩
    | _ =>
      simp only [removedFrames] at h
      rcases ih h with h | ⟨e, h⟩
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr ⟨e, List.mem_cons_of_mem _ h⟩

theorem dropAll_fields (s : RtState) (p : PortId) :
    let r := (dropAll s p).1
    r.shell = s.shell ∧ r.inst = s.inst ∧ r.names = s.names ∧ r.storage = s.storage ∧
    r.config.schemas = s.config.schemas ∧ r.config.values = s.config.values ∧
    r.display = s.display := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dropPorts_fields (s : RtState) (ps : List PortId) :
    let r := (dropPorts s ps).1
    r.shell = s.shell ∧ r.inst = s.inst ∧ r.names = s.names ∧ r.storage = s.storage ∧
    r.config.schemas = s.config.schemas ∧ r.config.values = s.config.values ∧
    r.display = s.display := by
  induction ps generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [dropPorts]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ih (dropAll s p).1
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := dropAll_fields s p
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6, a7.trans b7⟩

/-- What a browser step does to the fields the refinement tabulates. -/
theorem browserStep_spec (h : Host) (cfg : Config) (s : RtState) (e : Event) :
    let r := browserStep h cfg s e
    let so := Napplet.step h.crypto cfg.shell s.shell e
    r.1.shell = so.1 ∧ r.1.inst = clearInst s.inst (removedFrames so.2) ∧ r.1.names = s.names ∧
    r.1.storage = s.storage ∧ r.1.config.schemas = s.config.schemas ∧
    r.1.config.values = s.config.values ∧ r.1.display = s.display ∧
    (∀ o ∈ so.2, ∀ x ∈ ofShell o, x ∈ r.2) := by
  rcases hso : Napplet.step h.crypto cfg.shell s.shell e with ⟨sh, outs⟩
  have hf := dropPorts_fields { s with shell := sh, ports := keepBound sh (boundPorts outs ++ s.ports), inst := clearInst s.inst (removedFrames outs) } (closedPorts outs)
  simp only [browserStep, hso, flushStep]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hf
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
  intro o ho x hx
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨o, ho, hx⟩))

theorem napStep_fields (h : Host) (w : World) (cx : Ctx) (s : RtState) (j : Json) (d : Domain) :
    let r := (napStep h w cx s j d).1
    r.shell = s.shell ∧ r.inst = s.inst ∧ r.names = s.names := by
  cases d <;> simp only [napStep, lift] <;> split <;> exact ⟨rfl, rfl, rfl⟩

theorem napStep_store (h : Host) (w : World) (cx : Ctx) (s : RtState) (j : Json) (d : Domain)
    (sc : NapStorage.Scope)
    (hsc : sc ≠ NapStorage.scopeFor cx.storage .shared ∧ sc ≠ NapStorage.scopeFor cx.storage .inst) :
    (napStep h w cx s j d).1.storage.store sc = s.storage.store sc := by
  cases d <;> simp only [napStep, lift] <;> split <;> try rfl
  rename_i r _
  refine Run.Storage.handle_isolated h w cx s.storage r ?_
  generalize r.sel = sel
  cases sel
  · exact hsc.1
  · exact hsc.2

theorem napStep_config (h : Host) (w : World) (cx : Ctx) (s : RtState) (j : Json) (d : Domain)
    (sc : NapStorage.Scope) (hsc : sc ≠ Run.Config.scopeOf cx) :
    (napStep h w cx s j d).1.config.schemas sc = s.config.schemas sc ∧
    (napStep h w cx s j d).1.config.values sc = s.config.values sc := by
  cases d <;> simp only [napStep, lift] <;> split <;> try exact ⟨rfl, rfl⟩
  exact Run.Config.handle_frame _ _ _ _ _ hsc

theorem napStep_fb (h : Host) (w : World) (cx : Ctx) (s : RtState) (j : Json) (d : Domain)
    (k : String × (Nat × Nat)) (hk : ∀ r, Run.Display.decode j = .ok r → k ∉ Run.Display.touched r) :
    (napStep h w cx s j d).1.display.fb k.1 k.2 = s.display.fb k.1 k.2 := by
  cases d <;> simp only [napStep, lift] <;> split <;> try rfl
  rename_i r hr
  exact Run.Display.handle_fb_frame _ _ _ _ _ (hk r hr)

theorem replyStep_fields (h : Host) (s : RtState) (tag : CallTag) (rep : Reply) :
    let r := (replyStep h s tag rep).1
    r.shell = s.shell ∧ r.inst = s.inst ∧ r.names = s.names ∧ r.storage.store = s.storage.store ∧
    r.config.schemas = s.config.schemas ∧ r.config.values = s.config.values ∧
    r.display.fb = s.display.fb := by
  simp only [replyStep]
  split <;> simp [Run.Storage.onReply, Run.Config.onReply, Run.Display.onReply]

theorem eventStep_fields (h : Host) (s : RtState) (e : HostEvent) :
    let r := (eventStep h s e).1
    r.shell = s.shell ∧ r.inst = s.inst ∧ r.names = s.names ∧ r.storage.store = s.storage.store ∧
    r.config.schemas = s.config.schemas ∧ r.display.fb = s.display.fb ∧
    ∀ sc, sc ∉ (world s).live.map Run.Config.scopeOf → r.config.values sc = s.config.values sc := by
  simp only [eventStep]
  exact ⟨trivial, trivial, trivial, rfl, Run.Config.onEvent_schemas _ _ _ _,
    Run.Display.onEvent_fb _ _ _ _, fun sc hsc => (Run.Config.onEvent_frame h (world s) s.config e hsc).2⟩

/-- The frame condition: `T` differs from `S` only at the keys `step'` re-tabulates. -/
structure Frame (S T : RtState) (i : Input) (outs : List Output) : Prop where
  frames : ∀ w, w ∉ i.wins → w ∉ outWins outs → T.shell.frames w = S.shell.frames w
  removed : ∀ w, S.shell.frames w = some .removed → T.shell.frames w = some .removed
  bindings : ∀ q, q ∉ outPorts outs → T.shell.bindings q = S.shell.bindings q
  grants : ∀ q, q ∉ i.ports → q ∉ outPorts outs → T.shell.grants q = S.shell.grants q
  inst : ∀ w, w ∉ i.wins → w ∉ outWins outs → T.inst w = S.inst w
  names : T.names = S.names
  store : ∀ sc, sc ∉ scopesAt S i → T.storage.store sc = S.storage.store sc
  schemas : ∀ sc, sc ∉ scopesAt S i → T.config.schemas sc = S.config.schemas sc
  values : ∀ sc, sc ∉ scopesAt S i → T.config.values sc = S.config.values sc
  fb : ∀ k, k ∉ pixelsAt i → T.display.fb k.1 k.2 = S.display.fb k.1 k.2

theorem Frame.of_eq {S T : RtState} {i : Input} {outs : List Output} (h1 : T.shell = S.shell)
    (h2 : T.inst = S.inst) (h3 : T.names = S.names) (h4 : T.storage.store = S.storage.store)
    (h5 : T.config.schemas = S.config.schemas) (h6 : T.config.values = S.config.values)
    (h7 : T.display.fb = S.display.fb) : Frame S T i outs where
  frames _ _ _ := by rw [h1]
  removed _ h := by rw [h1]; exact h
  bindings _ _ := by rw [h1]
  grants _ _ _ := by rw [h1]
  inst _ _ _ := by rw [h2]
  names := h3
  store _ _ := by rw [h4]
  schemas _ _ := by rw [h5]
  values _ _ := by rw [h6]
  fb _ _ := by rw [h7]

theorem step_browser (h : Host) (cfg : Config) (S : RtState) (i : Input) (e : Event)
    (he : i.event? = some e) :
    ∃ S0 : RtState, S0.shell = S.shell ∧ S0.names = S.names ∧ S0.storage = S.storage ∧
      S0.config = S.config ∧ S0.display = S.display ∧ (∀ w, w ∉ i.wins → S0.inst w = S.inst w) ∧
      e.wins ⊆ i.wins ∧ e.ports ⊆ i.ports ∧ step h cfg S i = browserStep h cfg S0 e ∧
      S0.ports = S.ports ∧
      (∀ w, S0.inst w ≠ S.inst w → S.shell.frames w = none ∧ ∃ m b, e = .create w m b) := by
  cases i with
  | create w m bytes inst =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    by_cases hn : (S.shell.frames w).isNone = true
    · refine ⟨{ S with inst := upd S.inst w inst }, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
      · intro v hv; simp only [Input.wins, List.mem_singleton] at hv; simp [upd, hv]
      · simp [Event.wins, Input.wins]
      · simp [Event.ports]
      · simp [step, hn]
      · intro v hv
        by_cases hvw : v = w
        · subst hvw; exact ⟨by simpa using hn, m, bytes, rfl⟩
        · simp [upd, hvw] at hv
    · refine ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_, ?_, ?_, rfl, fun _ h => absurd rfl h⟩
      · simp [Event.wins, Input.wins]
      · simp [Event.ports]
      · simp [step, hn]
  | load w =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins, Input.wins],
      by simp [Event.ports], rfl, rfl, fun _ h => absurd rfl h⟩
  | hello w ps =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins, Input.wins],
      by simp [Event.ports, Input.ports], rfl, rfl, fun _ h => absurd rfl h⟩
  | windowMsg w =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins, Input.wins],
      by simp [Event.ports], rfl, rfl, fun _ h => absurd rfl h⟩
  | portClosed p =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins],
      by simp [Event.ports, Input.ports], rfl, rfl, fun _ h => absurd rfl h⟩
  | grant p g =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins],
      by simp [Event.ports, Input.ports], rfl, rfl, fun _ h => absurd rfl h⟩
  | message p j => simp [Input.event?] at he
  | reply t r => simp [Input.event?] at he
  | event ev => simp [Input.event?] at he
  | tick n => simp [Input.event?] at he

theorem Frame.browser (h : Host) (cfg : Config) (S : RtState) (i : Input) (e : Event)
    (he : i.event? = some e) : Frame S (step h cfg S i).1 i (step h cfg S i).2 := by
  obtain ⟨S0, e1, e2, e3, e4, e5, e6, hw, hp, hstep, -, -⟩ := step_browser h cfg S i e he
  rw [hstep]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, bo⟩ := browserStep_spec h cfg S0 e
  have ho : ∀ o ∈ (Napplet.step h.crypto cfg.shell S.shell e).2, ∀ x ∈ ofShell o,
      x ∈ (browserStep h cfg S0 e).2 := by rw [← e1]; exact bo
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hwi hwo
    rw [b1, e1]
    rcases step_frames_frame (c := h.crypto) (cfg := cfg.shell) (s := S.shell) e w with h1 | h1 | h1
    · exact h1
    · exact absurd (hw h1) hwi
    · exact absurd (mem_outWins (.inl (ho _ h1 _ (by simp [ofShell])))) hwo
  · intro w hr
    rw [b1, e1]
    exact Napplet.removed_stays_removed e hr
  · intro q hq
    rw [b1, e1]
    rcases step_bindings_frame (c := h.crypto) (cfg := cfg.shell) (s := S.shell) e q with h1 | h1 | ⟨w, id, h1⟩
    · exact h1
    · exact absurd (mem_outPorts (.inl (ho _ h1 _ (by simp [ofShell])))) hq
    · exact absurd (mem_outPorts (.inr ⟨w, id, ho _ h1 _ (by simp [ofShell])⟩)) hq
  · intro q hqi hqo
    rw [b1, e1]
    rcases step_grants_frame (c := h.crypto) (cfg := cfg.shell) (s := S.shell) e q with h1 | h1 | h1
    · exact h1
    · exact absurd (hp h1) hqi
    · exact absurd (mem_outPorts (.inl (ho _ h1 _ (by simp [ofShell])))) hqo
  · intro w hwi hwo
    rw [b2, clearInst_other, e6 w hwi]
    intro hm
    rw [e1] at hm
    rcases mem_removedFrames hm with h1 | ⟨er, h1⟩
    · exact hwo (mem_outWins (.inl (ho _ h1 _ (by simp [ofShell]))))
    · exact hwo (mem_outWins (.inr ⟨er, ho _ h1 _ (by simp [ofShell])⟩))
  · rw [b3, e2]
  · intro sc _; rw [b4, e3]
  · intro sc _; rw [b5, e4]
  · intro sc _; rw [b6, e4]
  · intro k _; rw [b7, e5]

/-- Every input changes the tabulated fields only at the keys `step'` re-tabulates. -/
theorem step_frame (h : Host) (cfg : Config) (S : RtState) (i : Input) :
    Frame S (step h cfg S i).1 i (step h cfg S i).2 := by
  cases hi : i.event? with
  | some e => exact Frame.browser h cfg S i e hi
  | none =>
    cases i with
    | message p j =>
      simp only [step]
      split
      · exact Frame.of_eq rfl rfl rfl rfl rfl rfl rfl
      · split
        · rename_i env _ _ d _ _
          split
          · rename_i cx hcx
            obtain ⟨n1, n2, n3⟩ := napStep_fields h (world S) cx S j d
            have hsa : scopesAt S (.message p j) =
                [NapStorage.scopeFor cx.storage .shared, NapStorage.scopeFor cx.storage .inst] := by
              simp [scopesAt, hcx]
            refine ⟨?_, ?_, ?_, ?_, ?_, n3, ?_, ?_, ?_, ?_⟩
            · intro w _ _; rw [n1]
            · intro w hr; rw [n1]; exact hr
            · intro q _; rw [n1]
            · intro q _ _; rw [n1]
            · intro w _ _; rw [n2]
            · intro sc hsc
              rw [hsa] at hsc
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsc
              exact napStep_store h (world S) cx S j d sc hsc
            · intro sc hsc
              rw [hsa] at hsc
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsc
              exact (napStep_config h (world S) cx S j d sc hsc.1).1
            · intro sc hsc
              rw [hsa] at hsc
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsc
              exact (napStep_config h (world S) cx S j d sc hsc.1).2
            · intro k hk
              apply napStep_fb
              intro r hr hm
              apply hk
              simp only [pixelsAt, hr]
              exact hm
          · exact Frame.of_eq rfl rfl rfl rfl rfl rfl rfl
        · exact Frame.of_eq rfl rfl rfl rfl rfl rfl rfl
    | reply tag r =>
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := replyStep_fields h S tag r
      exact Frame.of_eq r1 r2 r3 r4 r5 r6 r7
    | event e =>
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := eventStep_fields h S e
      refine ⟨?_, ?_, ?_, ?_, ?_, r3, ?_, ?_, ?_, ?_⟩
      · intro w _ _; simp only [step]; rw [r1]
      · intro w hr; simp only [step]; rw [r1]; exact hr
      · intro q _; simp only [step]; rw [r1]
      · intro q _ _; simp only [step]; rw [r1]
      · intro w _ _; simp only [step]; rw [r2]
      · intro sc _; simp only [step]; rw [r4]
      · intro sc _; simp only [step]; rw [r5]
      · intro sc hsc; simp only [step]; exact r7 sc hsc
      · intro k _; simp only [step]; rw [r6]
    | tick n => exact Frame.of_eq rfl rfl rfl rfl rfl rfl rfl
    | _ => simp [Input.event?] at hi

end Runtime

end Napplet

namespace Napplet.Refine

open _root_.Napplet.Runtime NapStorage
open _root_.Napplet.Runtime (Output)

/-- Keep only live statuses (the removed ones live in `ShellState'.removed`). -/
def liveOnly : Option FrameStatus → Option FrameStatus
  | some (.live id ex p ld) => some (.live id ex p ld)
  | _ => none

/-- The shell state with finite maps: live frames, removed windows as intervals,
bindings and grants. -/
structure ShellState' where
  live : FMap WindowId (Option FrameStatus)
  removed : Ivs
  bindings : FMap PortId (Option Binding)
  grants : FMap PortId (List Grant)

def ShellState'.abs (s : ShellState') : ShellState where
  frames w := if s.removed.mem w then some .removed else s.live.get w
  bindings := s.bindings.get
  grants := s.grants.get

/-- NAP-STORAGE's component state with a finite store. -/
structure StorageSt' where
  store : FMap Scope KV
  quota : Nat
  keys : List Scope

/-- NAP-CONFIG's component state with finite schemas and values. -/
structure ConfigSt' where
  schemas : FMap Scope (Option Run.Config.Reg)
  values : FMap Scope (Option Json)
  subs : List PortId
  schemaKeys : List Scope
  valueKeys : List Scope

/-- NAP-DISPLAY's component state with a finite framebuffer keyed by (display, pixel). -/
structure DisplaySt' where
  cfg : Run.Display.Cfg
  devices : List NapDisplay.DisplayDevice
  offline : List String
  fb : FMap (String × (Nat × Nat)) NapDisplay.RGB

/-- The runtime state as a port stores it. Every map is finite; the other fields are
those of `RtState`. -/
structure RtState' where
  shell : ShellState'
  inst : FMap WindowId Nat
  ports : List PortId
  now : Nat
  user : String
  names : FMap WindowId (Option String)
  shellNap : Run.Shell.St
  theme : Run.Theme.St
  identity : Run.Identity.St
  storage : StorageSt'
  inc : Run.Inc.St
  intent : Run.Intent.St
  notify : Run.Notify.St
  display : DisplaySt'
  keys : Run.Keys.St
  relay : Run.Relay.St
  outbox : Run.Outbox.St
  media : Run.Media.St
  config : ConfigSt'
  resource : Run.Resource.St
  upload : Run.Upload.St
  link : Run.Link.St
  value : Run.Value.St
  cvm : Run.Cvm.St
  pow : Run.Pow.St

/-- The abstraction: read every finite map as a function. -/
def abs (s : RtState') : RtState where
  shell := s.shell.abs
  inst := s.inst.get
  ports := s.ports
  now := s.now
  user := s.user
  names := s.names.get
  shellNap := s.shellNap
  theme := s.theme
  identity := s.identity
  storage := { store := s.storage.store.get, quota := s.storage.quota, keys := s.storage.keys }
  inc := s.inc
  intent := s.intent
  notify := s.notify
  display := { cfg := s.display.cfg, devices := s.display.devices, offline := s.display.offline,
               fb := fun d xy => s.display.fb.get (d, xy) }
  keys := s.keys
  relay := s.relay
  outbox := s.outbox
  media := s.media
  config := { schemas := s.config.schemas.get, values := s.config.values.get, subs := s.config.subs,
              schemaKeys := s.config.schemaKeys, valueKeys := s.config.valueKeys }
  resource := s.resource
  upload := s.upload
  link := s.link
  value := s.value
  cvm := s.cvm
  pow := s.pow

/-! ### Re-tabulation -/

def keepNe {α : Type} (l : List α) : Bool := !l.isEmpty
def keepNat (n : Nat) : Bool := n != 0
def keepRGB (c : NapDisplay.RGB) : Bool := decide (c ≠ [0, 0, 0])

theorem keepSome_dflt {α : Type} : ∀ (b : Option α), b.isSome = false → b = none
  | none, _ => rfl
theorem keepNe_dflt {α : Type} : ∀ (b : List α), keepNe b = false → b = []
  | [], _ => rfl
  | _ :: _, h => by simp [keepNe] at h
theorem keepNat_dflt : ∀ (b : Nat), keepNat b = false → b = 0 := by
  intro b h; simpa [keepNat] using h
theorem keepRGB_dflt : ∀ (b : NapDisplay.RGB), keepRGB b = false → b = [0, 0, 0] := by
  intro b h; simpa [keepRGB] using h

/-- Add every candidate window that is now removed to the interval set. -/
def addRemoved (f : WindowId → Option FrameStatus) : List WindowId → Ivs → Ivs
  | [], I => I
  | w :: ws, I => addRemoved f ws (if f w = some .removed then Ivs.insert w I else I)

theorem addRemoved_canon (f : WindowId → Option FrameStatus) : ∀ (ws : List WindowId) (I : Ivs),
    Ivs.Canon I → Ivs.Canon (addRemoved f ws I)
  | [], _, h => h
  | w :: ws, I, h => by
    simp only [addRemoved]
    apply addRemoved_canon
    split
    · exact Ivs.insert_canon w I h
    · exact h

theorem addRemoved_mem (f : WindowId → Option FrameStatus) : ∀ (ws : List WindowId) (I : Ivs),
    Ivs.Canon I → ∀ x, Ivs.mem (addRemoved f ws I) x = true ↔
      Ivs.mem I x = true ∨ (x ∈ ws ∧ f x = some .removed)
  | [], _, _, x => by simp [addRemoved]
  | w :: ws, I, h, x => by
    simp only [addRemoved]
    have hc : Ivs.Canon (if f w = some .removed then Ivs.insert w I else I) := by
      split
      · exact Ivs.insert_canon w I h
      · exact h
    rw [addRemoved_mem f ws _ hc x]
    by_cases hw : f w = some .removed
    · simp only [hw, ↓reduceIte, Ivs.mem_insert w I h.ne x, List.mem_cons]
      constructor
      · rintro ((rfl | h1) | ⟨h1, h2⟩)
        · exact .inr ⟨.inl rfl, hw⟩
        · exact .inl h1
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h1 | ⟨rfl | h1, h2⟩)
        · exact .inl (.inr h1)
        · exact .inl (.inl rfl)
        · exact .inr ⟨h1, h2⟩
    · simp only [hw, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (h1 | ⟨h1, h2⟩)
        · exact .inl h1
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h1 | ⟨rfl | h1, h2⟩)
        · exact .inl h1
        · exact absurd h2 hw
        · exact .inr ⟨h1, h2⟩

/-- Re-tabulate the state `t` that `Runtime.step` produced from `S = abs s`, on the keys
the input can have touched. -/
def reify (s : RtState') (i : Input) (S t : RtState) (outs : List Runtime.Output) : RtState' :=
  let tw := i.wins ++ outWins outs
  let ws := s.shell.live.keys ++ tw
  let tp := i.ports ++ outPorts outs
  let sc := scopesAt S i
  { shell := { live := FMap.tab none Option.isSome ws (fun w => liveOnly (t.shell.frames w))
               removed := addRemoved t.shell.frames ws s.shell.removed
               bindings := FMap.tab none Option.isSome (s.shell.bindings.keys ++ tp) t.shell.bindings
               grants := FMap.tab [] keepNe (s.shell.grants.keys ++ tp) t.shell.grants }
    inst := FMap.tab 0 keepNat (s.inst.keys ++ tw) t.inst
    ports := t.ports
    now := t.now
    user := t.user
    names := s.names
    shellNap := t.shellNap
    theme := t.theme
    identity := t.identity
    storage := { store := FMap.tab [] keepNe (s.storage.store.keys ++ sc) t.storage.store,
                 quota := t.storage.quota, keys := t.storage.keys }
    inc := t.inc
    intent := t.intent
    notify := t.notify
    display := { cfg := t.display.cfg, devices := t.display.devices, offline := t.display.offline,
                 fb := FMap.tab [0, 0, 0] keepRGB (s.display.fb.keys ++ pixelsAt i)
                   (fun k => t.display.fb k.1 k.2) }
    keys := t.keys
    relay := t.relay
    outbox := t.outbox
    media := t.media
    config := { schemas := FMap.tab none Option.isSome (s.config.schemas.keys ++ sc) t.config.schemas,
                values := FMap.tab none Option.isSome (s.config.values.keys ++ sc) t.config.values,
                subs := t.config.subs, schemaKeys := t.config.schemaKeys, valueKeys := t.config.valueKeys }
    resource := t.resource
    upload := t.upload
    link := t.link
    value := t.value
    cvm := t.cvm
    pow := t.pow }

/-- One step on the finite representation: the outputs of `Runtime.step` on `abs s`, and
the re-tabulated state. -/
def step' (h : Host) (cfg : Config) (s : RtState') (i : Input) : RtState' × List Runtime.Output :=
  let S := abs s
  let r := Runtime.step h cfg S i
  (reify s i S r.1 r.2, r.2)

theorem step'_outputs (h : Host) (cfg : Config) (s : RtState') (i : Input) :
    (step' h cfg s i).2 = (Runtime.step h cfg (abs s) i).2 := rfl

/-! ### Well-formedness -/

/-- The representation is canonical: defaults are the model's, keys are distinct, no entry
holds the default, live frames are live and not removed, intervals are canonical. -/
structure WF (s : RtState') : Prop where
  live_dflt : s.shell.live.dflt = none
  live_wf : s.shell.live.WF Option.isSome
  live_live : ∀ e ∈ s.shell.live.entries, liveOnly e.2 = e.2
  live_not_removed : ∀ w ∈ s.shell.live.keys, Ivs.mem s.shell.removed w = false
  removed : Ivs.Canon s.shell.removed
  bindings_dflt : s.shell.bindings.dflt = none
  bindings_wf : s.shell.bindings.WF Option.isSome
  grants_dflt : s.shell.grants.dflt = []
  grants_wf : s.shell.grants.WF keepNe
  inst_dflt : s.inst.dflt = 0
  inst_wf : s.inst.WF keepNat
  store_dflt : s.storage.store.dflt = []
  store_wf : s.storage.store.WF keepNe
  schemas_dflt : s.config.schemas.dflt = none
  schemas_wf : s.config.schemas.WF Option.isSome
  values_dflt : s.config.values.dflt = none
  values_wf : s.config.values.WF Option.isSome
  fb_dflt : s.display.fb.dflt = [0, 0, 0]
  fb_wf : s.display.fb.WF keepRGB

/-! ### The refinement -/

theorem liveOnly_live {o : Option FrameStatus} (h : (liveOnly o).isSome = true) : liveOnly o = o := by
  match o, h with
  | some (.live _ _ _ _), _ => rfl

theorem liveOnly_idem (o : Option FrameStatus) : liveOnly (liveOnly o) = liveOnly o := by
  match o with
  | some (.live _ _ _ _) => rfl
  | some .removed => rfl
  | none => rfl

/-- A map tabulated on a superset of the keys where `t` differs from `abs s` denotes `t`. -/
theorem get_tab_of {α β : Type} [DecidableEq α] {m : FMap α β} {d : β} {keep : β → Bool}
    {ks : List α} {f : α → β} (hd : m.dflt = d) (hk : ∀ b, keep b = false → b = d)
    (hf : ∀ a, a ∉ ks → f a = m.get a) : (FMap.tab d keep (m.keys ++ ks) f).get = f := by
  apply FMap.get_tab hk
  intro a ha
  simp only [List.mem_append, not_or] at ha
  rw [hf a ha.2, FMap.get_of_not_mem ha.1, hd]

theorem abs_reify {s : RtState'} {i : Input} {t : RtState} {outs : List Runtime.Output}
    (hw : WF s) (hf : Frame (abs s) t i outs) : abs (reify s i (abs s) t outs) = t := by
  obtain ⟨hfr, hrem, hbi, hgr, hin, hna, hst, hsc, hva, hfb⟩ := hf
  have hframes : ∀ w, (abs s).shell.frames w =
      if Ivs.mem s.shell.removed w then some .removed else s.shell.live.get w := fun _ => rfl
  generalize hS : abs s = S at hfr hrem hbi hgr hin hna hst hsc hva hfb hframes
  cases t with
  | mk tsh tinst tports tnow tuser tnames tshellNap ttheme tidentity tstorage tinc tintent tnotify
      tdisplay tkeys trelay toutbox tmedia tconfig tresource tupload tlink tvalue tcvm tpow =>
  cases tsh with
  | mk tf tb tg =>
  cases tstorage with
  | mk tstore tquota tkeys =>
  cases tconfig with
  | mk tsch tval tsubs tsk tvk =>
  cases tdisplay with
  | mk dcfg ddev doff dfb =>
  simp only at hfr hrem hbi hgr hin hna hst hsc hva hfb
  have hSb : S.shell.bindings = s.shell.bindings.get := by rw [← hS]; rfl
  have hSg : S.shell.grants = s.shell.grants.get := by rw [← hS]; rfl
  have hSi : S.inst = s.inst.get := by rw [← hS]; rfl
  have hSn : S.names = s.names.get := by rw [← hS]; rfl
  have hSst : S.storage.store = s.storage.store.get := by rw [← hS]; rfl
  have hSsc : S.config.schemas = s.config.schemas.get := by rw [← hS]; rfl
  have hSva : S.config.values = s.config.values.get := by rw [← hS]; rfl
  have hSfb : S.display.fb = fun d xy => s.display.fb.get (d, xy) := by rw [← hS]; rfl
  simp only [abs, reify, ShellState'.abs]
  congr 1
  · congr 1
    funext w
    have hlive : (FMap.tab none Option.isSome (s.shell.live.keys ++ (i.wins ++ outWins outs))
        (fun w => liveOnly (tf w))).get = fun w => liveOnly (tf w) := by
      apply FMap.get_tab keepSome_dflt
      intro v hv
      simp only [List.mem_append, not_or] at hv
      rw [hfr v hv.2.1 hv.2.2, hframes, FMap.get_of_not_mem hv.1, hw.live_dflt]
      split <;> rfl
    rw [hlive]
    have hmem := addRemoved_mem tf (s.shell.live.keys ++ (i.wins ++ outWins outs)) s.shell.removed
      hw.removed w
    have hnot : ∀ st, tf w = some st → st ≠ .removed →
        Ivs.mem (addRemoved tf (s.shell.live.keys ++ (i.wins ++ outWins outs)) s.shell.removed) w = false := by
      intro st htf hst'
      cases hm : Ivs.mem (addRemoved tf _ s.shell.removed) w
      · rfl
      · rcases hmem.mp hm with h1 | ⟨_, h2⟩
        · have := hrem w (by rw [hframes]; simp [h1]); rw [htf] at this; cases this; exact absurd rfl hst'
        · rw [htf] at h2; cases h2; exact absurd rfl hst'
    cases htf : tf w with
    | none =>
      have : Ivs.mem (addRemoved tf (s.shell.live.keys ++ (i.wins ++ outWins outs)) s.shell.removed) w = false := by
        cases hm : Ivs.mem (addRemoved tf _ s.shell.removed) w
        · rfl
        · rcases hmem.mp hm with h1 | ⟨_, h2⟩
          · have := hrem w (by rw [hframes]; simp [h1]); rw [htf] at this; cases this
          · rw [htf] at h2; cases h2
      simp [this, liveOnly, htf]
    | some st =>
      cases st with
      | removed =>
        have : Ivs.mem (addRemoved tf (s.shell.live.keys ++ (i.wins ++ outWins outs)) s.shell.removed) w = true := by
          apply hmem.mpr
          by_cases hk : w ∈ s.shell.live.keys ++ (i.wins ++ outWins outs)
          · exact .inr ⟨hk, htf⟩
          · simp only [List.mem_append, not_or] at hk
            have h1 := hfr w hk.2.1 hk.2.2
            rw [htf, hframes, FMap.get_of_not_mem hk.1, hw.live_dflt] at h1
            split at h1
            · rename_i hm; exact .inl hm
            · cases h1
        simp [this]
      | live id ex p ld =>
        simp [hnot _ htf (by simp), liveOnly, htf]
    · exact get_tab_of hw.bindings_dflt keepSome_dflt (fun q hq => by
        simp only [List.mem_append, not_or] at hq
        rw [hbi q hq.2, hSb])
    · exact get_tab_of hw.grants_dflt keepNe_dflt (fun q hq => by
        simp only [List.mem_append, not_or] at hq
        rw [hgr q hq.1 hq.2, hSg])
  · exact get_tab_of hw.inst_dflt keepNat_dflt (fun w hw' => by
      simp only [List.mem_append, not_or] at hw'
      rw [hin w hw'.1 hw'.2, hSi])
  · rw [hna, hSn]
  · congr 1
    exact get_tab_of hw.store_dflt keepNe_dflt (fun sc h => by rw [hst sc h, hSst])
  · congr 1
    have := get_tab_of (f := fun k => dfb k.1 k.2) hw.fb_dflt keepRGB_dflt (fun k h => by
      rw [hfb k h, hSfb])
    funext d xy
    exact congrFun this (d, xy)
  · congr 1
    · exact get_tab_of hw.schemas_dflt keepSome_dflt (fun sc h => by rw [hsc sc h, hSsc])
    · exact get_tab_of hw.values_dflt keepSome_dflt (fun sc h => by rw [hva sc h, hSva])

/-- The refinement: `step'` on the finite representation is `Runtime.step` on its
abstraction. With `step'_outputs`, every theorem about `Runtime.step` holds of `step'`. -/
theorem abs_step' {h : Host} {cfg : Config} {s : RtState'} (hw : WF s) (i : Input) :
    abs (step' h cfg s i).1 = (Runtime.step h cfg (abs s) i).1 :=
  abs_reify hw (step_frame h cfg (abs s) i)

/-! ### Well-formedness is preserved -/

theorem WF.reify {s : RtState'} {i : Input} {t : RtState} {outs : List Runtime.Output}
    (hw : WF s) (hf : Frame (abs s) t i outs) : WF (reify s i (abs s) t outs) where
  live_dflt := rfl
  live_wf := FMap.tab_wf
  live_live := by
    intro e he
    obtain ⟨h1, -, -⟩ := FMap.mem_tab_entries he
    rw [h1, liveOnly_idem]
  live_not_removed := by
    intro w hk
    obtain ⟨-, hkeep⟩ := FMap.keys_tab hk
    show Ivs.mem (addRemoved t.shell.frames (s.shell.live.keys ++ (i.wins ++ outWins outs))
      s.shell.removed) w = false
    cases hm : Ivs.mem (addRemoved t.shell.frames _ s.shell.removed) w
    · rfl
    · rcases (addRemoved_mem _ _ _ hw.removed w).mp hm with h1 | ⟨_, h2⟩
      · have := hf.removed w (by simp [abs, ShellState'.abs, h1])
        rw [this] at hkeep; simp [liveOnly] at hkeep
      · rw [h2] at hkeep; simp [liveOnly] at hkeep
  removed := addRemoved_canon _ _ _ hw.removed
  bindings_dflt := rfl
  bindings_wf := FMap.tab_wf
  grants_dflt := rfl
  grants_wf := FMap.tab_wf
  inst_dflt := rfl
  inst_wf := FMap.tab_wf
  store_dflt := rfl
  store_wf := FMap.tab_wf
  schemas_dflt := rfl
  schemas_wf := FMap.tab_wf
  values_dflt := rfl
  values_wf := FMap.tab_wf
  fb_dflt := rfl
  fb_wf := FMap.tab_wf

theorem WF.step' {h : Host} {cfg : Config} {s : RtState'} (hw : WF s) (i : Input) :
    WF (step' h cfg s i).1 :=
  hw.reify (step_frame h cfg (abs s) i)

/-! ### Initial state and reachability -/

/-- The initial finite state. `names` is the finite form of `Config.endpointName`. -/
def init' (cfg : Config) (names : FMap WindowId (Option String)) : RtState' where
  shell := { live := .const none, removed := [], bindings := .const none, grants := .const [] }
  inst := .const 0
  ports := []
  now := 0
  user := ""
  names := names
  shellNap := Run.Shell.St.init cfg.shell
  theme := Run.Theme.St.init
  identity := Run.Identity.St.init
  storage := { store := .const [], quota := cfg.storageQuota, keys := [] }
  inc := Run.Inc.St.init cfg.incCfg
  intent := Run.Intent.St.init cfg.intentCfg
  notify := Run.Notify.St.init cfg.notifyCfg
  display := { cfg := cfg.displayCfg, devices := cfg.displayCfg.devices, offline := [],
               fb := .const [0, 0, 0] }
  keys := Run.Keys.St.init cfg.keysCfg
  relay := Run.Relay.St.init cfg.relayCfg
  outbox := Run.Outbox.St.init cfg.outboxCfg
  media := Run.Media.St.init cfg.mediaCfg
  config := { schemas := .const none, values := .const none, subs := [], schemaKeys := [], valueKeys := [] }
  resource := Run.Resource.St.init cfg.resourceCfg
  upload := Run.Upload.St.init cfg.uploadCfg
  link := Run.Link.St.init cfg.linkCfg
  value := Run.Value.St.init cfg.valueCfg
  cvm := Run.Cvm.St.init cfg.cvmCfg
  pow := Run.Pow.St.init cfg.powCfg

theorem WF.init' (cfg : Config) (names : FMap WindowId (Option String)) : WF (init' cfg names) where
  live_dflt := rfl
  live_wf := ⟨List.nodup_nil, by simp [Refine.init', FMap.const]⟩
  live_live := by simp [Refine.init', FMap.const]
  live_not_removed := by simp [Refine.init', FMap.const, FMap.keys]
  removed := trivial
  bindings_dflt := rfl
  bindings_wf := ⟨List.nodup_nil, by simp [Refine.init', FMap.const]⟩
  grants_dflt := rfl
  grants_wf := ⟨List.nodup_nil, by simp [Refine.init', FMap.const]⟩
  inst_dflt := rfl
  inst_wf := ⟨List.nodup_nil, by simp [Refine.init', FMap.const]⟩
  store_dflt := rfl
  store_wf := ⟨List.nodup_nil, by simp [Refine.init', FMap.const]⟩
  schemas_dflt := rfl
  schemas_wf := ⟨List.nodup_nil, by simp [Refine.init', FMap.const]⟩
  values_dflt := rfl
  values_wf := ⟨List.nodup_nil, by simp [Refine.init', FMap.const]⟩
  fb_dflt := rfl
  fb_wf := ⟨List.nodup_nil, by simp [Refine.init', FMap.const]⟩

/-- `init'` denotes `RtState.init` when `names` is the endpoint-name policy. -/
theorem abs_init' (cfg : Config) (names : FMap WindowId (Option String))
    (hn : names.get = cfg.endpointName) : abs (init' cfg names) = RtState.init cfg := by
  simp only [abs, Refine.init', RtState.init, ShellState'.abs, hn, FMap.get_const]
  rfl

/-- States `step'` reaches from `init'`. -/
inductive Reachable' (h : Host) (cfg : Config) (names : FMap WindowId (Option String)) : RtState' → Prop where
  | init : Reachable' h cfg names (init' cfg names)
  | step {s : RtState'} (i : Input) : Reachable' h cfg names s → Reachable' h cfg names (step' h cfg s i).1

/-- Every state `step'` reaches is well formed and is the abstraction of a state
`Runtime.step` reaches, so every theorem about reachable states applies to it. -/
theorem Reachable'.abs {h : Host} {cfg : Config} {names : FMap WindowId (Option String)}
    (hn : names.get = cfg.endpointName) {s : RtState'} (hr : Reachable' h cfg names s) :
    WF s ∧ Runtime.Reachable h cfg (Refine.abs s) := by
  induction hr with
  | init => exact ⟨WF.init' cfg names, abs_init' cfg names hn ▸ .init⟩
  | step i _ ih =>
    refine ⟨ih.1.step' i, ?_⟩
    rw [abs_step' ih.1]
    exact .step i ih.2

/-! ### Invariants for the memory bound -/

section mem
variable {c : Crypto} {scfg : ShellConfig} {sh : ShellState}

def IsLive (o : Option FrameStatus) : Prop := ∃ id ex p ld, o = some (.live id ex p ld)

theorem revoke_live_or (w w' : WindowId) (hl : IsLive (sh.frames w)) :
    IsLive ((revoke sh w').1.frames w) ∨ Napplet.Output.removeFrame w ∈ (revoke sh w').2 := by
  rcases revoke_frames_frame (s := sh) w w' with h | h
  · exact .inl (h ▸ hl)
  · exact .inr h

/-- A live frame stays live unless the shell removes it. -/
theorem live_stays (e : Event) (w : WindowId) (hl : IsLive (sh.frames w)) :
    IsLive ((Napplet.step c scfg sh e).1.frames w) ∨
      Napplet.Output.removeFrame w ∈ (Napplet.step c scfg sh e).2 := by
  obtain ⟨id, ex, p, ld, hf⟩ := hl
  cases e with
  | create w' m bytes =>
    simp only [Napplet.step]
    split
    · exact .inl ⟨id, ex, p, ld, hf⟩
    · split
      · exact .inl ⟨id, ex, p, ld, hf⟩
      · have : w ≠ w' := by intro hw; subst hw; simp_all
        exact .inl ⟨id, ex, p, ld, by simp [upd, this, hf]⟩
  | load w' =>
    simp only [Napplet.step]
    split
    · by_cases hw : w = w'
      · subst hw; exact .inl ⟨_, _, _, _, by dsimp only; rw [upd_same]⟩
      · exact .inl ⟨id, ex, p, ld, by simp [upd, hw, hf]⟩
    · exact revoke_live_or w w' ⟨id, ex, p, ld, hf⟩
    · exact .inl ⟨id, ex, p, ld, hf⟩
  | hello w' ports =>
    simp only [Napplet.step]
    split
    · split
      · split
        · by_cases hw : w = w'
          · subst hw; exact .inl ⟨_, _, _, _, by dsimp only; rw [upd_same]⟩
          · exact .inl ⟨id, ex, p, ld, by simp [upd, hw, hf]⟩
        · exact .inl ⟨id, ex, p, ld, hf⟩
      · exact .inl ⟨id, ex, p, ld, hf⟩
    · exact revoke_live_or w w' ⟨id, ex, p, ld, hf⟩
    · exact .inl ⟨id, ex, p, ld, hf⟩
  | windowMsg w' =>
    simp only [Napplet.step]
    split
    · exact revoke_live_or w w' ⟨id, ex, p, ld, hf⟩
    · exact .inl ⟨id, ex, p, ld, hf⟩
  | portClosed q =>
    simp only [Napplet.step]
    split
    · rename_i b _
      exact revoke_live_or w b.window ⟨id, ex, p, ld, hf⟩
    · exact .inl ⟨id, ex, p, ld, hf⟩
  | nap q env => exact .inl ⟨id, ex, p, ld, by rw [step_nap_state]; exact hf⟩
  | grant q g =>
    simp only [Napplet.step]
    split <;> exact .inl ⟨id, ex, p, ld, hf⟩

/-- Creating a frame in an unused window either makes it live or rejects it. -/
theorem create_none {w : WindowId} {m : ManifestEvent} {bytes : Bytes} (hn : sh.frames w = none) :
    IsLive ((Napplet.step c scfg sh (.create w m bytes)).1.frames w) ∨
      ∃ er, Napplet.Output.rejected w er ∈ (Napplet.step c scfg sh (.create w m bytes)).2 := by
  simp only [Napplet.step, hn]
  split
  · rename_i er _; exact .inr ⟨er, by simp⟩
  · exact .inl ⟨_, _, _, _, by dsimp only; rw [upd_same]⟩

theorem boundPorts_revoke (w : WindowId) : Runtime.boundPorts (revoke sh w).2 = [] := by
  unfold revoke; split <;> rfl

/-- A shell step binds at most one port, and only one that was unbound. -/
theorem boundPorts_step (e : Event) :
    (Runtime.boundPorts (Napplet.step c scfg sh e).2).length ≤ 1 ∧
      ∀ q ∈ Runtime.boundPorts (Napplet.step c scfg sh e).2, sh.bindings q = none := by
  cases e with
  | create w m bytes =>
    simp only [Napplet.step]
    split
    · simp [Runtime.boundPorts]
    · split <;> simp [Runtime.boundPorts]
  | load w =>
    simp only [Napplet.step]
    split
    · simp [Runtime.boundPorts]
    · rw [boundPorts_revoke]; simp
    · simp [Runtime.boundPorts]
  | hello w ports =>
    simp only [Napplet.step]
    split
    · split
      · split
        · rename_i hb; simp [Runtime.boundPorts, hb]
        · simp [Runtime.boundPorts]
      · simp [Runtime.boundPorts]
    · rw [boundPorts_revoke]; simp
    · simp [Runtime.boundPorts]
  | windowMsg w =>
    simp only [Napplet.step]
    split
    · rw [boundPorts_revoke]; simp
    · simp [Runtime.boundPorts]
  | portClosed p =>
    simp only [Napplet.step]
    split
    · rw [boundPorts_revoke]; simp
    · simp [Runtime.boundPorts]
  | nap p env =>
    simp only [Napplet.step]
    split
    · split
      · split <;> simp [Runtime.boundPorts]
      · simp [Runtime.boundPorts]
    · simp [Runtime.boundPorts]
  | grant p g =>
    simp only [Napplet.step]
    split <;> simp [Runtime.boundPorts]

end mem

theorem mem_removedFrames_of {os : List Napplet.Output} {w : WindowId}
    (h : Napplet.Output.removeFrame w ∈ os ∨ ∃ e, Napplet.Output.rejected w e ∈ os) :
    w ∈ removedFrames os := by
  induction os with
  | nil => rcases h with h | ⟨_, h⟩ <;> simp at h
  | cons o os ih =>
    rcases h with h | ⟨e, h⟩
    · rcases List.mem_cons.mp h with rfl | h
      · simp [removedFrames]
      · have := ih (.inl h); cases o <;> simp [removedFrames, this]
    · rcases List.mem_cons.mp h with rfl | h
      · simp [removedFrames]
      · have := ih (.inr ⟨e, h⟩); cases o <;> simp [removedFrames, this]

theorem clearInst_mem (f : WindowId → Nat) : ∀ (ws : List WindowId) (w : WindowId),
    w ∈ ws → clearInst f ws w = 0
  | [], _, h => by simp at h
  | v :: ws, w, h => by
    simp only [clearInst]
    by_cases hw : w ∈ ws
    · exact clearInst_mem _ ws w hw
    · rw [clearInst_other _ ws w hw]
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp [upd]
      · exact absurd h hw

theorem napStep_ports (h : Host) (w : World) (cx : Ctx) (s : RtState) (j : Json) (d : Domain) :
    (napStep h w cx s j d).1.ports = s.ports := by
  cases d <;> simp only [napStep, lift] <;> split <;> rfl

/-- Inputs that are not browser events leave the shell, instance ids and ports alone. -/
theorem step_nonbrowser (h : Host) (cfg : Config) (S : RtState) (i : Input) (hi : i.event? = none) :
    (Runtime.step h cfg S i).1.shell = S.shell ∧ (Runtime.step h cfg S i).1.inst = S.inst ∧
      (Runtime.step h cfg S i).1.ports = S.ports := by
  cases i with
  | message p j =>
    simp only [Runtime.step]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · split
      · split
        · exact ⟨(napStep_fields _ _ _ _ _ _).1, (napStep_fields _ _ _ _ _ _).2.1, napStep_ports _ _ _ _ _ _⟩
        · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
  | reply tag r =>
    refine ⟨(replyStep_fields h S tag r).1, (replyStep_fields h S tag r).2.1, ?_⟩
    simp only [Runtime.step, replyStep]; split <;> rfl
  | event e => exact ⟨(eventStep_fields h S e).1, (eventStep_fields h S e).2.1, rfl⟩
  | tick n => exact ⟨rfl, rfl, rfl⟩
  | _ => simp [Input.event?] at hi

/-- Memory invariant of the reference machine: a non-zero instance id belongs to a live
frame, and `ports` lists bound ports without repetition. -/
structure MemInv (S : RtState) : Prop where
  inst : ∀ w, S.inst w ≠ 0 → IsLive (S.shell.frames w)
  ports_bound : ∀ p ∈ S.ports, (S.shell.bindings p).isSome = true
  ports_nodup : S.ports.Nodup

theorem MemInv.init (cfg : Config) : MemInv (RtState.init cfg) where
  inst _ h := absurd rfl h
  ports_bound _ h := by simp [RtState.init] at h
  ports_nodup := List.nodup_nil

theorem MemInv.step {h : Host} {cfg : Config} {S : RtState} (hm : MemInv S) (i : Input) :
    MemInv (Runtime.step h cfg S i).1 := by
  cases hi : i.event? with
  | none =>
    obtain ⟨e1, e2, e3⟩ := step_nonbrowser h cfg S i hi
    exact ⟨fun w hw => by rw [e1]; rw [e2] at hw; exact hm.inst w hw,
      fun p hp => by rw [e1]; rw [e3] at hp; exact hm.ports_bound p hp, by rw [e3]; exact hm.ports_nodup⟩
  | some e =>
    obtain ⟨S0, e1, -, -, -, -, -, -, -, hstep, hp0, hdiff⟩ := step_browser h cfg S i e hi
    rw [hstep]
    have hports : (browserStep h cfg S0 e).1.ports =
        keepBound (Napplet.step h.crypto cfg.shell S0.shell e).1
          (boundPorts (Napplet.step h.crypto cfg.shell S0.shell e).2 ++ S0.ports) := by
      rcases hso : Napplet.step h.crypto cfg.shell S0.shell e with ⟨sh, outs⟩
      simp only [browserStep, hso, flushStep]
      exact (dropPorts_shell _ _).2
    obtain ⟨b1, b2, -, -, -, -, -, -⟩ := browserStep_spec h cfg S0 e
    rw [e1] at b1 b2 hports
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rw [b2] at hw
      have hnr : w ∉ removedFrames (Napplet.step h.crypto cfg.shell S.shell e).2 :=
        fun hm => hw (clearInst_mem _ _ _ hm)
      rw [clearInst_other _ _ _ hnr] at hw
      rw [b1]
      by_cases hd : S0.inst w = S.inst w
      · rw [hd] at hw
        rcases live_stays (c := h.crypto) (scfg := cfg.shell) e w (hm.inst w hw) with h1 | h1
        · exact h1
        · exact absurd (mem_removedFrames_of (.inl h1)) hnr
      · obtain ⟨hn, m, b, rfl⟩ := hdiff w hd
        rcases create_none (c := h.crypto) (scfg := cfg.shell) (m := m) (bytes := b) hn with h1 | ⟨er, h1⟩
        · exact h1
        · exact absurd (mem_removedFrames_of (.inr ⟨er, h1⟩)) hnr
    · intro p hp
      rw [hports] at hp
      rw [b1]
      exact (List.mem_filter.mp hp).2
    · rw [hports]
      refine List.Nodup.sublist (List.filter_sublist) ?_
      rw [hp0]
      obtain ⟨hl, hun⟩ := boundPorts_step (c := h.crypto) (scfg := cfg.shell) (sh := S.shell) e
      refine List.nodup_append.mpr ⟨?_, hm.ports_nodup, ?_⟩
      · match hb : boundPorts (Napplet.step h.crypto cfg.shell S.shell e).2, hl with
        | [], _ => exact List.nodup_nil
        | [_], _ => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
      · intro a ha b hb' hab
        subst hab
        have := hm.ports_bound a hb'
        rw [hun a ha] at this
        cases this

theorem Reachable.memInv {h : Host} {cfg : Config} {S : RtState} (hr : Runtime.Reachable h cfg S) :
    MemInv S := by
  induction hr with
  | init => exact MemInv.init cfg
  | step i _ ih => exact ih.step i

/-! ### Memory follows live state -/

section memory
variable {h : Host} {cfg : Config} {names : FMap WindowId (Option String)} {s : RtState'}

/-- Every key of the live-frame map is a live window. -/
theorem live_keys (hw : WF s) {w : WindowId} (hk : w ∈ s.shell.live.keys) :
    IsLive ((abs s).shell.frames w) := by
  simp only [abs, ShellState'.abs, hw.live_not_removed w hk]
  obtain ⟨⟨k, v⟩, he, rfl⟩ := List.mem_map.mp hk
  rw [FMap.get_of_mem hw.live_wf.1 he]
  have h1 := hw.live_live _ he
  have h2 := hw.live_wf.2 _ he
  simp only at h1 h2
  rw [← h1] at h2 ⊢
  match v, h2 with
  | some (.live id ex p ld), _ => exact ⟨id, ex, p, ld, rfl⟩

/-- Every key of the bindings map is a bound port. -/
theorem bindings_keys (hw : WF s) {q : PortId} (hk : q ∈ s.shell.bindings.keys) :
    ((abs s).shell.bindings q).isSome = true := by
  obtain ⟨⟨k, v⟩, he, rfl⟩ := List.mem_map.mp hk
  simp only [abs, ShellState'.abs]
  rw [FMap.get_of_mem hw.bindings_wf.1 he]
  exact hw.bindings_wf.2 _ he

/-- Every key of the grants map is a bound port. -/
theorem grants_keys (hn : names.get = cfg.endpointName) (hr : Reachable' h cfg names s)
    {q : PortId} (hk : q ∈ s.shell.grants.keys) : ((abs s).shell.bindings q).isSome = true := by
  obtain ⟨hw, hR⟩ := hr.abs hn
  obtain ⟨⟨k, v⟩, he, rfl⟩ := List.mem_map.mp hk
  cases hb : (abs s).shell.bindings k with
  | some _ => rfl
  | none =>
    have := (Runtime.shell_inv hR).grants_bound k hb
    simp only [abs, ShellState'.abs] at this
    rw [FMap.get_of_mem hw.grants_wf.1 he] at this
    have := hw.grants_wf.2 _ he
    simp_all [keepNe]

/-- Every key of the instance-id map is a live window. -/
theorem inst_keys (hn : names.get = cfg.endpointName) (hr : Reachable' h cfg names s)
    {w : WindowId} (hk : w ∈ s.inst.keys) : IsLive ((abs s).shell.frames w) := by
  obtain ⟨hw, hR⟩ := hr.abs hn
  obtain ⟨⟨k, v⟩, he, rfl⟩ := List.mem_map.mp hk
  apply (Reachable.memInv hR).inst
  simp only [abs]
  rw [FMap.get_of_mem hw.inst_wf.1 he]
  have := hw.inst_wf.2 _ he
  simpa [keepNat] using this

/-- `ports` lists bound ports, each once. -/
theorem ports_bound (hn : names.get = cfg.endpointName) (hr : Reachable' h cfg names s) :
    (∀ p ∈ s.ports, ((abs s).shell.bindings p).isSome = true) ∧ s.ports.Nodup := by
  obtain ⟨-, hR⟩ := hr.abs hn
  exact ⟨(Reachable.memInv hR).ports_bound, (Reachable.memInv hR).ports_nodup⟩

/-- No component keeps per-endpoint state for a port that is not bound
(`Runtime.teardown_clears` on the abstraction). -/
theorem components_bound (hn : names.get = cfg.endpointName) (hr : Reachable' h cfg names s)
    {p : PortId} (hb : (abs s).shell.bindings p = none) : mentions (abs s) p = false :=
  Runtime.teardown_clears (hr.abs hn).2 hb

/-- Removed windows cost at most one interval more than there are live windows, when the
host numbers windows `0, 1, …, n - 1` (every window below `n` was created, none above). -/
theorem removed_length_le (hw : WF s) {n : Nat}
    (hb : ∀ w, (abs s).shell.frames w ≠ none → w < n)
    (hcov : ∀ w, w < n → (abs s).shell.frames w ≠ none) :
    s.shell.removed.length ≤ s.shell.live.keys.length + 1 := by
  apply Ivs.length_le hw.removed (n := n)
  · intro x hx
    apply hb x
    simp [abs, ShellState'.abs, hx]
  · intro x hx
    have := hcov x hx
    cases hm : Ivs.mem s.shell.removed x
    · right
      simp only [abs, ShellState'.abs, hm] at this
      by_cases hk : x ∈ s.shell.live.keys
      · exact hk
      · rw [FMap.get_of_not_mem hk, hw.live_dflt] at this
        exact absurd rfl this
    · exact .inl rfl

/-- **Removed windows, unconditionally.** The intervals number at most one more than the
live windows plus the window ids below the largest removed one that were never used. A
host that numbers windows consecutively uses every id, so the last term is zero
(`removed_length_le`): the cost does not grow with the number of removals. -/
theorem removed_length_le_unused (hw : WF s) :
    s.shell.removed.length ≤ s.shell.live.keys.length +
      ((List.range (Ivs.top s.shell.removed)).filter fun w => ((abs s).shell.frames w).isNone).length + 1 := by
  have h := Ivs.length_le hw.removed (n := Ivs.top s.shell.removed)
    (L := s.shell.live.keys ++ (List.range (Ivs.top s.shell.removed)).filter fun w => ((abs s).shell.frames w).isNone)
    (fun x hx => Ivs.lt_top hx) ?_
  · simpa [Nat.add_assoc] using h
  · intro x hx
    cases hm : Ivs.mem s.shell.removed x
    · right
      by_cases hk : x ∈ s.shell.live.keys
      · exact List.mem_append_left _ hk
      · apply List.mem_append_right
        simp only [List.mem_filter, List.mem_range]
        refine ⟨hx, ?_⟩
        simp [abs, ShellState'.abs, hm, FMap.get_of_not_mem hk, hw.live_dflt]
    · exact .inl rfl

end memory

end Napplet.Refine
