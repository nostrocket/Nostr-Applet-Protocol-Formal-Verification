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
      e.wins ⊆ i.wins ∧ e.ports ⊆ i.ports ∧ step h cfg S i = browserStep h cfg S0 e := by
  cases i with
  | create w m bytes inst =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    by_cases hn : (S.shell.frames w).isNone = true
    · refine ⟨{ S with inst := upd S.inst w inst }, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · intro v hv; simp only [Input.wins, List.mem_singleton] at hv; simp [upd, hv]
      · simp [Event.wins, Input.wins]
      · simp [Event.ports]
      · simp [step, hn]
    · refine ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_, ?_, ?_⟩
      · simp [Event.wins, Input.wins]
      · simp [Event.ports]
      · simp [step, hn]
  | load w =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins, Input.wins],
      by simp [Event.ports], rfl⟩
  | hello w ps =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins, Input.wins],
      by simp [Event.ports, Input.ports], rfl⟩
  | windowMsg w =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins, Input.wins],
      by simp [Event.ports], rfl⟩
  | portClosed p =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins],
      by simp [Event.ports, Input.ports], rfl⟩
  | grant p g =>
    simp only [Input.event?, Option.some.injEq] at he; subst he
    exact ⟨S, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [Event.wins],
      by simp [Event.ports, Input.ports], rfl⟩
  | message p j => simp [Input.event?] at he
  | reply t r => simp [Input.event?] at he
  | event ev => simp [Input.event?] at he
  | tick n => simp [Input.event?] at he

theorem Frame.browser (h : Host) (cfg : Config) (S : RtState) (i : Input) (e : Event)
    (he : i.event? = some e) : Frame S (step h cfg S i).1 i (step h cfg S i).2 := by
  obtain ⟨S0, e1, e2, e3, e4, e5, e6, hw, hp, hstep⟩ := step_browser h cfg S i e he
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
