/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Capability
import Napplet.Wire

/-!
# Shell runtime state machine (NIP-5D §Transport, §Identity, §Security)

The shell sees browser events (iframe `load`, window messages, port closure) and
NAP envelopes arriving on ports. `step` is the shell's transition function.

Modelled assumptions (not proved, they are browser guarantees):
* `WindowId` in an event is the true `MessageEvent.source` (unforgeable).
* Ports listed in `hello` are the ports actually transferred.
* The retained bootstrap port is unreachable from napplet code.

Main results (all over every reachable state):
* `nap_dispatch_requires_binding`: NAP messages are processed only from a bound port.
* `dispatch_sender_verified`: the sender identity attached to a dispatched message
  is one the runtime computed from verified bytes.
* `dispatch_domain_exposed`: only exposed domains are dispatched.
* `revoke_*`: second hello, post-handoff window message, second load and port
  close each close the port, drop the binding and every grant, and remove the frame.
* `removed_stays_removed`, `no_rebind_removed`: identities are never re-bound to an
  existing iframe.
* `Inv` is an inductive invariant: bindings and frames agree, grants exist only on
  bound ports.
-/

namespace Napplet

/-- An abstract capability grant attached to a session. -/
abbrev Grant := String

/-- Iframe status as tracked by the shell. -/
inductive FrameStatus where
  /-- Verified iframe. `port = none` until the single `napplet.hello`. -/
  | live (id : Identity) (exposed : List Domain) (port : Option PortId) (loaded : Bool)
  /-- Torn down. A window id is never reused. -/
  | removed
  deriving DecidableEq, Repr

/-- What a bound port is attached to. -/
structure Binding where
  window : WindowId
  identity : Identity
  exposed : List Domain
  deriving DecidableEq, Repr

structure ShellState where
  frames : WindowId → Option FrameStatus
  bindings : PortId → Option Binding
  grants : PortId → List Grant

def ShellState.init : ShellState :=
  { frames := fun _ => none, bindings := fun _ => none, grants := fun _ => [] }

/-- Inputs to the shell. -/
inductive Event where
  /-- Host asks to run manifest `m` with fetched artifact `bytes` in a new window `w`. -/
  | create (w : WindowId) (m : ManifestEvent) (bytes : Bytes)
  /-- iframe `load` event. -/
  | load (w : WindowId)
  /-- Window-level `{type:"napplet.hello"}` with transferred ports. -/
  | hello (w : WindowId) (ports : List PortId)
  /-- Any other window-level message from window `w`. -/
  | windowMsg (w : WindowId)
  /-- A port closed or errored. -/
  | portClosed (p : PortId)
  /-- An envelope arriving on port `p`. -/
  | nap (p : PortId) (env : Envelope)
  /-- Shell policy attaches a grant to the session on port `p`. -/
  | grant (p : PortId) (g : Grant)

/-- Observable shell actions. -/
inductive Output where
  | rejected (w : WindowId) (e : ManifestError)
  /-- `srcdoc` iframe created with `sandbox="allow-scripts"` and this namespace. -/
  | iframeCreated (w : WindowId) (id : Identity) (exposed : List Domain)
  | bound (w : WindowId) (p : PortId) (id : Identity)
  | closePort (p : PortId)
  | removeFrame (w : WindowId)
  /-- Hand the envelope to the NAP handler for domain `d`, with runtime-attested sender. -/
  | dispatch (p : PortId) (sender : Identity) (d : Domain) (env : Envelope)
  deriving DecidableEq, Repr

/-- Tear down window `w`: close its port explicitly, revoke binding and grants,
remove the frame (NIP-5D §Identity 5–7). -/
def revoke (s : ShellState) (w : WindowId) : ShellState × List Output :=
  match s.frames w with
  | some (.live _ _ (some p) _) =>
    ({ frames := upd s.frames w (some .removed)
       bindings := upd s.bindings p none
       grants := upd s.grants p [] }, [.closePort p, .removeFrame w])
  | some (.live _ _ none _) =>
    ({ s with frames := upd s.frames w (some .removed) }, [.removeFrame w])
  | _ => (s, [])

/-- Admit a verified manifest, or say why not. -/
def admit (c : Crypto) (cfg : ShellConfig) (m : ManifestEvent) (bytes : Bytes) :
    Except ManifestError (Identity × List Domain) :=
  match checkManifest c m bytes with
  | .error e => .error e
  | .ok v =>
    let ex := exposedFor cfg v.identity
    match missingRequired ex v.required with
    | some n => if cfg.strictRequired then .error (.missingRequired n) else .ok (v.identity, ex)
    | none => .ok (v.identity, ex)

/-- The shell transition function. -/
def step (c : Crypto) (cfg : ShellConfig) (s : ShellState) : Event → ShellState × List Output
  | .create w m bytes =>
    match s.frames w with
    | some _ => (s, [])
    | none =>
      match admit c cfg m bytes with
      | .error e => (s, [.rejected w e])
      | .ok (id, ex) =>
        ({ s with frames := upd s.frames w (some (.live id ex none false)) },
         [.iframeCreated w id ex])
  | .load w =>
    match s.frames w with
    | some (.live id ex p false) =>
      ({ s with frames := upd s.frames w (some (.live id ex p true)) }, [])
    | some (.live _ _ _ true) => revoke s w
    | _ => (s, [])
  | .hello w ports =>
    match s.frames w with
    | some (.live id ex none ld) =>
      match ports with
      | [p] =>
        match s.bindings p with
        | none =>
          ({ s with
              frames := upd s.frames w (some (.live id ex (some p) ld))
              bindings := upd s.bindings p (some ⟨w, id, ex⟩) },
           [.bound w p id])
        | some _ => (s, [])
      | _ => (s, [])
    | some (.live _ _ (some _) _) => revoke s w
    | _ => (s, [])
  | .windowMsg w =>
    match s.frames w with
    | some (.live _ _ (some _) _) => revoke s w
    | _ => (s, [])
  | .portClosed p =>
    match s.bindings p with
    | some b => revoke s b.window
    | none => (s, [])
  | .nap p env =>
    match s.bindings p with
    | some b =>
      match env.domain? with
      | some d => if d ∈ b.exposed then (s, [.dispatch p b.identity d env]) else (s, [])
      | none => (s, [])
    | none => (s, [])
  | .grant p g =>
    match s.bindings p with
    | some _ => ({ s with grants := upd s.grants p (g :: s.grants p) }, [])
    | none => (s, [])

/-! ## Reachability -/

inductive Reachable (c : Crypto) (cfg : ShellConfig) : ShellState → Prop where
  | init : Reachable c cfg .init
  | step {s : ShellState} (e : Event) : Reachable c cfg s → Reachable c cfg (step c cfg s e).1

/-- `id` was produced by verifying some manifest against some bytes. -/
def Verified (c : Crypto) (id : Identity) : Prop :=
  ∃ m bytes v, checkManifest c m bytes = .ok v ∧ v.identity = id

/-! ## Local (one-step) properties -/

section local_props
variable {c : Crypto} {cfg : ShellConfig} {s : ShellState}

/-- Unbound ports produce nothing and change nothing. -/
theorem nap_unbound_dropped {p : PortId} {env : Envelope} (h : s.bindings p = none) :
    step c cfg s (.nap p env) = (s, []) := by
  simp [step, h]

/-- The only way to get a `dispatch` output is a NAP envelope on a bound port whose
binding carries exactly that sender identity and exposes that domain. -/
theorem dispatch_inv {e : Event} {p : PortId} {sender : Identity} {d : Domain} {env : Envelope}
    (h : Output.dispatch p sender d env ∈ (step c cfg s e).2) :
    e = .nap p env ∧ ∃ b, s.bindings p = some b ∧ b.identity = sender ∧ d ∈ b.exposed := by
  cases e with
  | nap p' env' =>
    simp only [step] at h
    split at h
    · rename_i b hb
      split at h
      · rename_i d' _
        split at h
        · simp at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨rfl, b, hb, rfl, by assumption⟩
        · simp at h
      · simp at h
    · simp at h
  | create w m bytes =>
    simp only [step] at h
    split at h
    · simp at h
    · split at h <;> simp at h
  | load w =>
    simp only [step, revoke] at h
    split at h <;> (try split at h) <;> simp at h
  | hello w ports =>
    simp only [step, revoke] at h
    split at h
    · split at h
      · split at h <;> simp at h
      · simp at h
    · split at h <;> simp at h
    · simp at h
  | windowMsg w =>
    simp only [step, revoke] at h
    split at h
    · split at h <;> simp at h
    · simp at h
  | portClosed q =>
    simp only [step, revoke] at h
    split at h
    · split at h <;> simp at h
    · simp at h
  | grant q g =>
    simp only [step] at h
    split at h <;> simp at h

/-- NAP messages are processed only from a bound port (NIP-5D §Identity 9). -/
theorem nap_dispatch_requires_binding {p : PortId} {env : Envelope}
    (h : (step c cfg s (.nap p env)).2 ≠ []) : (s.bindings p).isSome := by
  cases hb : s.bindings p with
  | none => simp [nap_unbound_dropped hb] at h
  | some _ => rfl

/-- Messages for domains not exposed to this napplet are silently ignored, so the
host dispatch allowlist matches namespace injection. -/
theorem dispatch_domain_exposed {e : Event} {p : PortId} {sender : Identity} {d : Domain}
    {env : Envelope} (h : Output.dispatch p sender d env ∈ (step c cfg s e).2) :
    ∃ b, s.bindings p = some b ∧ d ∈ b.exposed := by
  obtain ⟨_, b, hb, _, hd⟩ := dispatch_inv h
  exact ⟨b, hb, hd⟩

theorem revoke_frames_removed {w w' : WindowId} (h : s.frames w = some .removed) :
    (revoke s w').1.frames w = some .removed := by
  unfold revoke
  split
  · by_cases hw : w = w' <;> simp [upd, hw, h]
  · by_cases hw : w = w' <;> simp [upd, hw, h]
  · exact h

/-- A removed window never comes back. -/
theorem removed_stays_removed {w : WindowId} (e : Event) (h : s.frames w = some .removed) :
    (step c cfg s e).1.frames w = some .removed := by
  cases e with
  | create w' m bytes =>
    simp only [step]
    split
    · exact h
    · rename_i hn
      split
      · exact h
      · have : w ≠ w' := by intro hw; subst hw; simp_all
        simp [upd, this, h]
  | load w' =>
    simp only [step]
    split
    · rename_i hf
      have : w ≠ w' := by intro hw; subst hw; simp_all
      simp [upd, this, h]
    · exact revoke_frames_removed h
    · exact h
  | hello w' ports =>
    simp only [step]
    split
    · rename_i hf
      have : w ≠ w' := by intro hw; subst hw; simp_all
      split
      · split
        · simp [upd, this, h]
        · exact h
      · exact h
    · exact revoke_frames_removed h
    · exact h
  | windowMsg w' =>
    simp only [step]
    split
    · exact revoke_frames_removed h
    · exact h
  | portClosed q =>
    simp only [step]
    split
    · exact revoke_frames_removed h
    · exact h
  | nap q env =>
    simp only [step]
    split
    · split
      · split <;> exact h
      · exact h
    · exact h
  | grant q g =>
    simp only [step]
    split <;> exact h

/-- A removed window can never be (re)bound (NIP-5D §Identity 10). -/
theorem no_rebind_removed {w : WindowId} {p : PortId} {id : Identity} (e : Event)
    (h : s.frames w = some .removed) : Output.bound w p id ∉ (step c cfg s e).2 := by
  intro hm
  cases e with
  | hello w' ports =>
    simp only [step, revoke] at hm
    split at hm
    · rename_i hf
      split at hm
      · split at hm
        · simp at hm
          obtain ⟨rfl, -, -⟩ := hm
          simp_all
        · simp at hm
      · simp at hm
    · split at hm <;> simp at hm
    · simp at hm
  | create w' m bytes =>
    simp only [step] at hm
    split at hm
    · simp at hm
    · split at hm <;> simp at hm
  | load w' =>
    simp only [step, revoke] at hm
    split at hm <;> (try split at hm) <;> simp at hm
  | windowMsg w' =>
    simp only [step, revoke] at hm
    split at hm
    · split at hm <;> simp at hm
    · simp at hm
  | portClosed q =>
    simp only [step, revoke] at hm
    split at hm
    · split at hm <;> simp at hm
    · simp at hm
  | nap q env =>
    simp only [step] at hm
    split at hm
    · split at hm
      · split at hm <;> simp at hm
      · simp at hm
    · simp at hm
  | grant q g =>
    simp only [step] at hm
    split at hm <;> simp at hm

/-- At most one `napplet.hello` per iframe: a hello on an already-bound frame tears
it down (NIP-5D §Identity 4–6). -/
theorem revoke_second_hello {w : WindowId} {id : Identity} {ex : List Domain} {p : PortId}
    {ld : Bool} {ports : List PortId} (h : s.frames w = some (.live id ex (some p) ld)) :
    let r := step c cfg s (.hello w ports)
    r.1.frames w = some .removed ∧ r.1.bindings p = none ∧ r.1.grants p = [] ∧
    r.2 = [.closePort p, .removeFrame w] := by
  simp [step, revoke, h]

/-- Any other window-level message after handoff tears the frame down. -/
theorem revoke_window_msg {w : WindowId} {id : Identity} {ex : List Domain} {p : PortId}
    {ld : Bool} (h : s.frames w = some (.live id ex (some p) ld)) :
    let r := step c cfg s (.windowMsg w)
    r.1.frames w = some .removed ∧ r.1.bindings p = none ∧ r.1.grants p = [] ∧
    r.2 = [.closePort p, .removeFrame w] := by
  simp [step, revoke, h]

/-- A second `load` (navigation or reload) tears the frame down. -/
theorem revoke_second_load {w : WindowId} {id : Identity} {ex : List Domain} {p : PortId}
    (h : s.frames w = some (.live id ex (some p) true)) :
    let r := step c cfg s (.load w)
    r.1.frames w = some .removed ∧ r.1.bindings p = none ∧ r.1.grants p = [] ∧
    r.2 = [.closePort p, .removeFrame w] := by
  simp [step, revoke, h]

end local_props

/-! ## Inductive invariant -/

/-- Shell-state invariant. -/
structure Inv (c : Crypto) (cfg : ShellConfig) (s : ShellState) : Prop where
  /-- Every binding points at a live frame holding that port. -/
  bind_frame : ∀ p b, s.bindings p = some b →
    ∃ ld, s.frames b.window = some (.live b.identity b.exposed (some p) ld)
  /-- Every frame holding a port is bound on that port. -/
  frame_bind : ∀ w id ex p ld, s.frames w = some (.live id ex (some p) ld) →
    s.bindings p = some ⟨w, id, ex⟩
  /-- Grants exist only on bound ports. -/
  grants_bound : ∀ p, s.bindings p = none → s.grants p = []
  /-- Every live frame's identity came from verified bytes, with policy exposure. -/
  frame_verified : ∀ w id ex po ld, s.frames w = some (.live id ex po ld) →
    Verified c id ∧ ex = exposedFor cfg id

theorem Inv.init (c : Crypto) (cfg : ShellConfig) : Inv c cfg .init where
  bind_frame := by simp [ShellState.init]
  frame_bind := by simp [ShellState.init]
  grants_bound := by simp [ShellState.init]
  frame_verified := by simp [ShellState.init]

theorem admit_ok {c : Crypto} {cfg : ShellConfig} {m : ManifestEvent} {bytes : Bytes}
    {id : Identity} {ex : List Domain} (h : admit c cfg m bytes = .ok (id, ex)) :
    Verified c id ∧ ex = exposedFor cfg id := by
  unfold admit at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i v hv
    have key : id = v.identity ∧ ex = exposedFor cfg v.identity := by
      split at h
      · split at h
        · simp at h
        · simp at h; exact ⟨h.1.symm, h.2.symm⟩
      · simp at h; exact ⟨h.1.symm, h.2.symm⟩
    obtain ⟨rfl, rfl⟩ := key
    exact ⟨⟨m, bytes, v, hv, rfl⟩, rfl⟩

/-- Created frames get exactly the policy exposure, never more. -/
theorem create_exposure {c : Crypto} {cfg : ShellConfig} {s : ShellState} {w : WindowId}
    {m : ManifestEvent} {bytes : Bytes} {id : Identity} {ex : List Domain}
    (h : Output.iframeCreated w id ex ∈ (step c cfg s (.create w m bytes)).2) :
    Verified c id ∧ ex = exposedFor cfg id := by
  simp only [step] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i id' ex' ha
      have hv := admit_ok ha
      simp only [List.mem_singleton, Output.iframeCreated.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      exact hv

/-- `revoke` preserves the invariant. -/
theorem Inv.revoke {c : Crypto} {cfg : ShellConfig} {s : ShellState} (hi : Inv c cfg s)
    (w : WindowId) : Inv c cfg (revoke s w).1 := by
  unfold Napplet.revoke
  split
  · rename_i id ex p ld hf
    have hb := hi.frame_bind _ _ _ _ _ hf
    constructor
    · intro q b hq
      simp only [upd] at hq ⊢
      split at hq
      · simp at hq
      · rename_i hqp
        obtain ⟨ld', hl⟩ := hi.bind_frame q b hq
        refine ⟨ld', ?_⟩
        have : b.window ≠ w := by
          intro hw
          rw [hw, hf] at hl
          simp at hl
          exact hqp hl.2.2.1.symm
        simp [this, hl]
    · intro w' id' ex' q ld' hf'
      simp only [upd] at hf' ⊢
      split at hf'
      · simp at hf'
      · rename_i hw
        have := hi.frame_bind _ _ _ _ _ hf'
        have hqp : q ≠ p := by
          intro hq; subst hq
          rw [hb] at this
          simp at this
          exact hw this.1.symm
        simp [hqp, this]
    · intro q hq
      simp only [upd] at hq ⊢
      split
      · rfl
      · rename_i hqp
        simp [hqp] at hq
        exact hi.grants_bound q hq
    · intro w' id' ex' po ld' hf'
      simp only [upd] at hf'
      split at hf'
      · simp at hf'
      · exact hi.frame_verified _ _ _ _ _ hf'
  · rename_i id ex ld hf
    constructor
    · intro q b hq
      obtain ⟨ld', hl⟩ := hi.bind_frame q b hq
      refine ⟨ld', ?_⟩
      have : b.window ≠ w := by
        intro hw; rw [hw, hf] at hl; simp at hl
      simp [upd, this, hl]
    · intro w' id' ex' q ld' hf'
      simp only [upd] at hf'
      split at hf'
      · simp at hf'
      · exact hi.frame_bind _ _ _ _ _ hf'
    · exact hi.grants_bound
    · intro w' id' ex' po ld' hf'
      simp only [upd] at hf'
      split at hf'
      · simp at hf'
      · exact hi.frame_verified _ _ _ _ _ hf'
  · exact hi

/-- The invariant is preserved by every step. -/
theorem Inv.step {c : Crypto} {cfg : ShellConfig} {s : ShellState} (hi : Inv c cfg s)
    (e : Event) : Inv c cfg (step c cfg s e).1 := by
  cases e with
  | create w m bytes =>
    simp only [Napplet.step]
    split
    · exact hi
    · rename_i hn
      split
      · exact hi
      · rename_i id ex ha
        have hv := admit_ok ha
        constructor
        · intro q b hq
          obtain ⟨ld, hl⟩ := hi.bind_frame q b hq
          refine ⟨ld, ?_⟩
          have : b.window ≠ w := by intro hw; rw [hw, hn] at hl; simp at hl
          simp [upd, this, hl]
        · intro w' id' ex' q ld hf
          simp only [upd] at hf
          split at hf
          · simp at hf
          · exact hi.frame_bind _ _ _ _ _ hf
        · exact hi.grants_bound
        · intro w' id' ex' po ld hf
          simp only [upd] at hf
          split at hf
          · simp at hf; obtain ⟨rfl, rfl, -, -⟩ := hf; exact hv
          · exact hi.frame_verified _ _ _ _ _ hf
  | load w =>
    simp only [Napplet.step]
    split
    · rename_i id ex po hf
      constructor
      · intro q b hq
        obtain ⟨ld, hl⟩ := hi.bind_frame q b hq
        by_cases hw : b.window = w
        · rw [hw, hf] at hl
          simp at hl
          obtain ⟨h1, h2, h3, -⟩ := hl
          exact ⟨true, by simp [upd, hw, h1, h2, h3]⟩
        · exact ⟨ld, by simp [upd, hw, hl]⟩
      · intro w' id' ex' q ld hf'
        simp only [upd] at hf'
        split at hf'
        · rename_i hw
          subst hw
          simp at hf'
          obtain ⟨rfl, rfl, rfl, -⟩ := hf'
          exact hi.frame_bind _ _ _ _ _ hf
        · exact hi.frame_bind _ _ _ _ _ hf'
      · exact hi.grants_bound
      · intro w' id' ex' po' ld hf'
        simp only [upd] at hf'
        split at hf'
        · simp at hf'
          obtain ⟨rfl, rfl, -, -⟩ := hf'
          exact hi.frame_verified _ _ _ _ _ hf
        · exact hi.frame_verified _ _ _ _ _ hf'
    · exact hi.revoke w
    · exact hi
  | hello w ports =>
    simp only [Napplet.step]
    split
    · rename_i id ex ld hf
      split
      · rename_i p
        split
        · rename_i hpn
          constructor
          · intro q b hq
            simp only [upd] at hq ⊢
            split at hq
            · rename_i hqp
              subst hqp
              simp at hq
              subst hq
              exact ⟨ld, by simp⟩
            · rename_i hqp
              obtain ⟨ld', hl⟩ := hi.bind_frame q b hq
              have : b.window ≠ w := by intro hw; rw [hw, hf] at hl; simp at hl
              exact ⟨ld', by simp [this, hl]⟩
          · intro w' id' ex' q ld' hf'
            simp only [upd] at hf' ⊢
            split at hf'
            · rename_i hw
              subst hw
              simp at hf'
              obtain ⟨rfl, rfl, rfl, -⟩ := hf'
              simp
            · rename_i hw
              have hb := hi.frame_bind _ _ _ _ _ hf'
              have : q ≠ p := by intro hq; subst hq; rw [hb] at hpn; simp at hpn
              simp [this, hb]
          · intro q hq
            simp only [upd] at hq
            split at hq
            · simp at hq
            · exact hi.grants_bound q hq
          · intro w' id' ex' po ld' hf'
            simp only [upd] at hf'
            split at hf'
            · simp at hf'
              obtain ⟨rfl, rfl, -, -⟩ := hf'
              exact hi.frame_verified _ _ _ _ _ hf
            · exact hi.frame_verified _ _ _ _ _ hf'
        · exact hi
      · exact hi
    · exact hi.revoke w
    · exact hi
  | windowMsg w =>
    simp only [Napplet.step]
    split
    · exact hi.revoke w
    · exact hi
  | portClosed p =>
    simp only [Napplet.step]
    split
    · exact hi.revoke _
    · exact hi
  | nap p env =>
    simp only [Napplet.step]
    split
    · split
      · split <;> exact hi
      · exact hi
    · exact hi
  | grant p g =>
    simp only [Napplet.step]
    split
    · rename_i b hb
      constructor
      · exact hi.bind_frame
      · exact hi.frame_bind
      · intro q hq
        simp only [upd]
        split
        · rename_i hqp; subst hqp; simp [hb] at hq
        · exact hi.grants_bound q hq
      · exact hi.frame_verified
    · exact hi

theorem Reachable.inv {c : Crypto} {cfg : ShellConfig} {s : ShellState}
    (h : Reachable c cfg s) : Inv c cfg s := by
  induction h with
  | init => exact Inv.init c cfg
  | step e _ ih => exact ih.step e

/-! ## Global properties over reachable states -/

/-- The sender attached to any dispatched NAP message was computed by the runtime from
verified artifact bytes; it is never taken from a host, gateway or message. -/
theorem dispatch_sender_verified {c : Crypto} {cfg : ShellConfig} {s : ShellState}
    (hr : Reachable c cfg s) {e : Event} {p : PortId} {sender : Identity} {d : Domain}
    {env : Envelope} (h : Output.dispatch p sender d env ∈ (step c cfg s e).2) :
    Verified c sender ∧ d ∈ exposedFor cfg sender := by
  obtain ⟨-, b, hb, rfl, hd⟩ := dispatch_inv h
  have hi := hr.inv
  obtain ⟨ld, hf⟩ := hi.bind_frame p b hb
  obtain ⟨hv, hex⟩ := hi.frame_verified _ _ _ _ _ hf
  exact ⟨hv, hex ▸ hd⟩

/-- Grants never outlive their binding: after a port closes, nothing remains. -/
theorem revoke_port_closed {c : Crypto} {cfg : ShellConfig} {s : ShellState}
    (hr : Reachable c cfg s) {p : PortId} {b : Binding} (hb : s.bindings p = some b) :
    let r := step c cfg s (.portClosed p)
    r.1.bindings p = none ∧ r.1.grants p = [] ∧ r.1.frames b.window = some .removed ∧
    Output.closePort p ∈ r.2 := by
  obtain ⟨ld, hf⟩ := hr.inv.bind_frame p b hb
  simp [step, hb, revoke, hf]

/-- In any reachable state, a port carries grants only while bound. -/
theorem grants_only_bound {c : Crypto} {cfg : ShellConfig} {s : ShellState}
    (hr : Reachable c cfg s) {p : PortId} (h : s.grants p ≠ []) : (s.bindings p).isSome := by
  cases hb : s.bindings p with
  | none => exact absurd (hr.inv.grants_bound p hb) h
  | some _ => rfl

/-- A port is bound to at most one window. -/
theorem binding_unique_window {c : Crypto} {cfg : ShellConfig} {s : ShellState}
    (hr : Reachable c cfg s) {w₁ w₂ : WindowId} {id₁ id₂ : Identity} {ex₁ ex₂ : List Domain}
    {p : PortId} {l₁ l₂ : Bool}
    (h₁ : s.frames w₁ = some (.live id₁ ex₁ (some p) l₁))
    (h₂ : s.frames w₂ = some (.live id₂ ex₂ (some p) l₂)) : w₁ = w₂ := by
  have a := hr.inv.frame_bind _ _ _ _ _ h₁
  have b := hr.inv.frame_bind _ _ _ _ _ h₂
  rw [a] at b
  simp at b
  exact b.1

end Napplet
