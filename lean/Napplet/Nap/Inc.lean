/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-INC (`inc`): inter-napplet communication

The runtime passes the authenticated `sender` endpoint into `handle`; `IncReq` has no
sender field, so a napplet cannot set or forge it.

Results:
* `emit_delivery`: topic deliveries go only to exact-topic subscribers, never back to
  the emitter, always stamped with the authenticated sender.
* `open_ok`: on success `inc.channel.opened` is enqueued before the open result.
* `open_fail_unchanged`: a failed open creates no channel.
* `chEmit_delivery`: channel events go only to the other member, stamped with sender.
* `close_notifies_both`, `destroy_notifies_peers`, `destroy_clears`.
-/

namespace Napplet.NapInc

structure Channel where
  id : Nat
  a : Endpoint
  b : Endpoint
  deriving DecidableEq, Repr

structure IncState where
  subs : List (Endpoint × String)
  channels : List Channel
  next : Nat

inductive IncReq where
  | emit (topic : String) (payload : Option String)
  | subscribe (id : String) (topic : String)
  | unsubscribe (topic : String)
  | chOpen (id : String) (target : Endpoint)
  | chEmit (ch : Nat) (payload : Option String)
  | chClose (ch : Nat)
  deriving DecidableEq, Repr

inductive IncOut where
  | event (to : Endpoint) (topic : String) (sender : Endpoint) (payload : Option String)
  | subscribeResult (to : Endpoint) (id : String) (error : Option String)
  | opened (to : Endpoint) (ch : Nat) (peer : Endpoint)
  | openResult (to : Endpoint) (id : String) (ch : Option Nat) (peer : Option Endpoint)
      (error : Option String)
  | chEvent (to : Endpoint) (ch : Nat) (sender : Endpoint) (payload : Option String)
  | closed (to : Endpoint) (ch : Nat) (reason : Option String)
  deriving DecidableEq, Repr

/-- The other member of a channel, if `e` is a member. -/
def peerOf (c : Channel) (e : Endpoint) : Option Endpoint :=
  if c.a = e then some c.b else if c.b = e then some c.a else none

theorem peerOf_member {c : Channel} {e p : Endpoint} (h : peerOf c e = some p) :
    (c.a = e ∧ c.b = p) ∨ (c.b = e ∧ c.a = p) := by
  unfold peerOf at h
  split at h
  · simp at h; exact .inl ⟨by assumption, h⟩
  · split at h
    · simp at h; exact .inr ⟨by assumption, h⟩
    · simp at h

/-- Handle one request from authenticated endpoint `sender`.
`live` says which endpoints exist; `acl` gates topic subscriptions. -/
def handle (live : Endpoint → Bool) (acl : Endpoint → String → Bool) (s : IncState)
    (sender : Endpoint) : IncReq → IncState × List IncOut
  | .emit t pl =>
    (s, (s.subs.filter fun x => x.2 == t && x.1 != sender).map fun x => .event x.1 t sender pl)
  | .subscribe id t =>
    if acl sender t then
      ({ s with subs := (sender, t) :: s.subs }, [.subscribeResult sender id none])
    else (s, [.subscribeResult sender id (some "topic rejected by ACL")])
  | .unsubscribe t =>
    ({ s with subs := s.subs.filter fun x => !(x.1 == sender && x.2 == t) }, [])
  | .chOpen id tgt =>
    if live tgt && tgt != sender then
      ({ s with channels := ⟨s.next, sender, tgt⟩ :: s.channels, next := s.next + 1 },
       [.opened tgt s.next sender, .openResult sender id (some s.next) (some tgt) none])
    else (s, [.openResult sender id none none (some "target not found")])
  | .chEmit ch pl =>
    match s.channels.find? (·.id == ch) with
    | some c =>
      match peerOf c sender with
      | some p => (s, [.chEvent p ch sender pl])
      | none => (s, [])
    | none => (s, [])
  | .chClose ch =>
    match s.channels.find? (·.id == ch) with
    | some c =>
      if (peerOf c sender).isSome then
        ({ s with channels := s.channels.filter (·.id != ch) },
         [.closed c.a ch none, .closed c.b ch none])
      else (s, [])
    | none => (s, [])

theorem emit_delivery {live : Endpoint → Bool} {acl : Endpoint → String → Bool} {s : IncState}
    {sender : Endpoint} {t : String} {pl : Option String} {o : IncOut}
    (h : o ∈ (handle live acl s sender (.emit t pl)).2) :
    ∃ to, o = .event to t sender pl ∧ to ≠ sender ∧ (to, t) ∈ s.subs := by
  simp only [handle, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨to, t'⟩, ⟨hm, ht, hne⟩, rfl⟩ := h
  simp only at ht hne
  subst ht
  exact ⟨to, rfl, hne, hm⟩

/-- On success, the target's `inc.channel.opened` precedes the caller's result. -/
theorem open_ok {live : Endpoint → Bool} {acl : Endpoint → String → Bool} {s : IncState}
    {sender tgt : Endpoint} {id : String} (hl : live tgt = true) (hne : tgt ≠ sender) :
    (handle live acl s sender (.chOpen id tgt)).2 =
      [.opened tgt s.next sender, .openResult sender id (some s.next) (some tgt) none] := by
  simp [handle, hl, hne]

theorem open_fail_unchanged {live : Endpoint → Bool} {acl : Endpoint → String → Bool}
    {s : IncState} {sender tgt : Endpoint} {id : String}
    (h : ¬(live tgt = true ∧ tgt ≠ sender)) :
    handle live acl s sender (.chOpen id tgt) =
      (s, [.openResult sender id none none (some "target not found")]) := by
  simp only [handle]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    exact absurd hc h
  · rfl

theorem chEmit_delivery {live : Endpoint → Bool} {acl : Endpoint → String → Bool}
    {s : IncState} {sender : Endpoint} {ch : Nat} {pl : Option String} {o : IncOut}
    (h : o ∈ (handle live acl s sender (.chEmit ch pl)).2) :
    ∃ c p, c ∈ s.channels ∧ c.id = ch ∧ peerOf c sender = some p ∧
      o = .chEvent p ch sender pl := by
  simp only [handle] at h
  split at h
  · rename_i c hc
    split at h
    · rename_i p hp
      simp at h
      have hmem := List.mem_of_find?_eq_some hc
      have hid := List.find?_some hc
      simp at hid
      exact ⟨c, p, hmem, hid, hp, h⟩
    · simp at h
  · simp at h

theorem close_notifies_both {live : Endpoint → Bool} {acl : Endpoint → String → Bool}
    {s : IncState} {sender : Endpoint} {ch : Nat} {c : Channel}
    (hc : s.channels.find? (·.id == ch) = some c) (hm : (peerOf c sender).isSome) :
    (handle live acl s sender (.chClose ch)).2 = [.closed c.a ch none, .closed c.b ch none] := by
  simp [handle, hc, hm]

/-- Endpoint destruction: drop its subscriptions and channels, tell each peer. -/
def destroy (s : IncState) (e : Endpoint) : IncState × List IncOut :=
  ({ subs := s.subs.filter (·.1 != e)
     channels := s.channels.filter fun c => !(c.a == e || c.b == e)
     next := s.next },
   (s.channels.filterMap fun c => (peerOf c e).map fun p => .closed p c.id (some "peer destroyed")))

theorem destroy_clears (s : IncState) (e : Endpoint) :
    (∀ x ∈ (destroy s e).1.subs, x.1 ≠ e) ∧
    (∀ c ∈ (destroy s e).1.channels, c.a ≠ e ∧ c.b ≠ e) := by
  constructor
  · intro x hx
    simp [destroy] at hx
    exact hx.2
  · intro c hc
    simp [destroy] at hc
    exact hc.2

theorem destroy_notifies_peers {s : IncState} {e p : Endpoint} {c : Channel}
    (hc : c ∈ s.channels) (hp : peerOf c e = some p) :
    IncOut.closed p c.id (some "peer destroyed") ∈ (destroy s e).2 := by
  simp only [destroy, List.mem_filterMap]
  exact ⟨c, hc, by simp [hp]⟩

end Napplet.NapInc
