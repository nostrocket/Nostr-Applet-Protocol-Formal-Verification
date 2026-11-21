import Napplet.Basic

/-!
# NAP-MEDIA (`media`, PR napplet/naps#10 branch `nub-media`)

Media sessions with an explicit owner (shell or napplet), canonical shell-assigned
ids, retirement and focus handling.

Results:
* `Inv` (ids below `next`, live and retired disjoint, live ids unique) is preserved
  by every operation.
* `create_fresh`: canonical ids are never reused, including retired ones.
* `retire_once`: exactly one `ended` per session; retiring again does nothing.
* `retired_silent`: commands and focus events for a retired id produce nothing.
* `ops_preserve_owner`: no operation changes a session's owner or endpoint.
* `fetch_only_shell_owned`: the shell fetches a source only for shell-owned sessions.
* `resume_only_after_focus_pause`, `user_pause_blocks_resume`: focus regain resumes
  only playback that focus loss paused, and never after a user pause.
-/

namespace Napplet.NapMedia

inductive Owner where
  | shell
  | napplet
  deriving DecidableEq, Repr

inductive Status where
  | playing | paused | stopped | buffering
  deriving DecidableEq, Repr

inductive Reason where
  | user | ended | error | preempted | focusLost | focusGained | destroyed | backendExited | policy
  deriving DecidableEq, Repr

inductive Action where
  | play | pause | stop | next | prev | seek | volume
  deriving DecidableEq, Repr

structure Session where
  id : Nat
  endpoint : Endpoint
  owner : Owner
  status : Status
  pausedByFocus : Bool
  deriving DecidableEq, Repr

structure MediaState where
  live : List Session
  retired : List Nat
  next : Nat

inductive MediaOut where
  | createResult (to : Endpoint) (id : String) (sid : Option Nat) (error : Option String)
  | fetchSource (sid : Nat)
  | ended (to : Endpoint) (sid : Nat) (reason : Reason)
  | state (to : Endpoint) (sid : Nat) (status : Status) (reason : Option Reason)
  | command (to : Endpoint) (sid : Nat) (action : Action) (reason : Option Reason)
  deriving DecidableEq, Repr

def find (s : MediaState) (sid : Nat) : Option Session := s.live.find? (·.id == sid)

/-- Update the live session `sid` without touching its id, owner or endpoint. -/
def modify (s : MediaState) (sid : Nat) (st : Status) (pbf : Bool) : MediaState :=
  { s with live := s.live.map fun x => if x.id = sid then { x with status := st, pausedByFocus := pbf } else x }

def create (s : MediaState) (sender : Endpoint) (id : String) (owner : Owner) (hasSource : Bool)
    (consentOk : Bool) : MediaState × List MediaOut :=
  if owner = .shell ∧ hasSource = false then (s, [.createResult sender id none (some "missing source")])
  else if consentOk = false then (s, [.createResult sender id none (some "autoplay denied")])
  else
    let sid := s.next
    ({ s with live := ⟨sid, sender, owner, .stopped, false⟩ :: s.live, next := s.next + 1 },
     .createResult sender id (some sid) none :: (if owner = .shell then [.fetchSource sid] else []))

def retire (s : MediaState) (sid : Nat) (r : Reason) : MediaState × List MediaOut :=
  match find s sid with
  | none => (s, [])
  | some x =>
    ({ s with live := s.live.filter (·.id != sid), retired := sid :: s.retired },
     [.ended x.endpoint sid r])

/-- A napplet commands a shell-owned session it owns. Anything else is ignored. -/
def command (s : MediaState) (sender : Endpoint) (sid : Nat) (a : Action) :
    MediaState × List MediaOut :=
  match find s sid with
  | none => (s, [])
  | some x =>
    if x.endpoint ≠ sender ∨ x.owner ≠ .shell then (s, [])
    else
      let st := match a with
        | .play => Status.playing | .pause => .paused | .stop => .stopped | _ => x.status
      (modify s sid st false, [.state x.endpoint sid st (some .user)])

def focusLost (s : MediaState) (sid : Nat) : MediaState × List MediaOut :=
  match find s sid with
  | none => (s, [])
  | some x =>
    if x.status ≠ .playing then (s, [])
    else
      (modify s sid .paused true,
       [match x.owner with
        | .shell => .state x.endpoint sid .paused (some .focusLost)
        | .napplet => .command x.endpoint sid .pause (some .focusLost)])

def focusGained (s : MediaState) (sid : Nat) : MediaState × List MediaOut :=
  match find s sid with
  | none => (s, [])
  | some x =>
    if x.pausedByFocus = false then (s, [])
    else
      (modify s sid .playing false,
       [match x.owner with
        | .shell => .state x.endpoint sid .playing (some .focusGained)
        | .napplet => .command x.endpoint sid .play (some .focusGained)])

/-- The user (or the napplet's own action) pauses: supersedes any focus pause. -/
def userPause (s : MediaState) (sid : Nat) : MediaState :=
  match find s sid with
  | none => s
  | some _ => modify s sid .paused false

/-! ### Invariant -/

structure Inv (s : MediaState) : Prop where
  live_lt : ∀ x ∈ s.live, x.id < s.next
  retired_lt : ∀ r ∈ s.retired, r < s.next
  disjoint : ∀ x ∈ s.live, x.id ∉ s.retired
  nodup : (s.live.map (·.id)).Nodup

theorem Inv.init : Inv ⟨[], [], 0⟩ := ⟨by simp, by simp, by simp, by simp⟩

theorem modify_ids (s : MediaState) (sid : Nat) (st : Status) (b : Bool) :
    (modify s sid st b).live.map (·.id) = s.live.map (·.id) := by
  simp only [modify, List.map_map]
  congr 1
  funext x
  simp only [Function.comp]
  split <;> rfl

theorem mem_modify {s : MediaState} {sid : Nat} {st : Status} {b : Bool} {x : Session}
    (h : x ∈ (modify s sid st b).live) :
    ∃ y ∈ s.live, y.id = x.id ∧ y.owner = x.owner ∧ y.endpoint = x.endpoint := by
  simp only [modify, List.mem_map] at h
  obtain ⟨y, hy, hx⟩ := h
  refine ⟨y, hy, ?_⟩
  split at hx <;> (subst hx; simp)

theorem Inv.modify {s : MediaState} (hi : Inv s) (sid : Nat) (st : Status) (b : Bool) :
    Inv (modify s sid st b) := by
  constructor
  · intro x hx
    obtain ⟨y, hy, hid, -, -⟩ := mem_modify hx
    rw [← hid]; exact hi.live_lt y hy
  · exact hi.retired_lt
  · intro x hx
    obtain ⟨y, hy, hid, -, -⟩ := mem_modify hx
    rw [← hid]; exact hi.disjoint y hy
  · rw [modify_ids]; exact hi.nodup

theorem find_some {s : MediaState} {sid : Nat} {x : Session} (h : find s sid = some x) :
    x ∈ s.live ∧ x.id = sid := by
  have := List.find?_some h
  simp only [beq_iff_eq] at this
  exact ⟨List.mem_of_find?_eq_some h, this⟩

theorem Inv.create {s : MediaState} (hi : Inv s) (sender : Endpoint) (id : String) (o : Owner)
    (hs c : Bool) : Inv (create s sender id o hs c).1 := by
  unfold Napplet.NapMedia.create
  split
  · exact hi
  · split
    · exact hi
    · constructor
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · have := hi.live_lt x hx; simp; omega
      · intro r hr
        have := hi.retired_lt r hr; simp; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · intro hr; have := hi.retired_lt _ hr; simp at this
        · exact hi.disjoint x hx
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, hi.nodup⟩
        simp only [List.mem_map, not_exists, not_and]
        intro x hx heq
        have := hi.live_lt x hx
        omega

theorem Inv.retire {s : MediaState} (hi : Inv s) (sid : Nat) (r : Reason) : Inv (retire s sid r).1 := by
  unfold Napplet.NapMedia.retire
  split
  · exact hi
  · rename_i x hx
    have ⟨hxl, hxid⟩ := find_some hx
    constructor
    · intro y hy
      simp only [List.mem_filter] at hy
      exact hi.live_lt y hy.1
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [← hxid]; exact hi.live_lt x hxl
      · exact hi.retired_lt q hq
    · intro y hy
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at hy
      simp only [List.mem_cons, not_or]
      exact ⟨hy.2, hi.disjoint y hy.1⟩
    · exact hi.nodup.sublist ((List.filter_sublist).map _)

theorem Inv.command {s : MediaState} (hi : Inv s) (e : Endpoint) (sid : Nat) (a : Action) :
    Inv (command s e sid a).1 := by
  unfold Napplet.NapMedia.command
  split
  · exact hi
  · split
    · exact hi
    · exact hi.modify _ _ _

theorem Inv.focusLost {s : MediaState} (hi : Inv s) (sid : Nat) : Inv (focusLost s sid).1 := by
  unfold Napplet.NapMedia.focusLost
  split
  · exact hi
  · split
    · exact hi
    · exact hi.modify _ _ _

theorem Inv.focusGained {s : MediaState} (hi : Inv s) (sid : Nat) : Inv (focusGained s sid).1 := by
  unfold Napplet.NapMedia.focusGained
  split
  · exact hi
  · split
    · exact hi
    · exact hi.modify _ _ _

theorem Inv.userPause {s : MediaState} (hi : Inv s) (sid : Nat) : Inv (userPause s sid) := by
  unfold Napplet.NapMedia.userPause
  split
  · exact hi
  · exact hi.modify _ _ _

/-! ### Properties -/

/-- Canonical ids are fresh: never a live id and never a retired one. -/
theorem create_fresh {s : MediaState} (hi : Inv s) {sender : Endpoint} {id : String} {o : Owner}
    {hs c : Bool} {sid : Nat} {e : Option String}
    (h : MediaOut.createResult sender id (some sid) e ∈ (create s sender id o hs c).2) :
    (∀ x ∈ s.live, x.id ≠ sid) ∧ sid ∉ s.retired := by
  unfold create at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · simp only [MediaOut.createResult.injEq, true_and, Option.some.injEq] at h
        obtain ⟨rfl, -⟩ := h
        refine ⟨fun x hx heq => ?_, fun hr => ?_⟩
        · have := hi.live_lt x hx; omega
        · have := hi.retired_lt _ hr; omega
      · split at h <;> simp at h

theorem find_retire_none (s : MediaState) (sid : Nat) (r : Reason) :
    find (retire s sid r).1 sid = none := by
  unfold retire
  split
  · assumption
  · simp [find, List.find?_eq_none]

/-- A session ends exactly once. -/
theorem retire_once (s : MediaState) (sid : Nat) (r r' : Reason) :
    (retire (retire s sid r).1 sid r').2 = [] := by
  have h := find_retire_none s sid r
  generalize (retire s sid r).1 = t at h ⊢
  simp [retire, h]

theorem find_retired {s : MediaState} (hi : Inv s) {sid : Nat} (hr : sid ∈ s.retired) :
    find s sid = none := by
  cases h : find s sid with
  | none => rfl
  | some x =>
    have ⟨hxl, hxid⟩ := find_some h
    exact absurd (hxid ▸ hr) (hi.disjoint x hxl)

/-- Nothing is sent for a retired session. -/
theorem retired_silent {s : MediaState} (hi : Inv s) {sid : Nat} (hr : sid ∈ s.retired)
    (e : Endpoint) (a : Action) :
    (command s e sid a).2 = [] ∧ (focusLost s sid).2 = [] ∧ (focusGained s sid).2 = [] ∧
    (retire s sid .user).2 = [] := by
  have hf := find_retired hi hr
  simp [command, focusLost, focusGained, retire, hf]

/-- Commands never change a session's owner or endpoint. -/
theorem ops_preserve_owner {s : MediaState} {e : Endpoint} {sid : Nat} {a : Action} {x : Session}
    (h : x ∈ (command s e sid a).1.live) :
    ∃ y ∈ s.live, y.id = x.id ∧ y.owner = x.owner ∧ y.endpoint = x.endpoint := by
  unfold command at h
  split at h
  · exact ⟨x, h, rfl, rfl, rfl⟩
  · split at h
    · exact ⟨x, h, rfl, rfl, rfl⟩
    · exact mem_modify h

/-- The shell fetches sources only for shell-owned sessions. -/
theorem fetch_only_shell_owned {s : MediaState} {sender : Endpoint} {id : String} {o : Owner}
    {hs c : Bool} {sid : Nat} (h : MediaOut.fetchSource sid ∈ (create s sender id o hs c).2) :
    o = .shell ∧ hs = true := by
  unfold create at h
  split at h
  · simp at h
  · rename_i h1
    split at h
    · simp at h
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      split at h
      · rename_i ho
        refine ⟨ho, ?_⟩
        cases hs
        · exact absurd ⟨ho, rfl⟩ h1
        · rfl
      · simp at h

/-- Focus regain resumes only playback that focus loss paused. -/
theorem resume_only_after_focus_pause {s : MediaState} {sid : Nat} {o : MediaOut}
    (h : o ∈ (focusGained s sid).2) : ∃ x, find s sid = some x ∧ x.pausedByFocus = true := by
  unfold focusGained at h
  split at h
  · simp at h
  · rename_i x hx
    split at h
    · simp at h
    · rename_i hp
      exact ⟨x, hx, by simpa using hp⟩

theorem find?_map_id (l : List Session) (f : Session → Session) (hf : ∀ y, (f y).id = y.id)
    (sid : Nat) : (l.map f).find? (·.id == sid) = (l.find? (·.id == sid)).map f := by
  induction l with
  | nil => rfl
  | cons y ys ih => simp only [List.map_cons, List.find?_cons, hf]; split <;> simp_all

theorem find_modify {s : MediaState} {sid : Nat} {st : Status} {b : Bool}
    {x : Session} (hx : find s sid = some x) :
    find (modify s sid st b) sid = some { x with status := st, pausedByFocus := b } := by
  have ⟨_, hxid⟩ := find_some hx
  unfold find modify at *
  simp only
  rw [find?_map_id _ _ (by intro y; split <;> rfl), hx]
  simp [hxid]

/-- After a user pause, focus regain does not resume. -/
theorem user_pause_blocks_resume {s : MediaState} (sid : Nat) :
    (focusGained (userPause s sid) sid).2 = [] := by
  unfold userPause
  split
  · rename_i hn; simp [focusGained, hn]
  · rename_i x hx
    unfold focusGained
    rw [find_modify hx]
    simp

end Napplet.NapMedia
