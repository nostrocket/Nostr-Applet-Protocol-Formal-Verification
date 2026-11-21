import Napplet.Basic

/-!
# NAP-NOTIFY (`notify`, PR napplet/naps#11 branch `nub-notify`)

Shell-rendered notifications.

Results:
* `render_attributed`, `render_sanitized`, `render_actions_capped`: every rendered
  notification names its originating napplet, has sanitised text, and shows at
  most three actions.
* `send_requires_permission`: nothing is created without permission or under rate
  limit; an error means nothing was created (`send_error_creates_nothing`).
* `dismiss_only_own`: a napplet can only dismiss its own notifications; unknown or
  foreign ids are silently ignored.
* `cleanup_removes_all`: iframe removal drops every notification of that napplet and
  no other.
* `send_same_id`.
-/

namespace Napplet.NapNotify

inductive Priority where
  | low | normal | high | urgent
  deriving DecidableEq, Repr

structure Action where
  id : String
  label : String
  deriving DecidableEq, Repr

structure NotificationPayload where
  title : String
  body : Option String := none
  actions : List Action := []
  priority : Priority := .normal
  deriving DecidableEq, Repr

structure Shown where
  nid : Nat
  owner : Endpoint
  title : String
  body : Option String
  actions : List Action
  priority : Priority
  deriving DecidableEq, Repr

structure NotifyEnv where
  /-- Strip HTML / script from text. -/
  sanitize : String → String
  permitted : Endpoint → Bool
  rateLimited : Endpoint → Priority → Bool

structure NotifyState where
  shown : List Shown
  next : Nat

inductive NotifyOut where
  | render (n : Shown)
  | hide (nid : Nat)
  | sendResult (to : Endpoint) (id : String) (nid : Option Nat) (error : Option String)
  deriving DecidableEq, Repr

def send (env : NotifyEnv) (s : NotifyState) (sender : Endpoint) (id : String)
    (p : NotificationPayload) : NotifyState × List NotifyOut :=
  if env.permitted sender = false then (s, [.sendResult sender id none (some "permission denied")])
  else if env.rateLimited sender p.priority then (s, [.sendResult sender id none (some "rate limited")])
  else
    let n : Shown := ⟨s.next, sender, env.sanitize p.title, p.body.map env.sanitize,
      p.actions.take 3, p.priority⟩
    ({ shown := n :: s.shown, next := s.next + 1 },
     [.render n, .sendResult sender id (some s.next) none])

/-- Dismiss: only the caller's own notifications; anything else is ignored. -/
def dismiss (s : NotifyState) (sender : Endpoint) (nid : Nat) : NotifyState × List NotifyOut :=
  if s.shown.any (fun n => n.nid == nid && n.owner == sender) then
    ({ s with shown := s.shown.filter (·.nid != nid) }, [.hide nid])
  else (s, [])

/-- Iframe removal: drop every notification the napplet owns. -/
def cleanup (s : NotifyState) (e : Endpoint) : NotifyState × List NotifyOut :=
  ({ s with shown := s.shown.filter (·.owner != e) },
   (s.shown.filter (·.owner == e)).map fun n => .hide n.nid)

theorem send_render {env : NotifyEnv} {s : NotifyState} {sender : Endpoint} {id : String}
    {p : NotificationPayload} {n : Shown} (h : NotifyOut.render n ∈ (send env s sender id p).2) :
    n.owner = sender ∧ n.title = env.sanitize p.title ∧ n.body = p.body.map env.sanitize ∧
    n.actions.length ≤ 3 ∧ env.permitted sender = true ∧ env.rateLimited sender p.priority = false := by
  unfold send at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h1 h2
      simp at h
      subst h
      exact ⟨rfl, rfl, rfl, List.length_take_le _ _, by simpa using h1, by simpa using h2⟩

theorem render_attributed {env : NotifyEnv} {s : NotifyState} {sender : Endpoint} {id : String}
    {p : NotificationPayload} {n : Shown} (h : NotifyOut.render n ∈ (send env s sender id p).2) :
    n.owner = sender := (send_render h).1

theorem render_sanitized {env : NotifyEnv} {s : NotifyState} {sender : Endpoint} {id : String}
    {p : NotificationPayload} {n : Shown} (h : NotifyOut.render n ∈ (send env s sender id p).2) :
    n.title = env.sanitize p.title ∧ n.body = p.body.map env.sanitize :=
  ⟨(send_render h).2.1, (send_render h).2.2.1⟩

theorem render_actions_capped {env : NotifyEnv} {s : NotifyState} {sender : Endpoint}
    {id : String} {p : NotificationPayload} {n : Shown}
    (h : NotifyOut.render n ∈ (send env s sender id p).2) : n.actions.length ≤ 3 :=
  (send_render h).2.2.2.1

theorem send_requires_permission {env : NotifyEnv} {s : NotifyState} {sender : Endpoint}
    {id : String} {p : NotificationPayload} {n : Shown}
    (h : NotifyOut.render n ∈ (send env s sender id p).2) :
    env.permitted sender = true ∧ env.rateLimited sender p.priority = false :=
  ⟨(send_render h).2.2.2.2.1, (send_render h).2.2.2.2.2⟩

theorem send_error_creates_nothing {env : NotifyEnv} {s : NotifyState} {sender : Endpoint}
    {id : String} {p : NotificationPayload} {e : String}
    (h : NotifyOut.sendResult sender id none (some e) ∈ (send env s sender id p).2) :
    (send env s sender id p).1 = s := by
  unfold send at h ⊢
  split
  · rfl
  · split
    · rfl
    · rename_i h1 h2
      simp [h1, h2] at h

/-- A napplet can only dismiss notifications it owns. -/
theorem dismiss_only_own {s : NotifyState} {sender : Endpoint} {nid : Nat}
    (h : (dismiss s sender nid).2 ≠ []) : ∃ n ∈ s.shown, n.nid = nid ∧ n.owner = sender := by
  unfold dismiss at h
  split at h
  · rename_i hany
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hany
    obtain ⟨n, hn, h1, h2⟩ := hany
    exact ⟨n, hn, h1, h2⟩
  · simp at h

theorem dismiss_foreign_ignored {s : NotifyState} {sender : Endpoint} {nid : Nat}
    (h : ∀ n ∈ s.shown, n.nid = nid → n.owner ≠ sender) : dismiss s sender nid = (s, []) := by
  unfold dismiss
  split
  · rename_i hany
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hany
    obtain ⟨n, hn, h1, h2⟩ := hany
    exact absurd h2 (h n hn h1)
  · rfl

theorem cleanup_removes_all (s : NotifyState) (e : Endpoint) :
    (∀ n ∈ (cleanup s e).1.shown, n.owner ≠ e) ∧
    (∀ n ∈ s.shown, n.owner ≠ e → n ∈ (cleanup s e).1.shown) := by
  constructor
  · intro n hn
    simp [cleanup] at hn
    exact hn.2
  · intro n hn hne
    simp [cleanup, hn, hne]

theorem send_same_id (env : NotifyEnv) (s : NotifyState) (sender : Endpoint) (id : String)
    (p : NotificationPayload) :
    ∃ nid e, NotifyOut.sendResult sender id nid e ∈ (send env s sender id p).2 := by
  unfold send
  split
  · exact ⟨_, _, List.mem_singleton_self _⟩
  · split
    · exact ⟨_, _, List.mem_singleton_self _⟩
    · exact ⟨_, _, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩

end Napplet.NapNotify
