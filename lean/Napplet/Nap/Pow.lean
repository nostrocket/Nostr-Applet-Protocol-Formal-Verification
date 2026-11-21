/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-POW (`pow`, PR napplet/naps#39 branch `nap-pow`)

NIP-13 proof-of-work mining in the shell. Hashing, nonce search and signing are
opaque.

Results:
* `submit_accepted`: a job is accepted only with a fresh per-napplet `jobId`, a
  target within the shell cap and room in the queue.
* `jobs_namespaced`: two napplets can use the same `jobId` without collision.
* `mine_done`: a finished event meets the target, carries the user's pubkey (stamped
  by the shell), exactly one `nonce` tag committing to the target, and every
  non-nonce tag from the template.
* `publish_verbatim`: `mineAndPublish` signs the mined event unchanged.
* `pushes_to_owner`: progress and results go only to the job's owner.
-/

namespace Napplet.NapPow

structure Template where
  kind : Nat
  content : String
  tags : List (List String)
  createdAt : Option Nat := none
  deriving DecidableEq, Repr

structure Unsigned where
  pubkey : Pubkey
  createdAt : Nat
  kind : Nat
  content : String
  tags : List (List String)
  deriving DecidableEq, Repr

structure Signed where
  event : Unsigned
  sig : String
  deriving DecidableEq, Repr

structure PowEnv where
  userPubkey : Pubkey
  now : Nat
  idOf : Unsigned → Hash
  leadingZeros : Hash → Nat
  /-- Nonce search over a committed event; `none` on timeout. -/
  search : Unsigned → Nat → Option String
  sign : Unsigned → String

structure PowCfg where
  maxTarget : Nat
  maxJobs : Nat

inductive Mode where
  | mine
  | mineAndPublish
  deriving DecidableEq, Repr

structure Job where
  owner : Endpoint
  jobId : String
  target : Nat
  template : Template
  mode : Mode
  deriving DecidableEq, Repr

inductive PowOut where
  | mineResult (to : Endpoint) (id jobId : String) (accepted : Bool) (error : Option String)
  | done (to : Endpoint) (jobId : String) (ev : Unsigned)
  | error (to : Endpoint) (jobId : String) (e : String)
  | publish (ev : Signed)
  deriving DecidableEq, Repr

def submit (cfg : PowCfg) (jobs : List Job) (sender : Endpoint) (id jobId : String) (t : Template)
    (target : Nat) (mode : Mode) : List Job × List PowOut :=
  if jobs.any (fun j => j.owner == sender && j.jobId == jobId) then
    (jobs, [.mineResult sender id jobId false (some "duplicate jobId")])
  else if target > cfg.maxTarget then (jobs, [.mineResult sender id jobId false (some "invalid target")])
  else if jobs.length ≥ cfg.maxJobs then (jobs, [.mineResult sender id jobId false (some "queue full")])
  else (⟨sender, jobId, target, t, mode⟩ :: jobs, [.mineResult sender id jobId true none])

theorem submit_accepted {cfg : PowCfg} {jobs : List Job} {sender : Endpoint} {id jobId : String}
    {t : Template} {target : Nat} {mode : Mode} {e : Option String}
    (h : PowOut.mineResult sender id jobId true e ∈ (submit cfg jobs sender id jobId t target mode).2) :
    (∀ j ∈ jobs, j.owner = sender → j.jobId ≠ jobId) ∧ target ≤ cfg.maxTarget ∧
      jobs.length < cfg.maxJobs := by
  unfold submit at h
  split at h
  · simp at h
  · rename_i h1
    split at h
    · simp at h
    · rename_i h2
      split at h
      · simp at h
      · rename_i h3
        simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, not_exists, not_and] at h1
        exact ⟨fun j hj ho hid => h1 j hj ho hid, by omega, by omega⟩

/-- Job ids are scoped per napplet: another napplet's job never blocks this one. -/
theorem jobs_namespaced {cfg : PowCfg} {jobs : List Job} {sender : Endpoint} {id jobId : String}
    {t : Template} {target : Nat} {mode : Mode} (hown : ∀ j ∈ jobs, j.owner ≠ sender)
    (ht : target ≤ cfg.maxTarget) (hq : jobs.length < cfg.maxJobs) :
    (submit cfg jobs sender id jobId t target mode).2 = [.mineResult sender id jobId true none] := by
  have h1 : jobs.any (fun j => j.owner == sender && j.jobId == jobId) = false := by
    simp only [List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
    intro j hj ho
    exact absurd ho (hown j hj)
  have h2 : ¬target > cfg.maxTarget := by omega
  have h3 : ¬jobs.length ≥ cfg.maxJobs := by omega
  simp [submit, h1, h2, h3]

/-- Replace any `nonce` tag with `["nonce", n, target]`. -/
def withNonce (tags : List (List String)) (n : String) (target : Nat) : List (List String) :=
  tags.filter (fun t => t.head? != some "nonce") ++ [["nonce", n, toString target]]

/-- Shell stamps pubkey and `created_at` when mining begins. -/
def stamp (env : PowEnv) (t : Template) : Unsigned :=
  ⟨env.userPubkey, t.createdAt.getD env.now, t.kind, t.content, t.tags⟩

/-- The committed event for nonce `n`. -/
def mined (env : PowEnv) (j : Job) (n : String) : Unsigned :=
  ⟨env.userPubkey, j.template.createdAt.getD env.now, j.template.kind, j.template.content,
   withNonce j.template.tags n j.target⟩

/-- Run a job to completion. -/
def run (env : PowEnv) (j : Job) : List PowOut :=
  match env.search (stamp env j.template) j.target with
  | none => [.error j.owner j.jobId "timeout"]
  | some n =>
    let ev := mined env j n
    if env.leadingZeros (env.idOf ev) < j.target then [.error j.owner j.jobId "timeout"]
    else match j.mode with
      | .mine => [.done j.owner j.jobId ev]
      | .mineAndPublish => [.publish ⟨ev, env.sign ev⟩, .done j.owner j.jobId ev]

theorem run_done {env : PowEnv} {j : Job} {to : Endpoint} {jid : String} {ev : Unsigned}
    (h : PowOut.done to jid ev ∈ run env j) :
    to = j.owner ∧ jid = j.jobId ∧ env.leadingZeros (env.idOf ev) ≥ j.target ∧
    ev.pubkey = env.userPubkey ∧
    ∃ n, ev.tags = withNonce j.template.tags n j.target := by
  unfold run at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i n hn
    split at h
    · simp at h
    · rename_i hz
      have key : to = j.owner ∧ jid = j.jobId ∧ ev = mined env j n := by
        split at h <;> simp at h <;> exact ⟨h.1, h.2.1, h.2.2⟩
      obtain ⟨rfl, rfl, rfl⟩ := key
      exact ⟨rfl, rfl, by omega, rfl, n, rfl⟩

/-- A finished event meets the target and commits to it in exactly one nonce tag. -/
theorem mine_done {env : PowEnv} {j : Job} {to : Endpoint} {jid : String} {ev : Unsigned}
    (h : PowOut.done to jid ev ∈ run env j) :
    env.leadingZeros (env.idOf ev) ≥ j.target ∧ ev.pubkey = env.userPubkey ∧
    (ev.tags.filter (fun t => t.head? == some "nonce")).length = 1 ∧
    (∀ t ∈ j.template.tags, t.head? ≠ some "nonce" → t ∈ ev.tags) := by
  obtain ⟨-, -, hz, hp, n, ht⟩ := run_done h
  refine ⟨hz, hp, ?_, ?_⟩
  · rw [ht]
    simp [withNonce, List.filter_append, List.filter_filter]
  · intro t ht' hn
    rw [ht]
    simp [withNonce, ht', hn]

/-- `mineAndPublish` signs the mined event verbatim, so the work stays valid. -/
theorem publish_verbatim {env : PowEnv} {j : Job} {s : Signed} (h : PowOut.publish s ∈ run env j) :
    j.mode = .mineAndPublish ∧ PowOut.done j.owner j.jobId s.event ∈ run env j ∧
    s.sig = env.sign s.event := by
  unfold run at h ⊢
  dsimp only at h ⊢
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hm
        simp at h
        subst h
        simp only [hm]
        split
        · exfalso; omega
        · simp

theorem pushes_to_owner {env : PowEnv} {j : Job} {o : PowOut} (h : o ∈ run env j) :
    (∃ jid ev, o = .done j.owner jid ev) ∨ (∃ jid e, o = .error j.owner jid e) ∨ (∃ s, o = .publish s) := by
  unfold run at h
  dsimp only at h
  split at h
  · simp at h; exact .inr (.inl ⟨_, _, h⟩)
  · split at h
    · simp at h; exact .inr (.inl ⟨_, _, h⟩)
    · split at h
      · simp at h; exact .inl ⟨_, _, h⟩
      · simp at h
        rcases h with h | h
        · exact .inr (.inr ⟨_, h⟩)
        · exact .inl ⟨_, _, h⟩

end Napplet.NapPow
