/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Shell

/-!
# NAP-SHELL (`shell`, optional)

`supports(domain)` is local. `shell.ready` → `shell.init` happens exactly once per
endpoint, and the environment describes only that napplet's own domains.
-/

namespace Napplet.NapShell

structure ShellEnvironment where
  capabilities : List Domain
  services : List String
  deriving DecidableEq, Repr

/-- `window.napplet.shell.supports(d)`: local, no wire message, works before init. -/
def supports (exposed : List Domain) (d : Domain) : Bool := decide (d ∈ exposed)

/-! ### `domains()` (PR #142)

"Returns a fresh, duplicate-free list of bare domains currently exposed to the calling
napplet. It is synchronous and local, MUST work before `shell.init`, and MUST agree with
`supports(domain)`." -/

/-- Remove duplicates, keeping the last occurrence of each element. -/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then dedup xs else x :: dedup xs

theorem mem_dedup {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α}, x ∈ dedup l ↔ x ∈ l
  | [] => by simp [dedup]
  | y :: ys => by
    have ih := @mem_dedup α _ x ys
    unfold dedup
    split
    · rename_i hy
      rw [ih]; constructor
      · exact List.mem_cons_of_mem _
      · intro h; rcases List.mem_cons.mp h with rfl | h
        · exact hy
        · exact h
    · simp [ih]

theorem nodup_dedup {α : Type} [DecidableEq α] : ∀ l : List α, (dedup l).Nodup
  | [] => by simp [dedup]
  | y :: ys => by
    unfold dedup
    split
    · exact nodup_dedup ys
    · rename_i hy
      exact List.nodup_cons.mpr ⟨fun h => hy (mem_dedup.mp h), nodup_dedup ys⟩

def domains (exposed : List Domain) : List Domain := dedup exposed

theorem domains_supports (exposed : List Domain) (d : Domain) :
    d ∈ domains exposed ↔ supports exposed d = true := by
  simp [domains, supports, mem_dedup]

theorem domains_nodup (exposed : List Domain) : (domains exposed).Nodup := nodup_dedup _

/-! ### `check(manifest)` (PR #142)

The target's declared `R` and `O` names are assessed against the exposure the shell's
policy gives the target identity (`exposedFor`), never the caller's. A name the shell
does not implement is known unavailable (it can never be exposed); a domain the policy
marks undisclosed is unknown. -/

inductive Status where
  | compatible | incompatible | unknown
  deriving DecidableEq, Repr

def Status.name : Status → String
  | .compatible => "compatible" | .incompatible => "incompatible" | .unknown => "unknown"

/-- `ShellCompatibility`. -/
structure Compatibility where
  status : Status
  missingRequired : List String
  missingOptional : List String
  deriving DecidableEq, Repr

/-- Availability of a declared domain name to the target: `some b` when known. -/
def availability (exposed undisclosed : List Domain) (n : String) : Option Bool :=
  match Domain.ofName? n with
  | none => some false
  | some d => if d ∈ undisclosed then none else some (decide (d ∈ exposed))

/-- Each known-unavailable name once. -/
def knownMissing (exposed undisclosed : List Domain) (ns : List String) : List String :=
  dedup (ns.filter fun n => availability exposed undisclosed n == some false)

def assess (exposed undisclosed : List Domain) (required optional : List String) : Compatibility :=
  let mr := knownMissing exposed undisclosed required
  { status :=
      if !mr.isEmpty then .incompatible
      else if required.all (fun n => availability exposed undisclosed n == some true) then .compatible
      else .unknown
    missingRequired := mr
    missingOptional := knownMissing exposed undisclosed optional }

theorem mem_knownMissing {e u : List Domain} {ns : List String} {n : String} :
    n ∈ knownMissing e u ns ↔ n ∈ ns ∧ availability e u n = some false := by
  simp [knownMissing, mem_dedup]

theorem knownMissing_nodup (e u : List Domain) (ns : List String) : (knownMissing e u ns).Nodup :=
  nodup_dedup _

/-- "`status` MUST be `incompatible` if any required domain is known unavailable". -/
theorem assess_incompatible_iff (e u : List Domain) (r o : List String) :
    (assess e u r o).status = .incompatible ↔ ∃ n ∈ r, availability e u n = some false := by
  constructor
  · intro h
    simp only [assess] at h
    split at h
    · rename_i hm
      cases hk : knownMissing e u r with
      | nil => rw [hk] at hm; simp at hm
      | cons n _ =>
        have : n ∈ knownMissing e u r := by rw [hk]; exact List.mem_cons_self
        exact ⟨n, (mem_knownMissing.mp this).1, (mem_knownMissing.mp this).2⟩
    · split at h <;> cases h
  · rintro ⟨n, hn, ha⟩
    have : n ∈ knownMissing e u r := mem_knownMissing.mpr ⟨hn, ha⟩
    have hne : (knownMissing e u r).isEmpty = false := by
      cases hk : knownMissing e u r with
      | nil => rw [hk] at this; cases this
      | cons => rfl
    simp [assess, hne]

/-- "otherwise `compatible` if every required domain is known available, or `unknown`". -/
theorem assess_compatible_iff (e u : List Domain) (r o : List String) :
    (assess e u r o).status = .compatible ↔ ∀ n ∈ r, availability e u n = some true := by
  constructor
  · intro h
    simp only [assess] at h
    split at h
    · cases h
    · split at h
      · rename_i hall; simpa using hall
      · cases h
  · intro hall
    have hne : (knownMissing e u r).isEmpty = true := by
      cases hk : knownMissing e u r with
      | nil => rfl
      | cons n _ =>
        have : n ∈ knownMissing e u r := by rw [hk]; exact List.mem_cons_self
        have ⟨hn, ha⟩ := mem_knownMissing.mp this
        rw [hall n hn] at ha; cases ha
    have : r.all (fun n => availability e u n == some true) = true := by simpa using hall
    simp [assess, hne, this]

/-- "no required domains means `compatible`". -/
theorem assess_no_required (e u : List Domain) (o : List String) :
    (assess e u [] o).status = .compatible := (assess_compatible_iff e u [] o).mpr (by simp)

/-- "Missing optional domains do not affect `status`". -/
theorem assess_optional_irrelevant (e u : List Domain) (r o o' : List String) :
    (assess e u r o).status = (assess e u r o').status := rfl

/-- With nothing undisclosed, the check is decided, and `compatible` exactly when the
load-time required-domain check (`missingRequired`) passes. -/
theorem assess_agrees_with_load (e : List Domain) (r o : List String) :
    (assess e [] r o).status ≠ .unknown ∧
    ((assess e [] r o).status = .compatible ↔ missingRequired e r = none) := by
  have known : ∀ n, availability e [] n = some true ∨ availability e [] n = some false := by
    intro n; unfold availability
    cases Domain.ofName? n with
    | none => exact .inr rfl
    | some d => by_cases hd : d ∈ e <;> simp [hd]
  refine ⟨?_, ?_⟩
  · intro hu
    by_cases hc : ∀ n ∈ r, availability e [] n = some true
    · rw [(assess_compatible_iff e [] r o).mpr hc] at hu; cases hu
    · have : ∃ n ∈ r, availability e [] n = some false := by
        refine Classical.byContradiction fun hno => hc fun n hn => ?_
        rcases known n with h | h
        · exact h
        · exact absurd ⟨n, hn, h⟩ hno
      rw [(assess_incompatible_iff e [] r o).mpr this] at hu; cases hu
  · rw [assess_compatible_iff]
    constructor
    · intro hall
      simp only [missingRequired, List.find?_eq_none]
      intro n hn
      have := hall n hn
      unfold availability at this
      cases hd : Domain.ofName? n with
      | none => rw [hd] at this; cases this
      | some d => rw [hd] at this; simpa using this
    · intro hm n hn
      obtain ⟨d, hd, hde⟩ := missingRequired_none hm n hn
      simp [availability, hd, hde]

/-- The environment for a bound endpoint describes only its own exposure. -/
def environment (b : Binding) (services : List String) : ShellEnvironment :=
  { capabilities := b.exposed, services }

/-- Runtime reaction to one `shell.ready`, given whether `shell.init` was already sent
on this endpoint. Returns the new flag and the `shell.init` messages to send. -/
def onReady (sent : Bool) (env : ShellEnvironment) : Bool × List ShellEnvironment :=
  if sent then (true, []) else (true, [env])

/-- Feed `n` `shell.ready` messages to one endpoint. -/
def run (env : ShellEnvironment) : Bool → Nat → Bool × List ShellEnvironment
  | sent, 0 => (sent, [])
  | sent, n + 1 =>
    let r := onReady sent env
    let r' := run env r.1 n
    (r'.1, r.2 ++ r'.2)

theorem run_after_init (env : ShellEnvironment) (n : Nat) : (run env true n).2 = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, onReady, ih]

/-- The first `shell.ready` yields exactly one `shell.init`; duplicates yield none. -/
theorem init_exactly_once (env : ShellEnvironment) (n : Nat) :
    (run env false (n + 1)).2 = [env] := by
  simp [run, onReady, run_after_init]

theorem init_at_most_once (env : ShellEnvironment) (sent : Bool) (n : Nat) :
    (run env sent n).2.length ≤ 1 := by
  cases n with
  | zero => simp [run]
  | succ n =>
    cases sent with
    | false => simp [init_exactly_once]
    | true => simp [run, onReady, run_after_init]

/-- In a reachable shell, `shell.init` advertises exactly the policy exposure for the
bound identity: nothing a manifest declared, nothing another napplet has. -/
theorem init_capabilities {c : Crypto} {cfg : ShellConfig} {s : ShellState}
    (hr : Reachable c cfg s) {p : PortId} {b : Binding} (hb : s.bindings p = some b)
    (services : List String) :
    (environment b services).capabilities = exposedFor cfg b.identity := by
  obtain ⟨ld, hf⟩ := hr.inv.bind_frame p b hb
  exact (hr.inv.frame_verified _ _ _ _ _ hf).2

end Napplet.NapShell
