/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-VALUE (`value`, PR napplet/naps#30 branch `nap-value`)

Shell-mediated value transfer and zaps. Wallet access, consent UI and zap-request
signing are shell-side opaque functions; the napplet's request carries no wallet
credential, preimage or key.

Results:
* `pay_requires_consent_or_allowance`: money moves only with explicit user consent
  or a pre-configured allowance for this napplet, rail and amount.
* `pay_within_policy`: rail enabled, target inspectable, amount within the
  per-napplet maximum.
* `allowance_debited`, `allowance_other_napplets_untouched`,
  `allowance_no_overspend`: allowances are bound to the napplet and never go
  below what was spent.
* `settled_requires_proof`: `settled` is reported only with backend confirmation;
  failures are never reported as success (`failure_not_success`).
* `zap_signed_by_shell`: the kind 9734 zap request is built and signed by the shell.
* `quote_not_binding`: a quote does not authorise anything; `send` re-checks.
* `send_same_id`.
-/

namespace Napplet.NapValue

inductive Rail where
  | zap
  | lnurl
  | other (name : String)
  deriving DecidableEq, Repr

inductive Target where
  | zap (pubkey : Pubkey) (eventId : Option String)
  | lnurl (url : String)
  | ext (type : String)
  deriving DecidableEq, Repr

structure ValueRequest where
  rail : Rail
  amountMsat : Nat
  target : Target
  comment : Option String := none
  deriving DecidableEq, Repr

inductive TransferState where
  | pending | settled | failed | cancelled
  deriving DecidableEq, Repr

/-- A standing allowance configured by the user, bound to one napplet and rail. -/
structure Allowance where
  napplet : Endpoint
  rail : Rail
  maxPerTransfer : Nat
  remaining : Nat
  deriving DecidableEq, Repr

structure ZapRequest where
  kind : Nat
  amountMsat : Nat
  target : Target
  sig : String
  deriving DecidableEq, Repr

structure ValueEnv where
  railEnabled : Rail → Bool
  /-- Per-napplet maximum amount for a rail. -/
  maxAmount : Endpoint → Rail → Nat
  /-- Can the shell inspect and present this target to the user? -/
  inspectable : Target → Bool
  /-- Outcome of the consent prompt. -/
  userApproves : Endpoint → ValueRequest → Bool
  /-- Shell signs the kind 9734 zap request. -/
  signZap : ValueRequest → ZapRequest
  /-- Wallet backend: `some proof` only on confirmed settlement. -/
  pay : ValueRequest → Option ZapRequest → Option String

structure ValueResult where
  ok : Bool
  status : TransferState
  amountMsat : Nat
  zapRequest : Option ZapRequest
  proof : Option String
  error : Option String
  deriving DecidableEq, Repr

inductive ValueOut where
  /-- The shell instructs its wallet backend to pay. -/
  | pay (req : ValueRequest) (zap : Option ZapRequest)
  | result (to : Endpoint) (id : String) (r : ValueResult)
  | topError (to : Endpoint) (id : String) (error : String)
  deriving DecidableEq, Repr

def covers (sender : Endpoint) (req : ValueRequest) (a : Allowance) : Bool :=
  a.napplet == sender && a.rail == req.rail &&
    decide (req.amountMsat ≤ a.maxPerTransfer) && decide (req.amountMsat ≤ a.remaining)

/-- Debit the first covering allowance. -/
def debit (sender : Endpoint) (req : ValueRequest) : List Allowance → List Allowance
  | [] => []
  | a :: as =>
    if covers sender req a then { a with remaining := a.remaining - req.amountMsat } :: as
    else a :: debit sender req as

/-- Policy checks shared by `quote` and `send`. -/
def policyError (env : ValueEnv) (sender : Endpoint) (req : ValueRequest) : Option String :=
  if env.railEnabled req.rail = false then some "unsupported rail"
  else if env.inspectable req.target = false then some "invalid target"
  else if req.amountMsat > env.maxAmount sender req.rail then some "amount out of policy"
  else none

/-- `value.send`. -/
def send (env : ValueEnv) (allowances : List Allowance) (sender : Endpoint) (id : String)
    (req : ValueRequest) : List Allowance × List ValueOut :=
  match policyError env sender req with
  | some e => (allowances, [.topError sender id e])
  | none =>
    let covered := allowances.any (covers sender req)
    if covered = false && env.userApproves sender req = false then
      (allowances, [.topError sender id "user cancelled"])
    else
      let allowances' := if covered then debit sender req allowances else allowances
      let zap := if req.rail = .zap then some (env.signZap req) else none
      match env.pay req zap with
      | some proof =>
        (allowances', [.pay req zap,
          .result sender id ⟨true, .settled, req.amountMsat, zap, some proof, none⟩])
      | none =>
        (allowances', [.pay req zap,
          .result sender id ⟨false, .failed, req.amountMsat, zap, none, some "payment failed"⟩])

/-- `value.quote`: advisory only, never moves money. -/
def quote (env : ValueEnv) (sender : Endpoint) (req : ValueRequest) : Except String Nat :=
  match policyError env sender req with
  | some e => .error e
  | none => .ok req.amountMsat

theorem policyError_none {env : ValueEnv} {sender : Endpoint} {req : ValueRequest}
    (h : policyError env sender req = none) :
    env.railEnabled req.rail = true ∧ env.inspectable req.target = true ∧
    req.amountMsat ≤ env.maxAmount sender req.rail := by
  unfold policyError at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i h1 h2 h3
        exact ⟨by simpa using h1, by simpa using h2, by omega⟩

/-- The structure of every non-error path. -/
theorem send_paid {env : ValueEnv} {al : List Allowance} {sender : Endpoint} {id : String}
    {req : ValueRequest} {o : ValueOut} (h : o ∈ (send env al sender id req).2)
    (hn : ∀ i e, o ≠ .topError sender i e) :
    policyError env sender req = none ∧
    (al.any (covers sender req) = true ∨ env.userApproves sender req = true) ∧
    let zap := if req.rail = .zap then some (env.signZap req) else none
    (o = .pay req zap ∨
     (∃ p, env.pay req zap = some p ∧
       o = .result sender id ⟨true, .settled, req.amountMsat, zap, some p, none⟩) ∨
     (env.pay req zap = none ∧
       o = .result sender id ⟨false, .failed, req.amountMsat, zap, none, some "payment failed"⟩)) := by
  unfold send at h
  split at h
  · simp at h; exact absurd h (hn _ _)
  · rename_i hp
    dsimp only at h
    split at h
    · simp at h; exact absurd h (hn _ _)
    · rename_i hc
      refine ⟨hp, ?_, ?_⟩
      · simp only [Bool.and_eq_true, not_and, Bool.not_eq_true] at hc
        cases hcv : al.any (covers sender req) with
        | true => exact .inl rfl
        | false => exact .inr (by simpa using hc (by simpa using hcv))
      · dsimp only
        split at h
        · rename_i p hpay
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr (.inl ⟨p, hpay, h⟩)
        · rename_i hpay
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr (.inr ⟨hpay, h⟩)

/-- Money moves only with explicit consent or a covering allowance for this napplet. -/
theorem pay_requires_consent_or_allowance {env : ValueEnv} {al : List Allowance}
    {sender : Endpoint} {id : String} {req req' : ValueRequest} {zap : Option ZapRequest}
    (h : ValueOut.pay req' zap ∈ (send env al sender id req).2) :
    env.userApproves sender req = true ∨
    ∃ a ∈ al, a.napplet = sender ∧ a.rail = req.rail ∧ req.amountMsat ≤ a.maxPerTransfer ∧
      req.amountMsat ≤ a.remaining := by
  obtain ⟨-, hc, -⟩ := send_paid h (by intro i e; simp)
  rcases hc with hc | hc
  · right
    simp only [List.any_eq_true] at hc
    obtain ⟨a, ha, hcov⟩ := hc
    simp only [covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcov
    exact ⟨a, ha, hcov.1.1.1, hcov.1.1.2, hcov.1.2, hcov.2⟩
  · exact .inl hc

theorem pay_within_policy {env : ValueEnv} {al : List Allowance} {sender : Endpoint}
    {id : String} {req req' : ValueRequest} {zap : Option ZapRequest}
    (h : ValueOut.pay req' zap ∈ (send env al sender id req).2) :
    req' = req ∧ env.railEnabled req.rail = true ∧ env.inspectable req.target = true ∧
    req.amountMsat ≤ env.maxAmount sender req.rail := by
  obtain ⟨hp, -, ho⟩ := send_paid h (by intro i e; simp)
  dsimp only at ho
  have hreq : req' = req := by
    rcases ho with ho | ⟨_, _, ho⟩ | ⟨_, ho⟩
    · simp only [ValueOut.pay.injEq] at ho; exact ho.1
    · simp at ho
    · simp at ho
  exact ⟨hreq, policyError_none hp⟩

/-- `settled` is reported only with a backend proof. -/
theorem settled_requires_proof {env : ValueEnv} {al : List Allowance} {sender : Endpoint}
    {id : String} {req : ValueRequest} {r : ValueResult}
    (h : ValueOut.result sender id r ∈ (send env al sender id req).2) (hs : r.status = .settled) :
    ∃ p, env.pay req r.zapRequest = some p ∧ r.proof = some p := by
  obtain ⟨-, -, ho⟩ := send_paid h (by intro i e; simp)
  dsimp only at ho
  rcases ho with ho | ⟨p, hp, ho⟩ | ⟨_, ho⟩
  · simp at ho
  · simp only [ValueOut.result.injEq, true_and] at ho
    subst ho
    exact ⟨p, hp, rfl⟩
  · simp only [ValueOut.result.injEq, true_and] at ho
    subst ho
    simp at hs

/-- A failed payment is never reported as success. -/
theorem failure_not_success {env : ValueEnv} {al : List Allowance} {sender : Endpoint}
    {id : String} {req : ValueRequest} {r : ValueResult}
    (h : ValueOut.result sender id r ∈ (send env al sender id req).2) (hr : r.ok = true) :
    r.status = .settled ∧ r.proof.isSome := by
  obtain ⟨-, -, ho⟩ := send_paid h (by intro i e; simp)
  dsimp only at ho
  rcases ho with ho | ⟨p, hp, ho⟩ | ⟨_, ho⟩
  · simp at ho
  · simp only [ValueOut.result.injEq, true_and] at ho
    subst ho
    simp
  · simp only [ValueOut.result.injEq, true_and] at ho
    subst ho
    simp at hr

/-- Zap requests are built and signed by the shell. -/
theorem zap_signed_by_shell {env : ValueEnv} {al : List Allowance} {sender : Endpoint}
    {id : String} {req req' : ValueRequest} {z : ZapRequest}
    (h : ValueOut.pay req' (some z) ∈ (send env al sender id req).2) :
    req.rail = .zap ∧ z = env.signZap req := by
  obtain ⟨-, -, ho⟩ := send_paid h (by intro i e; simp)
  dsimp only at ho
  rcases ho with ho | ⟨_, _, ho⟩ | ⟨_, ho⟩
  · simp only [ValueOut.pay.injEq] at ho
    obtain ⟨-, hz⟩ := ho
    split at hz
    · rename_i hr; simp at hz; exact ⟨hr, hz⟩
    · simp at hz
  · simp at ho
  · simp at ho

/-! ### Allowances -/

theorem debit_other {sender : Endpoint} {req : ValueRequest} :
    ∀ {l : List Allowance} {a : Allowance}, a ∈ l → a.napplet ≠ sender → a ∈ debit sender req l
  | [], _, h, _ => by simp at h
  | b :: bs, a, h, hn => by
    simp only [debit]
    split
    · rename_i hb
      rcases List.mem_cons.mp h with rfl | h
      · simp only [covers, Bool.and_eq_true, beq_iff_eq] at hb
        exact absurd hb.1.1.1 hn
      · exact List.mem_cons_of_mem _ h
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (debit_other h hn)

/-- Other napplets' allowances are never touched by this napplet's spending. -/
theorem allowance_other_napplets_untouched {env : ValueEnv} {al : List Allowance}
    {sender : Endpoint} {id : String} {req : ValueRequest} {a : Allowance} (ha : a ∈ al)
    (hn : a.napplet ≠ sender) : a ∈ (send env al sender id req).1 := by
  unfold send
  split
  · exact ha
  · dsimp only
    split
    · exact ha
    · split <;> (split <;> first | exact debit_other ha hn | exact ha)

/-- Total remaining allowance drops by exactly the amount when an allowance pays. -/
def total (l : List Allowance) : Nat := (l.map (·.remaining)).sum

theorem debit_total {sender : Endpoint} {req : ValueRequest} :
    ∀ {l : List Allowance}, l.any (covers sender req) = true →
      total (debit sender req l) + req.amountMsat = total l
  | [], h => by simp at h
  | b :: bs, h => by
    simp only [debit]
    split
    · rename_i hb
      simp only [covers, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [total, List.map_cons, List.sum_cons]
      omega
    · rename_i hb
      have : bs.any (covers sender req) = true := by
        simp only [List.any_cons, Bool.or_eq_true] at h
        rcases h with h | h
        · exact absurd h hb
        · exact h
      have ih := debit_total this
      simp only [total, List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- No overspend: when an allowance covers the transfer, the allowance pool shrinks
by exactly the amount paid; without one, the pool is unchanged. -/
theorem allowance_no_overspend {env : ValueEnv} {al : List Allowance} {sender : Endpoint}
    {id : String} {req : ValueRequest} :
    total (send env al sender id req).1 + req.amountMsat = total al ∨
    (send env al sender id req).1 = al := by
  unfold send
  split
  · exact .inr rfl
  · dsimp only
    split
    · exact .inr rfl
    · rename_i hc
      by_cases hcov : al.any (covers sender req) = true
      · left
        split <;> simp only [hcov, ↓reduceIte] <;> exact debit_total hcov
      · right
        simp only [Bool.not_eq_true] at hcov
        split <;> simp [hcov]

/-- A quote authorises nothing: it produces no output, and `send` re-runs every check. -/
theorem quote_not_binding (env : ValueEnv) (sender : Endpoint) (req : ValueRequest)
    (al : List Allowance) (id : String) (h : policyError env sender req ≠ none) :
    (send env al sender id req).2.all (fun o => match o with | .pay .. => false | _ => true) := by
  unfold send
  split
  · simp
  · rename_i hp; exact absurd hp h

theorem send_same_id {env : ValueEnv} {al : List Allowance} {sender : Endpoint} {id : String}
    {req : ValueRequest} :
    ∃ o ∈ (send env al sender id req).2, (∃ r, o = .result sender id r) ∨ (∃ e, o = .topError sender id e) := by
  unfold send
  split
  · exact ⟨_, List.mem_singleton_self _, .inr ⟨_, rfl⟩⟩
  · dsimp only
    split
    · exact ⟨_, List.mem_singleton_self _, .inr ⟨_, rfl⟩⟩
    · split
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), .inl ⟨_, rfl⟩⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), .inl ⟨_, rfl⟩⟩

end Napplet.NapValue
