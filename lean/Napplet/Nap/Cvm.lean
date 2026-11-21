/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-CVM (`cvm`, PR napplet/naps#31 branch `nap-cvm`)

ContextVM (MCP over Nostr) bridge. Modelled pieces: timeout validation, payment
policy, request/response correlation, registry calls, and the one-result rule.

Results:
* `timeout_ok`: an accepted timeout is in range, within shell policy, and exactly
  what was requested (never silently clamped). `timeout_120s_accepted`.
* `paid_requires_authority`: a paid call happens only with per-invocation consent
  (`prompt`) or a standing allowance that covers it (`allow`); `deny_never_pays`;
  `free_always_allowed`.
* `reserve_never_overspends`: concurrent reservations against one allowance never
  exceed it in total.
* `response_routed_to_owner`: a server response reaches only the endpoint that sent
  the request, with its original MCP id restored.
* `transport_ids_fresh`: identical caller ids from different napplets never collide.
* `late_response_dropped`, `duplicate_response_dropped`: at most one result per request.
* `registry_call_hash_checked`: a registry call is published only when the tool's
  verified schema hash matches the selector.
* `exactly_one_result`, `unimplemented_has_false`.
-/

namespace Napplet.NapCvm

/-! ### Timeouts -/

def defaultTimeout : Nat := 30000
def maxTimeout : Nat := 300000

def checkTimeout (shellMax : Nat) (t : Option Nat) : Except String Nat :=
  let v := t.getD defaultTimeout
  if v < 1 ∨ v > maxTimeout then .error "invalid timeout"
  else if v > shellMax then .error "timeout out of policy"
  else .ok v

theorem timeout_ok {shellMax : Nat} {t : Option Nat} {v : Nat} (h : checkTimeout shellMax t = .ok v) :
    v = t.getD defaultTimeout ∧ 1 ≤ v ∧ v ≤ maxTimeout ∧ v ≤ shellMax := by
  unfold checkTimeout at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h1 h2
      simp at h
      subst h
      simp only [not_or, Nat.not_lt] at h1
      refine ⟨rfl, h1.1, h1.2, by omega⟩

/-- Conformance case: an accepted 120 s request is not cut to 30 s. -/
theorem timeout_120s_accepted {shellMax : Nat} (h : 120000 ≤ shellMax) :
    checkTimeout shellMax (some 120000) = .ok 120000 := by
  simp [checkTimeout, maxTimeout]
  omega

#guard checkTimeout 300000 (some 0) matches .error "invalid timeout"
#guard checkTimeout 60000 (some 120000) matches .error "timeout out of policy"
#guard checkTimeout 300000 none matches .ok 30000

/-! ### Payments -/

inductive PayMode where
  | deny
  | prompt
  | allow
  deriving DecidableEq, Repr

/-- Decide one invocation. `allowance` is the standing budget configured outside the
napplet for this napplet, server, operation and method. Returns the new budget. -/
def decidePay (mode : PayMode) (price : Nat) (userConsents : Bool) (allowance : Option Nat) :
    Except String (Option Nat) :=
  if price = 0 then .ok allowance
  else match mode with
    | .deny => .error "payment denied"
    | .prompt => if userConsents then .ok allowance else .error "payment denied"
    | .allow =>
      match allowance with
      | some r => if price ≤ r then .ok (some (r - price)) else .error "payment denied"
      | none => .error "payment denied"

theorem free_always_allowed (mode : PayMode) (c : Bool) (a : Option Nat) :
    decidePay mode 0 c a = .ok a := by
  simp [decidePay]

theorem deny_never_pays {price : Nat} {c : Bool} {a a' : Option Nat} (hp : price > 0) :
    decidePay .deny price c a ≠ .ok a' := by
  simp [decidePay, Nat.pos_iff_ne_zero.mp hp]

/-- A paid call needs per-invocation consent or a covering standing allowance. -/
theorem paid_requires_authority {mode : PayMode} {price : Nat} {c : Bool} {a a' : Option Nat}
    (hp : price > 0) (h : decidePay mode price c a = .ok a') :
    (mode = .prompt ∧ c = true) ∨
    (mode = .allow ∧ ∃ r, a = some r ∧ price ≤ r ∧ a' = some (r - price)) := by
  unfold decidePay at h
  split at h
  · omega
  · split at h
    · simp at h
    · split at h
      · exact .inl ⟨rfl, by assumption⟩
      · simp at h
    · split at h
      · rename_i r
        split at h
        · simp at h
          exact .inr ⟨rfl, r, rfl, by assumption, h.symm⟩
        · simp at h
      · simp at h

/-- Reserve each price in turn against one budget (atomic per reservation). -/
def reserveAll : Nat → List Nat → List Nat
  | _, [] => []
  | budget, p :: ps =>
    if p ≤ budget then p :: reserveAll (budget - p) ps else reserveAll budget ps

/-- Concurrent paid calls never exceed the allowance in total. -/
theorem reserve_never_overspends (budget : Nat) (ps : List Nat) :
    (reserveAll budget ps).sum ≤ budget := by
  induction ps generalizing budget with
  | nil => simp [reserveAll]
  | cons p ps ih =>
    simp only [reserveAll]
    split
    · have := ih (budget - p); simp; omega
    · exact ih budget

/-! ### Correlation -/

structure Pending where
  tid : Nat
  endpoint : Endpoint
  server : String
  callerId : String
  deriving DecidableEq, Repr

structure Corr where
  pending : List Pending
  next : Nat

def sendReq (c : Corr) (e : Endpoint) (srv : String) (cid : String) : Corr × Nat :=
  ({ pending := ⟨c.next, e, srv, cid⟩ :: c.pending, next := c.next + 1 }, c.next)

def onResponse (c : Corr) (srv : String) (tid : Nat) : Corr × Option (Endpoint × String) :=
  match c.pending.find? (fun p => p.tid == tid && p.server == srv) with
  | some p => ({ c with pending := c.pending.filter (·.tid != tid) }, some (p.endpoint, p.callerId))
  | none => (c, none)

/-- Timeout expiry releases the correlation. -/
def expire (c : Corr) (tid : Nat) : Corr := { c with pending := c.pending.filter (·.tid != tid) }

/-- A response reaches only the requesting endpoint, with its caller id restored. -/
theorem response_routed_to_owner {c : Corr} {srv : String} {tid : Nat} {e : Endpoint}
    {cid : String} (h : (onResponse c srv tid).2 = some (e, cid)) :
    ⟨tid, e, srv, cid⟩ ∈ c.pending := by
  unfold onResponse at h
  split at h
  · rename_i p hp
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have hm := List.mem_of_find?_eq_some hp
    have hpr := List.find?_some hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hpr
    obtain ⟨h1, h2⟩ := hpr
    cases p; simp_all
  · simp at h

/-- Every new request gets a transport id no pending request has, so identical MCP
ids from different napplets never collide. -/
theorem transport_ids_fresh {c : Corr} (hi : ∀ p ∈ c.pending, p.tid < c.next) (e : Endpoint)
    (srv cid : String) : ∀ p ∈ c.pending, p.tid ≠ (sendReq c e srv cid).2 := by
  intro p hp
  have := hi p hp
  simp [sendReq]
  omega

theorem sendReq_inv {c : Corr} (hi : ∀ p ∈ c.pending, p.tid < c.next) (e : Endpoint)
    (srv cid : String) : ∀ p ∈ (sendReq c e srv cid).1.pending, p.tid < (sendReq c e srv cid).1.next := by
  intro p hp
  simp only [sendReq, List.mem_cons] at hp ⊢
  rcases hp with rfl | hp
  · simp
  · have := hi p hp; omega

/-- A response after timeout expiry produces nothing. -/
theorem late_response_dropped (c : Corr) (srv : String) (tid : Nat) :
    (onResponse (expire c tid) srv tid).2 = none := by
  have : (expire c tid).pending.find? (fun p => p.tid == tid && p.server == srv) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp [expire] at hp
    simp [hp.2]
  simp [onResponse, this]

/-- A second response for the same request produces nothing. -/
theorem duplicate_response_dropped (c : Corr) (srv : String) (tid : Nat) :
    (onResponse (onResponse c srv tid).1 srv tid).2 = none := by
  cases h : c.pending.find? (fun p => p.tid == tid && p.server == srv) with
  | none => simp [onResponse, h]
  | some p =>
    have : (c.pending.filter (·.tid != tid)).find? (fun p => p.tid == tid && p.server == srv) = none := by
      rw [List.find?_eq_none]
      intro q hq
      simp at hq
      simp [hq.2]
    simp [onResponse, h, this]

/-! ### Registry -/

/-- A registry call is published only if the tool's verified CEP-15 hash matches. -/
def registryCall (verifiedHash : String → Option Hash) (selectorHash : Hash) (tool : String) :
    Except String String :=
  if verifiedHash tool = some selectorHash then .ok tool else .error "schema mismatch"

theorem registry_call_hash_checked {vh : String → Option Hash} {sel : Hash} {tool t : String}
    (h : registryCall vh sel tool = .ok t) : t = tool ∧ vh tool = some sel := by
  unfold registryCall at h
  split at h
  · simp at h; exact ⟨h.symm, by assumption⟩
  · simp at h

/-! ### One result per request -/

inductive Op where
  | discover | request | close
  | registryList | registryHas | registryDescribe | registryCall
  deriving DecidableEq, Repr

inductive CvmOut where
  | result (to : Endpoint) (id : String) (error : Option String)
  | hasResult (to : Endpoint) (id : String) (has : Bool)
  deriving DecidableEq, Repr

/-- Shell response to a recognised request, given which operations it implements
and the outcome of performing it. -/
def respond (implemented : Op → Bool) (outcome : Option String) (to : Endpoint) (id : String) :
    Op → List CvmOut
  | .registryHas => if implemented .registryHas then [.hasResult to id (outcome.isNone)]
                    else [.hasResult to id false]
  | op => if implemented op then [.result to id outcome] else [.result to id (some "unsupported method")]

theorem exactly_one_result (impl : Op → Bool) (out : Option String) (to : Endpoint) (id : String)
    (op : Op) : (respond impl out to id op).length = 1 := by
  cases op <;> simp only [respond] <;> split <;> rfl

theorem unimplemented_has_false {impl : Op → Bool} (h : impl .registryHas = false)
    (out : Option String) (to : Endpoint) (id : String) :
    respond impl out to id .registryHas = [.hasResult to id false] := by
  simp [respond, h]

theorem unimplemented_unsupported {impl : Op → Bool} {op : Op} (hop : op ≠ .registryHas)
    (h : impl op = false) (out : Option String) (to : Endpoint) (id : String) :
    respond impl out to id op = [.result to id (some "unsupported method")] := by
  cases op <;> simp_all [respond]

end Napplet.NapCvm
