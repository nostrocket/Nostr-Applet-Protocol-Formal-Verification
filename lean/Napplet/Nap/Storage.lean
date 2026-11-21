/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-STORAGE (`storage`, PR napplet/naps#2/#3 branch `nub-storage`)

Scoped key-value storage. The runtime derives the scope from the authenticated
endpoint; `StorageReq` has no identity fields, so a napplet cannot supply or
override them.

Results:
* `handle_isolated`: a request only touches its own scope.
* `quota_preserved`: if every scope is within quota, it stays within quota.
* `set_then_get`, `set_fail_unchanged`, `handle_same_id`.
* `keys_nodup_preserved`: keys within a scope stay unique.
* Scope separation: shared vs instance, per instance, per publisher (a bare `d` is
  not a scope), per artifact hash.
-/

namespace Napplet.NapStorage

/-- Manifest key from the verified manifest (NAP-STORAGE §Identity Scope). -/
inductive ManifestKey where
  | named (publisher : Pubkey) (d : String)
  | root (publisher : Pubkey)
  | snapshot (eventId : String)
  deriving DecidableEq, Repr

abbrev InstanceId := Nat

structure Scope where
  key : ManifestKey
  artifactHash : Hash
  inst : Option InstanceId
  deriving DecidableEq, Repr

/-- What the runtime knows about an endpoint. Never sent by the napplet. -/
structure EndpointCtx where
  key : ManifestKey
  artifactHash : Hash
  instanceId : InstanceId

inductive ScopeSel where
  | shared
  | inst
  deriving DecidableEq, Repr

def scopeFor (e : EndpointCtx) : ScopeSel → Scope
  | .shared => ⟨e.key, e.artifactHash, none⟩
  | .inst => ⟨e.key, e.artifactHash, some e.instanceId⟩

inductive StorageReq where
  | get (id : String) (key : String) (sel : ScopeSel)
  | set (id : String) (key : String) (value : String) (sel : ScopeSel)
  | remove (id : String) (key : String) (sel : ScopeSel)
  | keys (id : String) (sel : ScopeSel)
  deriving DecidableEq, Repr

def StorageReq.id : StorageReq → String
  | get i _ _ | set i _ _ _ | remove i _ _ | keys i _ => i

def StorageReq.sel : StorageReq → ScopeSel
  | get _ _ s | set _ _ _ s | remove _ _ s | keys _ s => s

inductive Payload where
  | value (v : Option String)
  | keys (ks : List String)
  | empty
  deriving DecidableEq, Repr

structure StorageResult where
  id : String
  payload : Payload
  error : Option String
  deriving DecidableEq, Repr

abbrev KV := List (String × String)
abbrev Store := Scope → KV

def kvGet (l : KV) (k : String) : Option String := (l.find? (·.1 == k)).map (·.2)
def kvSet (l : KV) (k v : String) : KV := (k, v) :: l.filter (·.1 != k)
def kvRemove (l : KV) (k : String) : KV := l.filter (·.1 != k)

/-- Usage in UTF-8 bytes. -/
def usage (l : KV) : Nat := (l.map fun x => x.1.utf8ByteSize + x.2.utf8ByteSize).sum

/-- Recommended default quota: 512 KB. -/
def defaultQuota : Nat := 512 * 1024

def handle (quota : Nat) (st : Store) (e : EndpointCtx) : StorageReq → Store × StorageResult
  | .get i k sel => (st, ⟨i, .value (kvGet (st (scopeFor e sel)) k), none⟩)
  | .set i k v sel =>
    if usage (kvSet (st (scopeFor e sel)) k v) ≤ quota then
      (upd st (scopeFor e sel) (kvSet (st (scopeFor e sel)) k v), ⟨i, .empty, none⟩)
    else (st, ⟨i, .empty, some "quota exceeded"⟩)
  | .remove i k sel =>
    (upd st (scopeFor e sel) (kvRemove (st (scopeFor e sel)) k), ⟨i, .empty, none⟩)
  | .keys i sel => (st, ⟨i, .keys ((st (scopeFor e sel)).map (·.1)), none⟩)

theorem handle_same_id (q : Nat) (st : Store) (e : EndpointCtx) (r : StorageReq) :
    (handle q st e r).2.id = r.id := by
  cases r <;> simp only [handle, StorageReq.id] <;> (try split) <;> rfl

/-- A request touches only the scope the runtime derived for it. -/
theorem handle_isolated (q : Nat) (st : Store) (e : EndpointCtx) (r : StorageReq)
    {sc : Scope} (h : sc ≠ scopeFor e r.sel) : (handle q st e r).1 sc = st sc := by
  cases r <;> simp only [handle, StorageReq.sel] at h ⊢ <;> (try split) <;> simp [upd, h]

theorem usage_filter_le (l : KV) (p : String × String → Bool) :
    usage (l.filter p) ≤ usage l := by
  induction l with
  | nil => simp [usage]
  | cons x xs ih =>
    simp only [usage, List.filter_cons] at ih ⊢
    split <;> simp <;> omega

/-- Per-scope quota is an invariant. -/
theorem quota_preserved {q : Nat} {st : Store} (e : EndpointCtx) (r : StorageReq)
    (h : ∀ sc, usage (st sc) ≤ q) : ∀ sc, usage ((handle q st e r).1 sc) ≤ q := by
  intro sc
  cases r with
  | get => exact h sc
  | keys => exact h sc
  | set i k v sel =>
    simp only [handle]
    split
    · rename_i hu
      simp only [upd]
      split
      · rename_i hs; subst hs; exact hu
      · exact h sc
    · exact h sc
  | remove i k sel =>
    simp only [handle, upd]
    split
    · rename_i hs; subst hs
      exact Nat.le_trans (usage_filter_le _ _) (h _)
    · exact h sc

theorem kvGet_set (l : KV) (k v : String) : kvGet (kvSet l k v) k = some v := by
  simp [kvGet, kvSet]

/-- A successful `set` is visible to a later `get` in the same scope. -/
theorem set_then_get {q : Nat} {st : Store} {e : EndpointCtx} {i k v : String} {sel : ScopeSel}
    (hok : (handle q st e (.set i k v sel)).2.error = none) (i' : String) :
    (handle q (handle q st e (.set i k v sel)).1 e (.get i' k sel)).2.payload = .value (some v) := by
  by_cases hu : usage (kvSet (st (scopeFor e sel)) k v) ≤ q
  · simp [handle, hu, upd, kvGet_set]
  · simp [handle, hu] at hok

/-- A rejected `set` leaves storage unchanged. -/
theorem set_fail_unchanged {q : Nat} {st : Store} {e : EndpointCtx} {i k v : String}
    {sel : ScopeSel} (hf : (handle q st e (.set i k v sel)).2.error ≠ none) :
    (handle q st e (.set i k v sel)).1 = st := by
  by_cases hu : usage (kvSet (st (scopeFor e sel)) k v) ≤ q
  · simp [handle, hu] at hf
  · simp [handle, hu]

theorem nodup_filter_key (l : KV) (k : String) (h : (l.map (·.1)).Nodup) :
    ((l.filter (·.1 != k)).map (·.1)).Nodup :=
  h.sublist ((List.filter_sublist).map _)

theorem keys_nodup_set (l : KV) (k v : String) (h : (l.map (·.1)).Nodup) :
    ((kvSet l k v).map (·.1)).Nodup := by
  simp only [kvSet, List.map_cons, List.nodup_cons]
  refine ⟨?_, nodup_filter_key l k h⟩
  simp

theorem keys_nodup_preserved {q : Nat} {st : Store} (e : EndpointCtx) (r : StorageReq)
    (h : ∀ sc, ((st sc).map (·.1)).Nodup) : ∀ sc, (((handle q st e r).1 sc).map (·.1)).Nodup := by
  intro sc
  cases r with
  | get => exact h sc
  | keys => exact h sc
  | set i k v sel =>
    simp only [handle]
    split
    · simp only [upd]; split
      · rename_i hs; subst hs; exact keys_nodup_set _ _ _ (h _)
      · exact h sc
    · exact h sc
  | remove i k sel =>
    simp only [handle, upd]
    split
    · rename_i hs; subst hs; exact nodup_filter_key _ _ (h _)
    · exact h sc

/-! ### Scope separation -/

theorem shared_ne_instance (e : EndpointCtx) : scopeFor e .shared ≠ scopeFor e .inst := by
  simp [scopeFor]

theorem instances_isolated {e₁ e₂ : EndpointCtx} (h : e₁.instanceId ≠ e₂.instanceId) :
    scopeFor e₁ .inst ≠ scopeFor e₂ .inst := by
  simp [scopeFor, h]

/-- "A bare `d` value MUST NOT identify a scope": same `d`, different publisher,
different scope. -/
theorem bare_d_not_scope {e₁ e₂ : EndpointCtx} {p₁ p₂ : Pubkey} {d : String} {sel : ScopeSel}
    (h₁ : e₁.key = .named p₁ d) (h₂ : e₂.key = .named p₂ d) (hp : p₁ ≠ p₂) :
    scopeFor e₁ sel ≠ scopeFor e₂ sel := by
  cases sel <;> simp [scopeFor, h₁, h₂, hp]

theorem artifact_hash_isolated {e₁ e₂ : EndpointCtx} {sel : ScopeSel}
    (h : e₁.artifactHash ≠ e₂.artifactHash) : scopeFor e₁ sel ≠ scopeFor e₂ sel := by
  cases sel <;> simp [scopeFor, h]

end Napplet.NapStorage
