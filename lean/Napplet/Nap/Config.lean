/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-CONFIG (`config`, PR napplet/naps#14 branch `nub-config`, GitHub draft)

Per-napplet declarative configuration. The napplet declares a JSON-Schema subset;
the shell renders settings, validates, persists and delivers values. There is no
napplet write operation, so the shell is the sole writer by construction.

Schemas outside the Core Subset (`$ref`, `pattern`, combinators, conditionals, …)
are represented by `Schema.unsupported` carrying the error code the shell returns.

Results:
* `register_accepts_only_core`: an accepted schema has no unsupported feature, depth
  at most 4, and no secret field with a default.
* `values_valid`: every delivered value validates against its declared property.
* `values_declared`: only declared properties are delivered (`additionalProperties`
  is false at the top level).
* `secret_never_defaulted`: an unset secret is never delivered.
* `default_resolution`: a valid persisted value wins over the default.
* `no_schema_error`: `get`/`subscribe` before a schema yields `no-schema`.
-/

namespace Napplet.NapConfig

inductive ErrCode where
  | invalidSchema | versionConflict | unsupportedDraft | refNotAllowed | patternNotAllowed
  | secretWithDefault | schemaTooDeep | noSchema
  deriving DecidableEq, Repr

mutual
inductive Schema where
  | str (dflt : Option String) (secret : Bool) (minLen maxLen : Option Nat)
      (enum : Option (List String))
  | int (dflt : Option Int) (min max : Option Int)
  | bool (dflt : Option Bool)
  | obj (props : Props)
  | unsupported (code : ErrCode)
inductive Props where
  | nil
  | cons (key : String) (s : Schema) (rest : Props)
end

mutual
def Schema.depth : Schema → Nat
  | .obj ps => ps.depth + 1
  | _ => 0
def Props.depth : Props → Nat
  | .nil => 0
  | .cons _ s r => max s.depth r.depth
end

mutual
/-- First unsupported feature or secret-with-default found anywhere. -/
def Schema.firstError : Schema → Option ErrCode
  | .unsupported c => some c
  | .str (some _) true _ _ _ => some .secretWithDefault
  | .obj ps => ps.firstError
  | _ => none
def Props.firstError : Props → Option ErrCode
  | .nil => none
  | .cons _ s r =>
    match s.firstError with
    | some e => some e
    | none => r.firstError
end

def Props.lookup : Props → String → Option Schema
  | .nil, _ => none
  | .cons k s r, key => if k = key then some s else r.lookup key

def Props.toList : Props → List (String × Schema)
  | .nil => []
  | .cons k s r => (k, s) :: r.toList

/-- `config.registerSchema`: root must be an object in the Core Subset. -/
def register (s : Schema) : Except ErrCode Props :=
  match s with
  | .obj ps =>
    match ps.firstError with
    | some e => .error e
    | none => if s.depth > 4 then .error .schemaTooDeep else .ok ps
  | .unsupported c => .error c
  | _ => .error .invalidSchema

theorem register_accepts_only_core {s : Schema} {ps : Props} (h : register s = .ok ps) :
    s = .obj ps ∧ ps.firstError = none ∧ s.depth ≤ 4 := by
  unfold register at h
  split at h
  · rename_i ps'
    split at h
    · simp at h
    · rename_i he
      split at h
      · simp at h
      · rename_i hd
        simp at h
        subst h
        exact ⟨rfl, he, by omega⟩
  · simp at h
  · simp at h

/-! ### Values -/

inductive Val where
  | s (v : String)
  | i (v : Int)
  | b (v : Bool)
  /-- Nested objects are delivered opaquely in this model. -/
  | o
  deriving DecidableEq, Repr

/-- Primitive validation (Core Subset keywords). -/
def valid : Schema → Val → Bool
  | .str _ _ mn mx en, .s v =>
    (mn.all (· ≤ v.length)) && (mx.all (v.length ≤ ·)) && (en.all (v ∈ ·))
  | .int _ mn mx, .i v => (mn.all (· ≤ v)) && (mx.all (v ≤ ·))
  | .bool _, .b _ => true
  | .obj _, .o => true
  | _, _ => false

/-- Declared default, if any. Secret fields never have one. -/
def dflt : Schema → Option Val
  | .str (some d) false _ _ _ => some (.s d)
  | .int (some d) _ _ => some (.i d)
  | .bool (some d) => some (.b d)
  | _ => none

def isSecret : Schema → Bool
  | .str _ true _ _ _ => true
  | _ => false

/-- The declared default, only if it validates. -/
def validDefault (s : Schema) : Option Val :=
  match dflt s with
  | some d => if valid s d then some d else none
  | none => none

/-- Resolve one property: valid persisted value, else valid default, else nothing. -/
def resolve (s : Schema) (persisted : Option Val) : Option Val :=
  match persisted with
  | some v => if valid s v then some v else validDefault s
  | none => validDefault s

theorem validDefault_valid {s : Schema} {v : Val} (h : validDefault s = some v) :
    valid s v = true := by
  unfold validDefault at h
  split at h
  · split at h
    · simp at h; subst h; assumption
    · simp at h
  · simp at h

/-- The values the shell delivers for a registered schema. -/
def values (ps : Props) (persisted : String → Option Val) : List (String × Val) :=
  ps.toList.filterMap fun (k, s) => (resolve s (persisted k)).map (k, ·)

theorem resolve_valid {s : Schema} {p : Option Val} {v : Val} (h : resolve s p = some v) :
    valid s v = true := by
  unfold resolve at h
  split at h
  · split at h
    · simp at h; subst h; assumption
    · exact validDefault_valid h
  · exact validDefault_valid h

theorem values_spec {ps : Props} {pers : String → Option Val} {k : String} {v : Val}
    (h : (k, v) ∈ values ps pers) :
    ∃ s, (k, s) ∈ ps.toList ∧ resolve s (pers k) = some v := by
  simp only [values, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨k', s⟩, hm, v', hr, rfl, rfl⟩ := h
  exact ⟨s, hm, hr⟩

/-- Every delivered value validates against its declared property. -/
theorem values_valid {ps : Props} {pers : String → Option Val} {k : String} {v : Val}
    (h : (k, v) ∈ values ps pers) : ∃ s, (k, s) ∈ ps.toList ∧ valid s v = true := by
  obtain ⟨s, hm, hr⟩ := values_spec h
  exact ⟨s, hm, resolve_valid hr⟩

/-- Only declared properties are delivered. -/
theorem values_declared {ps : Props} {pers : String → Option Val} {k : String} {v : Val}
    (h : (k, v) ∈ values ps pers) : k ∈ ps.toList.map Prod.fst := by
  obtain ⟨s, hm, -⟩ := values_spec h
  exact List.mem_map.mpr ⟨(k, s), hm, rfl⟩

theorem dflt_secret {s : Schema} (h : isSecret s = true) : dflt s = none := by
  cases s with
  | str d sec a b c => cases d <;> cases sec <;> simp_all [isSecret, dflt]
  | int => simp [isSecret] at h
  | bool => simp [isSecret] at h
  | obj => simp [isSecret] at h
  | unsupported => simp [isSecret] at h

/-- An unset secret is never delivered. -/
theorem secret_never_defaulted {ps : Props} {pers : String → Option Val} {k : String}
    {v : Val} {s : Schema} (hsec : isSecret s = true)
    (hunset : pers k = none) (huniq : ∀ s', (k, s') ∈ ps.toList → s' = s) :
    (k, v) ∉ values ps pers := by
  intro h
  obtain ⟨s', hm, hr⟩ := values_spec h
  rw [huniq s' hm, hunset] at hr
  simp [resolve, validDefault, dflt_secret hsec] at hr

/-- A valid persisted value wins over the default. -/
theorem default_resolution {s : Schema} {v : Val} (hv : valid s v = true) :
    resolve s (some v) = some v := by
  simp [resolve, hv]

/-! ### Requests -/

inductive ConfigReq where
  | get (id : String)
  | subscribe
  | openSettings (section_ : Option String)
  deriving DecidableEq, Repr

inductive ConfigOut where
  | values (id : Option String) (vals : List (String × Val))
  | schemaError (code : ErrCode)
  /-- Shell opens its own settings UI (napplets never render it). -/
  | showSettings (section_ : Option String)
  deriving DecidableEq, Repr

def handle (schema : Option Props) (pers : String → Option Val) (focused : Bool) :
    ConfigReq → List ConfigOut
  | .get id =>
    match schema with
    | none => [.schemaError .noSchema]
    | some ps => [.values (some id) (values ps pers)]
  | .subscribe =>
    match schema with
    | none => [.schemaError .noSchema]
    | some ps => [.values none (values ps pers)]
  | .openSettings sec => if focused then [.showSettings sec] else []

theorem no_schema_error (pers : String → Option Val) (f : Bool) (r : ConfigReq)
    (hr : r ≠ .subscribe → ∃ id, r = .get id) :
    handle none pers f r = [.schemaError .noSchema] := by
  cases r with
  | get => rfl
  | subscribe => rfl
  | openSettings s => obtain ⟨_, h⟩ := hr (by simp); cases h

/-- Delivered values always come from `values`, so they are always valid. -/
theorem handle_values_valid {ps : Props} {pers : String → Option Val} {f : Bool}
    {r : ConfigReq} {id : Option String} {vals : List (String × Val)}
    (h : ConfigOut.values id vals ∈ handle (some ps) pers f r) : vals = values ps pers := by
  cases r with
  | get => simp [handle] at h; exact h.2
  | subscribe => simp [handle] at h; exact h.2
  | openSettings s => simp only [handle] at h; split at h <;> simp at h

end Napplet.NapConfig
