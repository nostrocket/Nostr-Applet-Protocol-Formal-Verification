/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# Finite maps and interval sets

The model's state uses functions for maps (`WindowId → Option FrameStatus`, `Scope → KV`,
...). A port stores finite data instead. This file gives the two finite representations
the refinement (`Napplet.Refine`) uses.

* `FMap α β`: an association list with a default. `get m a` is the value of the first
  entry for `a`, or the default. `tab` re-tabulates a function on a list of candidate
  keys and keeps only entries that differ from the default; `get_tab` says the result
  denotes the function whenever it is the default off the candidates.
* `Ivs`: a set of naturals as a sorted list of disjoint, non-adjacent closed intervals.
  It stores the shell's removed windows. `mem_insert` is its meaning; `insert` keeps the
  canonical form (`Canon`), and `Canon.length_le` bounds the number of intervals by the
  number of gaps (`length_le_gaps`).
-/

namespace Napplet

/-! ## Association lists -/

def alookup {α β : Type} [DecidableEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (k, v) :: r, a => if k = a then some v else alookup r a

theorem alookup_none_of_not_mem {α β : Type} [DecidableEq α] :
    ∀ {l : List (α × β)} {a : α}, a ∉ l.map Prod.fst → alookup l a = none
  | [], _, _ => rfl
  | (k, v) :: r, a, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [alookup, Ne.symm h.1, ↓reduceIte]
    exact alookup_none_of_not_mem h.2

theorem alookup_mem {α β : Type} [DecidableEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, alookup l a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [alookup] at h
  | (k, v) :: r, a, b, h => by
    simp only [alookup] at h
    split at h
    · rename_i hk; cases h; subst hk; simp
    · exact List.mem_cons_of_mem _ (alookup_mem h)

/-- Remove repeated elements, keeping the last occurrence. -/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then dedup l else a :: dedup l

theorem mem_dedup {α : Type} [DecidableEq α] : ∀ {l : List α} {a : α}, a ∈ dedup l ↔ a ∈ l
  | [], _ => by simp [dedup]
  | x :: l, a => by
    simp only [dedup]
    split
    · rename_i hx
      rw [mem_dedup]
      constructor
      · intro h; exact List.mem_cons_of_mem _ h
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact hx
        · exact h
    · simp [mem_dedup]

theorem nodup_dedup {α : Type} [DecidableEq α] : ∀ (l : List α), (dedup l).Nodup
  | [] => List.nodup_nil
  | x :: l => by
    simp only [dedup]
    split
    · exact nodup_dedup l
    · rename_i hx
      exact List.nodup_cons.mpr ⟨fun h => hx (mem_dedup.mp h), nodup_dedup l⟩

/-! ## Finite maps with a default -/

/-- A finite map: `entries` with a default for every other key. -/
structure FMap (α β : Type) where
  dflt : β
  entries : List (α × β)
  deriving Repr, DecidableEq

namespace FMap

variable {α β : Type} [DecidableEq α]

def get (m : FMap α β) (a : α) : β := (alookup m.entries a).getD m.dflt

def keys (m : FMap α β) : List α := m.entries.map Prod.fst

/-- The empty map with default `d`. -/
def const (d : β) : FMap α β := ⟨d, []⟩

@[simp] theorem get_const (d : β) : (const d : FMap α β).get = fun _ => d := rfl

/-- Re-tabulate `f` on the candidate keys `ks`, keeping only entries `keep` accepts
(entries `keep` rejects must equal the default). -/
def tab (d : β) (keep : β → Bool) (ks : List α) (f : α → β) : FMap α β :=
  ⟨d, (dedup ks).filterMap fun k => if keep (f k) then some (k, f k) else none⟩

theorem alookup_tab {keep : β → Bool} {f : α → β} :
    ∀ {ks : List α} (_ : ks.Nodup) (a : α),
      alookup (ks.filterMap fun k => if keep (f k) then some (k, f k) else none) a =
        if a ∈ ks ∧ keep (f a) = true then some (f a) else none
  | [], _, a => by simp [alookup]
  | k :: ks, hn, a => by
    have hn' := List.nodup_cons.mp hn
    simp only [List.filterMap_cons]
    have ih := alookup_tab (keep := keep) (f := f) hn'.2 a
    by_cases hk : keep (f k) = true
    · simp only [hk, ↓reduceIte, alookup]
      by_cases hka : k = a
      · subst hka; simp [hk]
      · simp only [hka, ↓reduceIte, ih, List.mem_cons]
        simp [Ne.symm hka]
    · simp only [hk, Bool.false_eq_true, ↓reduceIte, ih, List.mem_cons]
      by_cases hka : k = a
      · subst hka; simp [hk, hn'.1]
      · simp [Ne.symm hka]

/-- `tab` denotes `f` when `f` is the default off the candidates and `keep` rejects
only the default. -/
theorem get_tab {d : β} {keep : β → Bool} {ks : List α} {f : α → β}
    (hk : ∀ b, keep b = false → b = d) (hf : ∀ a, a ∉ ks → f a = d) :
    (tab d keep ks f).get = f := by
  funext a
  simp only [get, tab]
  rw [alookup_tab (nodup_dedup ks) a]
  by_cases ha : a ∈ dedup ks
  · cases hka : keep (f a)
    · have e := hk (f a) hka
      simp [e]
    · simp [ha]
  · have : ¬ (a ∈ dedup ks ∧ keep (f a) = true) := fun h => ha h.1
    simp only [this, ↓reduceIte, Option.getD_none]
    exact (hf a (fun h => ha (mem_dedup.mpr h))).symm

theorem keys_tab {d : β} {keep : β → Bool} {ks : List α} {f : α → β} {a : α}
    (h : a ∈ (tab d keep ks f).keys) : a ∈ ks ∧ keep (f a) = true := by
  simp only [keys, tab, List.mem_map, List.mem_filterMap] at h
  obtain ⟨⟨k, v⟩, ⟨k', hk', he⟩, rfl⟩ := h
  split at he
  · rename_i hkeep; cases he; exact ⟨mem_dedup.mp hk', hkeep⟩
  · cases he

omit [DecidableEq α] in
theorem fst_filterMap_sublist {g : α → β} {keep : α → Bool} : ∀ (l : List α),
    ((l.filterMap fun k => if keep k then some (k, g k) else none).map Prod.fst).Sublist l
  | [] => List.Sublist.slnil
  | k :: l => by
    by_cases hk : keep k = true
    · simp only [List.filterMap_cons, hk, ↓reduceIte, List.map_cons]
      exact (fst_filterMap_sublist l).cons_cons k
    · simp only [List.filterMap_cons, hk, Bool.false_eq_true, ↓reduceIte]
      exact (fst_filterMap_sublist l).cons k

theorem tab_nodup {d : β} {keep : β → Bool} {ks : List α} {f : α → β} :
    (tab d keep ks f).keys.Nodup :=
  List.Nodup.sublist (fst_filterMap_sublist (g := f) (keep := fun k => keep (f k)) (dedup ks))
    (nodup_dedup ks)

/-- Well-formed: keys are distinct and every entry is kept. -/
def WF (keep : β → Bool) (m : FMap α β) : Prop :=
  m.keys.Nodup ∧ ∀ e ∈ m.entries, keep e.2 = true

theorem tab_wf {d : β} {keep : β → Bool} {ks : List α} {f : α → β} : (tab d keep ks f).WF keep := by
  refine ⟨tab_nodup, ?_⟩
  intro e he
  simp only [tab, List.mem_filterMap] at he
  obtain ⟨k, -, h⟩ := he
  split at h
  · cases h; assumption
  · cases h

theorem get_of_mem {m : FMap α β} {a : α} {b : β} (hn : m.keys.Nodup) (h : (a, b) ∈ m.entries) :
    m.get a = b := by
  obtain ⟨d, l⟩ := m
  simp only [get, keys] at *
  induction l with
  | nil => simp at h
  | cons e l ih =>
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp h with rfl | h
    · simp [alookup]
    · simp only [alookup]
      have hne : e.1 ≠ a := by
        intro he; apply hn'.1; rw [he]; exact List.mem_map.mpr ⟨(a, b), h, rfl⟩
      simp only [hne, ↓reduceIte]
      exact ih hn'.2 h

theorem get_of_not_mem {m : FMap α β} {a : α} (h : a ∉ m.keys) : m.get a = m.dflt := by
  simp [get, alookup_none_of_not_mem h]

omit [DecidableEq α] in
theorem filterMap_self {keep : β → Bool} {g : α → β} : ∀ (l : List (α × β)),
    (l.map Prod.fst).Nodup → (∀ e ∈ l, g e.1 = e.2) → (∀ e ∈ l, keep e.2 = true) →
    (l.map Prod.fst).filterMap (fun k => if keep (g k) then some (k, g k) else none) = l
  | [], _, _, _ => rfl
  | e :: l, hn, hg, hk => by
    have hn' := List.nodup_cons.mp hn
    have he := hg e (by simp)
    have hke := hk e (by simp)
    simp only [List.map_cons, List.filterMap_cons, he, hke, ↓reduceIte]
    rw [filterMap_self l hn'.2 (fun e' h => hg e' (List.mem_cons_of_mem _ h))
      (fun e' h => hk e' (List.mem_cons_of_mem _ h))]

/-- Re-tabulating a well-formed map on its own keys gives it back. -/
theorem tab_self {m : FMap α β} {keep : β → Bool} (hw : m.WF keep) :
    tab m.dflt keep m.keys m.get = m := by
  obtain ⟨d, l⟩ := m
  obtain ⟨hn, hk⟩ := hw
  simp only [keys] at hn
  have hd : dedup (l.map Prod.fst) = l.map Prod.fst := by
    clear hk
    induction l with
    | nil => rfl
    | cons e l ih =>
      have hn' := List.nodup_cons.mp hn
      simp only [List.map_cons, dedup, hn'.1, ↓reduceIte, ih hn'.2]
  simp only [tab, keys, hd]
  rw [filterMap_self l hn (fun e he => get_of_mem (m := ⟨d, l⟩) hn he) hk]

end FMap

/-! ## Interval sets -/

/-- A set of naturals: closed intervals `[lo, hi]`, sorted, disjoint and non-adjacent
(`Canon`). -/
abbrev Ivs := List (Nat × Nat)

namespace Ivs
def mem (I : Ivs) (x : Nat) : Bool := I.any fun iv => iv.1 ≤ x && x ≤ iv.2
def insert (x : Nat) : Ivs → Ivs
  | [] => [(x, x)]
  | (a, b) :: rest =>
    if x + 1 < a then (x, x) :: (a, b) :: rest
    else if x + 1 = a then (x, b) :: rest
    else if x ≤ b then (a, b) :: rest
    else if x = b + 1 then
      match rest with
      | (c, d) :: rest' => if x + 1 = c then (a, d) :: rest' else (a, x) :: (c, d) :: rest'
      | [] => [(a, x)]
    else (a, b) :: insert x rest
theorem mem_cons {a b : Nat} {I : Ivs} {x : Nat} :
    mem ((a, b) :: I) x = true ↔ (a ≤ x ∧ x ≤ b) ∨ mem I x = true := by simp [mem]
theorem mem_cons_eq (a b : Nat) (I : Ivs) (x : Nat) :
    mem ((a, b) :: I) x = ((decide (a ≤ x) && decide (x ≤ b)) || mem I x) := by simp [mem]
theorem mem_nil (x : Nat) : mem [] x = false := rfl
/-- Every interval is non-empty. -/
def NE (I : Ivs) : Prop := ∀ iv ∈ I, iv.1 ≤ iv.2

theorem mem_insert (x : Nat) : ∀ (I : Ivs) (_ : NE I) (y : Nat),
    mem (insert x I) y = true ↔ y = x ∨ mem I y = true
  | [], _, y => by simp [insert, mem_cons, mem_nil]; omega
  | (a, b) :: rest, hne, y => by
    have hab : a ≤ b := hne (a, b) (by simp)
    have hr : NE rest := fun iv h => hne iv (List.mem_cons_of_mem _ h)
    unfold insert
    by_cases h1 : x + 1 < a
    · rw [ite_eq_left h1]; simp only [mem_cons]; cases mem rest y <;> simp <;> omega
    rw [ite_eq_right h1]
    by_cases h2 : x + 1 = a
    · rw [ite_eq_left h2]; simp only [mem_cons]; cases mem rest y <;> simp <;> omega
    rw [ite_eq_right h2]
    by_cases h3 : x ≤ b
    · rw [ite_eq_left h3]; simp only [mem_cons]; cases mem rest y <;> simp <;> omega
    rw [ite_eq_right h3]
    by_cases h4 : x = b + 1
    · rw [ite_eq_left h4]
      match rest, hr with
      | [], _ => simp [mem_cons, mem_nil]; omega
      | (c, d) :: rest', hr =>
        have hcd : c ≤ d := hr (c, d) (by simp)
        simp only
        by_cases h5 : x + 1 = c
        · rw [ite_eq_left h5]; simp only [mem_cons]; cases mem rest' y <;> simp <;> omega
        · rw [ite_eq_right h5]; simp only [mem_cons]; cases mem rest' y <;> simp <;> omega
    · rw [ite_eq_right h4]; simp only [mem_cons, mem_insert x rest hr y]
      cases mem rest y <;> simp <;> omega
/-- Canonical form: non-empty intervals, each starting at least two past the end of the
previous one, so a point not in the set lies between any two of them. -/
def Canon : Ivs → Prop
  | [] => True
  | (a, b) :: I => a ≤ b ∧ (∀ y, mem I y = true → b + 1 < y) ∧ Canon I

theorem Canon.ne : ∀ {I : Ivs}, Canon I → NE I
  | [], _ => fun _ h => by simp at h
  | (a, b) :: I, ⟨hab, _, hI⟩ => by
    intro iv h
    rcases List.mem_cons.mp h with rfl | h
    · exact hab
    · exact Canon.ne hI iv h

theorem canon_ge {a b : Nat} {I : Ivs} {y : Nat} (hc : Canon ((a, b) :: I))
    (hm : mem ((a, b) :: I) y = true) : a ≤ y := by
  rcases mem_cons.mp hm with h | h
  · exact h.1
  · have := hc.2.1 y h; have := hc.1; omega

theorem insert_canon (x : Nat) : ∀ (I : Ivs), Canon I → Canon (insert x I)
  | [], _ => by simp [insert, Canon, mem_nil]
  | (a, b) :: rest, hc => by
    have hab := hc.1
    have hgt := hc.2.1
    have hr := hc.2.2
    unfold insert
    by_cases h1 : x + 1 < a
    · rw [ite_eq_left h1]
      exact ⟨Nat.le_refl x, fun y hy => by have := canon_ge hc hy; omega, hc⟩
    rw [ite_eq_right h1]
    by_cases h2 : x + 1 = a
    · rw [ite_eq_left h2]; exact ⟨by omega, hgt, hr⟩
    rw [ite_eq_right h2]
    by_cases h3 : x ≤ b
    · rw [ite_eq_left h3]; exact hc
    rw [ite_eq_right h3]
    by_cases h4 : x = b + 1
    · rw [ite_eq_left h4]
      match rest, hgt, hr with
      | [], _, _ => simp [Canon, mem_nil]; omega
      | (c, d) :: rest', hgt, hr =>
        simp only
        by_cases h5 : x + 1 = c
        · rw [ite_eq_left h5]
          exact ⟨by have := hr.1; omega, hr.2.1, hr.2.2⟩
        · rw [ite_eq_right h5]
          have hcm : mem ((c, d) :: rest') c = true := mem_cons.mpr (.inl ⟨Nat.le_refl c, hr.1⟩)
          have hc' := hgt c hcm
          exact ⟨by omega, fun y hy => by have := canon_ge hr hy; omega, hr⟩
    · rw [ite_eq_right h4]
      refine ⟨hab, fun y hy => ?_, insert_canon x rest hr⟩
      rcases (mem_insert x rest hr.ne y).mp hy with rfl | hy
      · omega
      · exact hgt y hy

/-- One witness point per gap between consecutive intervals. -/
def gaps : Ivs → List Nat
  | [] => []
  | [_] => []
  | (_, b) :: (c, d) :: rest => (b + 1) :: gaps ((c, d) :: rest)

theorem length_gaps : ∀ (I : Ivs), I.length ≤ (gaps I).length + 1
  | [] => by simp
  | [_] => by simp [gaps]
  | (a, b) :: (c, d) :: rest => by
    have := length_gaps ((c, d) :: rest)
    simp only [gaps, List.length_cons] at *; omega

theorem gaps_succ : ∀ {I : Ivs} {g : Nat}, NE I → g ∈ gaps I → ∃ y, mem I y = true ∧ g = y + 1
  | [], _, _, h => by simp [gaps] at h
  | [_], _, _, h => by simp [gaps] at h
  | (a, b) :: (c, d) :: rest, g, hne, h => by
    simp only [gaps, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨b, mem_cons.mpr (.inl ⟨hne (a, b) (by simp), Nat.le_refl b⟩), rfl⟩
    · obtain ⟨y, hy, rfl⟩ := gaps_succ (fun iv h' => hne iv (List.mem_cons_of_mem _ h')) h
      exact ⟨y, by rw [mem_cons, hy]; simp, rfl⟩

theorem gaps_canon : ∀ {I : Ivs}, Canon I →
    (gaps I).Nodup ∧ (∀ g ∈ gaps I, mem I g = false) ∧ (∀ n, (∀ y, mem I y = true → y < n) → ∀ g ∈ gaps I, g < n)
  | [], _ => by simp [gaps]
  | [_], _ => by simp [gaps]
  | (a, b) :: (c, d) :: rest, hc => by
    obtain ⟨hab, hgt, hr⟩ := hc
    obtain ⟨ih1, ih2, ih3⟩ := gaps_canon hr
    have hcm : mem ((c, d) :: rest) c = true := mem_cons.mpr (.inl ⟨Nat.le_refl c, hr.1⟩)
    have hbc := hgt c hcm
    have hbig : ∀ g ∈ gaps ((c, d) :: rest), b + 2 < g := by
      intro g hg
      obtain ⟨y, hy, rfl⟩ := gaps_succ hr.ne hg
      have := hgt y hy; omega
    simp only [gaps]
    refine ⟨List.nodup_cons.mpr ⟨fun h => by have := hbig _ h; omega, ih1⟩, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · cases hm : mem ((c, d) :: rest) (b + 1)
        · rw [mem_cons_eq, hm]; simp
        · have := hgt _ hm; omega
      · have := hbig g hg
        rw [mem_cons_eq, ih2 g hg]; simp; omega
    · intro n hb g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · have := hb c (by rw [mem_cons, hcm]; simp); omega
      · exact ih3 n (fun y hy => hb y (by rw [mem_cons, hy]; simp)) g hg

/-- The memory bound: if every element of a canonical interval set is below `n` and every
point below `n` is in the set or in `L`, the set has at most `|L| + 1` intervals. For the
shell's removed windows with consecutively numbered windows, `L` lists the live ones. -/
theorem length_le {I : Ivs} {n : Nat} {L : List Nat} (hc : Canon I)
    (hb : ∀ x, mem I x = true → x < n) (hcov : ∀ x, x < n → mem I x = true ∨ x ∈ L) :
    I.length ≤ L.length + 1 := by
  obtain ⟨hnd, hnot, hlt⟩ := gaps_canon hc
  have hsub : ∀ g ∈ gaps I, g ∈ L := by
    intro g hg
    rcases hcov g (hlt n hb g hg) with h | h
    · rw [hnot g hg] at h; cases h
    · exact h
  have := List.Nodup.length_le_of_subset hnd hsub
  have := length_gaps I
  omega

end Ivs

end Napplet
