/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-THEME (`theme`)

Read-only. `colors` (background, text, primary) are required by the type.
`theme.changed` goes only to endpoints with `theme` exposed.
-/

namespace Napplet.NapTheme

structure ThemeColors where
  background : String
  text : String
  primary : String
  deriving DecidableEq, Repr

structure ThemeFont where
  name : String
  url : String
  deriving DecidableEq, Repr

structure ThemeBackground where
  url : String
  mode : String
  mime : String
  deriving DecidableEq, Repr

structure Theme where
  colors : ThemeColors
  body : Option ThemeFont := none
  titleFont : Option ThemeFont := none
  background : Option ThemeBackground := none
  title : Option String := none
  deriving DecidableEq, Repr

inductive ThemeOut where
  | getResult (to : Endpoint) (id : String) (theme : Option Theme) (error : Option String)
  | changed (to : Endpoint) (theme : Theme)
  deriving DecidableEq, Repr

/-- Answer `theme.get` with the same `id`. -/
def get (to : Endpoint) (id : String) (current : Option Theme) : ThemeOut :=
  match current with
  | some t => .getResult to id (some t) none
  | none => .getResult to id none (some "no active theme")

theorem get_same_id (to : Endpoint) (id : String) (cur : Option Theme) :
    ∃ t e, get to id cur = .getResult to id t e := by
  cases cur <;> exact ⟨_, _, rfl⟩

/-- A result carries a theme or an error, never both. -/
theorem get_theme_xor_error (to : Endpoint) (id : String) (cur : Option Theme) :
    ∃ t e, get to id cur = .getResult to id t e ∧ (t.isSome ≠ e.isSome) := by
  cases cur <;> exact ⟨_, _, rfl, by simp⟩

/-- Broadcast `theme.changed` to endpoints that have `theme` exposed. -/
def broadcast (eps : List (Endpoint × List Domain)) (t : Theme) : List ThemeOut :=
  (eps.filter fun e => decide (Domain.theme ∈ e.2)).map fun e => .changed e.1 t

theorem broadcast_only_exposed {eps : List (Endpoint × List Domain)} {t t' : Theme}
    {to : Endpoint} (h : ThemeOut.changed to t' ∈ broadcast eps t) :
    ∃ ds, (to, ds) ∈ eps ∧ Domain.theme ∈ ds := by
  simp only [broadcast, List.mem_map, List.mem_filter, decide_eq_true_eq,
    ThemeOut.changed.injEq] at h
  obtain ⟨⟨a, ds⟩, ⟨hm, ht⟩, rfl, -⟩ := h
  exact ⟨ds, hm, ht⟩

theorem broadcast_complete {eps : List (Endpoint × List Domain)} {t : Theme} {to : Endpoint}
    {ds : List Domain} (hm : (to, ds) ∈ eps) (ht : Domain.theme ∈ ds) :
    ThemeOut.changed to t ∈ broadcast eps t := by
  simp [broadcast]
  exact ⟨ds, hm, ht⟩

end Napplet.NapTheme
