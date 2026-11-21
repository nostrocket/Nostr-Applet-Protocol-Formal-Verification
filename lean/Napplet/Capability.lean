/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Manifest

/-!
# Capabilities and domain availability (NIP-5D §Required and Optional Capabilities,
§Runtime Domain Availability, §Shell Handlers)

* What a napplet gets is `exposedFor cfg id`: a function of shell support and
  per-identity policy only. Manifest declarations (`R`, `O`, `z`, `i`) and shell
  advertisements (`N`) never appear in it, so they cannot widen exposure.
* `missingRequired` is the load-time check of the complete `R` set.
* `andFilterMatch` models the proposed NIP-91 `&R` relay filter, and
  `andFilter_is_not_compatibility` shows it is not a compatibility test.
-/

namespace Napplet

/-- Shell-side configuration. -/
structure ShellConfig where
  /-- Domains this shell implements. -/
  supported : List Domain
  /-- Per-napplet policy: which domains this identity may use. -/
  policy : Identity → List Domain
  /-- Reject (rather than warn) when a required domain is unavailable. -/
  strictRequired : Bool := true

/-- Domains injected into `window.napplet` for this identity. -/
def exposedFor (cfg : ShellConfig) (id : Identity) : List Domain :=
  cfg.supported.filter fun d => decide (d ∈ cfg.policy id)

theorem exposedFor_supported {cfg : ShellConfig} {id : Identity} {d : Domain}
    (h : d ∈ exposedFor cfg id) : d ∈ cfg.supported := by
  simp [exposedFor] at h; exact h.1

theorem exposedFor_policy {cfg : ShellConfig} {id : Identity} {d : Domain}
    (h : d ∈ exposedFor cfg id) : d ∈ cfg.policy id := by
  simp [exposedFor] at h; exact h.2

/-- Declarations are not grants: two manifests with the same identity get the
same exposure whatever their `R`/`O`/`z`/`i` tags say. -/
theorem exposure_ignores_declarations (cfg : ShellConfig) (v w : VerifiedManifest)
    (h : v.identity = w.identity) :
    exposedFor cfg v.identity = exposedFor cfg w.identity := by
  rw [h]

/-- First required domain name the shell cannot expose, if any. Unknown names
count as missing. -/
def missingRequired (exposed : List Domain) (required : List String) : Option String :=
  required.find? fun n =>
    match Domain.ofName? n with
    | some d => !decide (d ∈ exposed)
    | none => true

theorem missingRequired_none {exposed : List Domain} {required : List String}
    (h : missingRequired exposed required = none) :
    ∀ n ∈ required, ∃ d, Domain.ofName? n = some d ∧ d ∈ exposed := by
  intro n hn
  simp only [missingRequired, List.find?_eq_none] at h
  have := h n hn
  revert this
  cases hd : Domain.ofName? n with
  | none => simp
  | some d => simp_all

/-! ### Shell handler compatibility (kind 31990 `N` tags) -/

/-- Full functionality iff manifest `R` ⊆ shell `N`. -/
def compatible (required advertised : List Domain) : Bool :=
  required.all fun d => decide (d ∈ advertised)

theorem compatible_iff (r n : List Domain) :
    compatible r n = true ↔ ∀ d ∈ r, d ∈ n := by
  simp [compatible]

/-- NIP-91 `&R` filter: every filter value appears in the event's `R` set. -/
def andFilterMatch (filter required : List Domain) : Bool :=
  filter.all fun d => decide (d ∈ required)

/-- The spec's example: a shell offering `relay` and `theme` is compatible with a
napplet requiring only `relay`, but `&R: ["relay","theme"]` does not return it.
So `&R` is only a discovery optimisation; clients MUST check `R` locally. -/
theorem andFilter_is_not_compatibility :
    let shell := [Domain.relay, .theme]
    let napplet := [Domain.relay]
    compatible napplet shell = true ∧ andFilterMatch shell napplet = false := by
  decide

/-- And the converse failure: `&R` can return a napplet that also requires a
domain the shell lacks. -/
theorem andFilter_admits_incompatible :
    let shell := [Domain.relay, .theme]
    let napplet := [Domain.relay, .theme, .storage]
    compatible napplet shell = false ∧ andFilterMatch shell napplet = true := by
  decide

end Napplet
