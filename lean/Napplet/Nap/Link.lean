/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-LINK (`link`, PR napplet/naps#53 branch `nap-link`)

Shell-mediated external link opening.

Results:
* `opened_scheme_safe`: only absolute URLs with a policy-allowed scheme are opened;
  `javascript:`, `data:`, `blob:`, `file:` and other local or code-bearing schemes
  never are, whatever the policy says (`forbidden_never_opened`).
* `relative_rejected`.
* `label_irrelevant`: the napplet-supplied `label` never affects the decision.
* `opened_requires_user_or_rule`: a link opens only with user approval or a
  persisted allow rule for this napplet.
* `opened_noopener`: every open is done without `window.opener`.
* `open_same_id`.
-/

namespace Napplet.NapLink

/-- Scheme of an absolute URL: non-empty ASCII letters/digits/`+-.`, then `:`. -/
def schemeOf (url : String) : Option String :=
  let cs := url.toList
  let s := cs.takeWhile (· != ':')
  if s.isEmpty || s.length == cs.length then none
  else if s.head?.map Char.isAlpha != some true then none
  else if s.all (fun c => c.isAlphanum || c == '+' || c == '-' || c == '.') then
    some (String.ofList (s.map Char.toLower))
  else none

#guard schemeOf "https://example.com" == some "https"
#guard schemeOf "JavaScript:alert(1)" == some "javascript"
#guard schemeOf "/relative/path" == none
#guard schemeOf "example.com" == none

/-- Local or code-bearing schemes. Never opened. -/
def forbidden : List String :=
  ["javascript", "data", "blob", "file", "vbscript", "about", "chrome", "filesystem"]

structure LinkEnv where
  /-- Schemes the shell's policy allows (`https` by default; `nostr`, `mailto` MAY). -/
  allowedSchemes : List String := ["https", "http"]
  /-- Persisted per-napplet allow rule for a URL (allow napplet / hostname / URL). -/
  ruleAllows : Endpoint → String → Bool
  /-- Persisted per-napplet deny rule. -/
  ruleDenies : Endpoint → String → Bool
  /-- Outcome of the prompt, which shows napplet identity and the destination. -/
  userApproves : Endpoint → String → Bool

inductive LinkStatus where
  | opened
  | denied
  deriving DecidableEq, Repr

inductive LinkOut where
  /-- Open outside the sandbox. `noopener` is part of the action. -/
  | openExternal (url : String) (noopener : Bool)
  | result (to : Endpoint) (id : String) (status : LinkStatus) (error : Option String)
  deriving DecidableEq, Repr

/-- `link.open(url, {label})`. -/
def openLink (env : LinkEnv) (sender : Endpoint) (id : String) (url : String)
    (_label : Option String) : List LinkOut :=
  match schemeOf url with
  | none => [.result sender id .denied (some "invalid-url")]
  | some s =>
    if s ∈ forbidden ∨ s ∉ env.allowedSchemes then
      [.result sender id .denied (some "unsupported-scheme")]
    else if env.ruleDenies sender url then [.result sender id .denied (some "blocked-by-policy")]
    else if env.ruleAllows sender url || env.userApproves sender url then
      [.openExternal url true, .result sender id .opened none]
    else [.result sender id .denied (some "user-denied")]

theorem opened_inv {env : LinkEnv} {sender : Endpoint} {id url u : String} {label : Option String}
    {n : Bool} (h : LinkOut.openExternal u n ∈ openLink env sender id url label) :
    u = url ∧ n = true ∧ ∃ s, schemeOf url = some s ∧ s ∉ forbidden ∧ s ∈ env.allowedSchemes ∧
      env.ruleDenies sender url = false ∧
      (env.ruleAllows sender url = true ∨ env.userApproves sender url = true) := by
  unfold openLink at h
  split at h
  · simp at h
  · rename_i s hs
    split at h
    · simp at h
    · rename_i hf
      split at h
      · simp at h
      · rename_i hd
        split at h
        · rename_i ha
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [not_or, Classical.not_not] at hf
          simp only [Bool.or_eq_true] at ha
          exact ⟨rfl, rfl, s, hs, hf.1, hf.2, by simpa using hd, ha⟩
        · simp at h

theorem opened_scheme_safe {env : LinkEnv} {sender : Endpoint} {id url u : String}
    {label : Option String} {n : Bool} (h : LinkOut.openExternal u n ∈ openLink env sender id url label) :
    ∃ s, schemeOf url = some s ∧ s ∉ forbidden ∧ s ∈ env.allowedSchemes := by
  obtain ⟨-, -, s, h1, h2, h3, -⟩ := opened_inv h
  exact ⟨s, h1, h2, h3⟩

/-- Even if a shell's policy lists a forbidden scheme, it is never opened. -/
theorem forbidden_never_opened {env : LinkEnv} {sender : Endpoint} {id url : String}
    {label : Option String} {s : String} (hs : schemeOf url = some s) (hf : s ∈ forbidden) :
    ∀ u n, LinkOut.openExternal u n ∉ openLink env sender id url label := by
  intro u n h
  obtain ⟨s', h1, h2, -⟩ := opened_scheme_safe h
  rw [hs] at h1
  cases h1
  exact h2 hf

theorem relative_rejected {env : LinkEnv} {sender : Endpoint} {id url : String}
    {label : Option String} (hs : schemeOf url = none) :
    openLink env sender id url label = [.result sender id .denied (some "invalid-url")] := by
  simp [openLink, hs]

/-- The napplet-supplied label is never proof of destination or intent. -/
theorem label_irrelevant (env : LinkEnv) (sender : Endpoint) (id url : String)
    (l₁ l₂ : Option String) : openLink env sender id url l₁ = openLink env sender id url l₂ := rfl

theorem opened_requires_user_or_rule {env : LinkEnv} {sender : Endpoint} {id url u : String}
    {label : Option String} {n : Bool} (h : LinkOut.openExternal u n ∈ openLink env sender id url label) :
    env.ruleAllows sender url = true ∨ env.userApproves sender url = true := by
  obtain ⟨-, -, -, -, -, -, -, h'⟩ := opened_inv h
  exact h'

theorem opened_noopener {env : LinkEnv} {sender : Endpoint} {id url u : String}
    {label : Option String} {n : Bool} (h : LinkOut.openExternal u n ∈ openLink env sender id url label) :
    n = true :=
  (opened_inv h).2.1

theorem open_same_id (env : LinkEnv) (sender : Endpoint) (id url : String) (l : Option String) :
    ∃ st e, LinkOut.result sender id st e ∈ openLink env sender id url l := by
  unfold openLink
  split
  · exact ⟨_, _, List.mem_singleton_self _⟩
  · split
    · exact ⟨_, _, List.mem_singleton_self _⟩
    · split
      · exact ⟨_, _, List.mem_singleton_self _⟩
      · split
        · exact ⟨_, _, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩
        · exact ⟨_, _, List.mem_singleton_self _⟩

end Napplet.NapLink
