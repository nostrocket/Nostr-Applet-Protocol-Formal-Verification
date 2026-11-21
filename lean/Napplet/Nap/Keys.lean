import Napplet.Basic

/-!
# NAP-KEYS (`keys`, PR napplet/naps#9 branch `nub-keys`)

Keyboard forwarding and action keybindings.

Combos are modelled as a set of modifiers plus a key, rendered in one canonical
order `Alt+Ctrl+Shift+Meta+Key`. This resolves the PR's open issue that the spec
calls that order "alphabetical" when it is not: the model uses the stated order,
and `normalize` makes the input order irrelevant.

Results:
* `parse_render`, `normalize_idem`, `normalize_order_free`: one canonical form.
* `Inv` (no reserved binding, no key bound twice) is preserved by `register` and
  `unregister`.
* `reserved_never_suppressed`: Tab, Shift+Tab, Escape and browser shortcuts always
  reach the browser.
* `text_input_never_forwarded`: keystrokes in text fields never leave the napplet.
* `register_duplicate_rejected`, `register_other_napplets_untouched`,
  `bindings_push_complete`.
-/

namespace Napplet.NapKeys

structure Combo where
  alt : Bool := false
  ctrl : Bool := false
  shift : Bool := false
  metaKey : Bool := false
  key : String
  deriving DecidableEq, Repr

def modifierNames : List String := ["Alt", "Ctrl", "Shift", "Meta"]

/-- Canonical rendering: `Alt+Ctrl+Shift+Meta+Key`, as tokens. -/
def render (c : Combo) : List String :=
  (if c.alt then ["Alt"] else []) ++ (if c.ctrl then ["Ctrl"] else []) ++
  (if c.shift then ["Shift"] else []) ++ (if c.metaKey then ["Meta"] else []) ++ [c.key]

/-- Parse `+`-separated tokens in any modifier order. Repeated modifiers, a bare
modifier or an empty key are rejected. -/
def parse : List String → Option Combo
  | [] => none
  | [k] => if k ∈ modifierNames ∨ k = "" then none else some { key := k }
  | m :: rest =>
    match parse rest with
    | none => none
    | some c =>
      if m = "Alt" then (if c.alt then none else some { c with alt := true })
      else if m = "Ctrl" then (if c.ctrl then none else some { c with ctrl := true })
      else if m = "Shift" then (if c.shift then none else some { c with shift := true })
      else if m = "Meta" then (if c.metaKey then none else some { c with metaKey := true })
      else none

def validKey (k : String) : Prop := k ∉ modifierNames ∧ k ≠ ""

theorem parse_key {k : String} (hk : validKey k) : parse [k] = some { key := k } := by
  have h : ¬(k ∈ modifierNames ∨ k = "") := fun h => h.elim hk.1 hk.2
  simp only [parse, h, ↓reduceIte]

theorem parse_render (c : Combo) (hk : validKey c.key) : parse (render c) = some c := by
  obtain ⟨a, ct, s, m, k⟩ := c
  simp only at hk
  have hn : ¬(k ∈ modifierNames ∨ k = "") := fun h => h.elim hk.1 hk.2
  cases a <;> cases ct <;> cases s <;> cases m <;>
    simp [render, parse, hn]

/-- Normalise a token list to canonical order. -/
def normalize (ts : List String) : Option (List String) := (parse ts).map render

theorem normalize_idem (c : Combo) (hk : validKey c.key) :
    normalize (render c) = some (render c) := by
  simp [normalize, parse_render c hk]

#guard normalize ["Ctrl", "Alt", "S"] == some ["Alt", "Ctrl", "S"]
#guard normalize ["Meta", "Shift", "Ctrl", "Alt", "P"] == some ["Alt", "Ctrl", "Shift", "Meta", "P"]
#guard normalize ["Ctrl", "Ctrl", "S"] == none
#guard normalize ["Ctrl"] == none

/-- Two token lists that parse to the same combo normalise identically. -/
theorem normalize_order_free {ts us : List String} (h : parse ts = parse us) :
    normalize ts = normalize us := by
  simp [normalize, h]

/-! ### Reserved keys -/

def reserved : List Combo :=
  [{ key := "Tab" }, { shift := true, key := "Tab" }, { key := "Escape" },
   { ctrl := true, key := "w" }, { ctrl := true, key := "t" }, { ctrl := true, key := "l" },
   { ctrl := true, key := "W" }, { ctrl := true, key := "T" }, { ctrl := true, key := "L" }]

/-! ### Action registration -/

structure Binding where
  owner : Endpoint
  actionId : String
  label : String
  combo : Option Combo
  deriving DecidableEq, Repr

structure KeysState where
  bindings : List Binding

/-- Invariant: no reserved combo is bound, and no combo is bound twice. -/
structure Inv (s : KeysState) : Prop where
  no_reserved : ∀ b ∈ s.bindings, ∀ c, b.combo = some c → c ∉ reserved
  unique : ∀ b₁ ∈ s.bindings, ∀ b₂ ∈ s.bindings, ∀ c,
    b₁.combo = some c → b₂.combo = some c → b₁ = b₂

inductive KeysOut where
  | registerResult (to : Endpoint) (id : String) (actionId : String) (binding : Option Combo)
      (error : Option String)
  /-- Complete list of the napplet's bindings (not a diff). -/
  | bindings (to : Endpoint) (list : List (String × Combo))
  deriving DecidableEq, Repr

def bindingsOf (s : KeysState) (e : Endpoint) : List (String × Combo) :=
  s.bindings.filterMap fun b => if b.owner = e then b.combo.map (b.actionId, ·) else none

/-- The shell assigns `defaultKey` only if it is not reserved and not already bound. -/
def assign (s : KeysState) (dk : Option Combo) : Option Combo :=
  match dk with
  | some c => if c ∈ reserved ∨ s.bindings.any (·.combo == some c) then none else some c
  | none => none

def register (s : KeysState) (sender : Endpoint) (id actionId label : String)
    (defaultKey : Option Combo) : KeysState × List KeysOut :=
  if s.bindings.any (fun b => b.owner == sender && b.actionId == actionId) then
    (s, [.registerResult sender id actionId none (some "duplicate action ID")])
  else
    let c := assign s defaultKey
    let s' : KeysState := { bindings := ⟨sender, actionId, label, c⟩ :: s.bindings }
    (s', [.registerResult sender id actionId c none, .bindings sender (bindingsOf s' sender)])

def unregister (s : KeysState) (sender : Endpoint) (actionId : String) :
    KeysState × List KeysOut :=
  let s' : KeysState :=
    { bindings := s.bindings.filter fun b => !(b.owner == sender && b.actionId == actionId) }
  (s', [.bindings sender (bindingsOf s' sender)])

theorem assign_safe {s : KeysState} {dk : Option Combo} {c : Combo} (h : assign s dk = some c) :
    c ∉ reserved ∧ ∀ b ∈ s.bindings, b.combo ≠ some c := by
  unfold assign at h
  split at h
  · rename_i c'
    split at h
    · simp at h
    · rename_i hc
      simp at h
      subst h
      simp only [not_or, List.any_eq_true, beq_iff_eq, not_exists, not_and] at hc
      exact ⟨hc.1, hc.2⟩
  · simp at h

theorem Inv.register {s : KeysState} (hi : Inv s) (sender : Endpoint) (id aid label : String)
    (dk : Option Combo) : Inv (register s sender id aid label dk).1 := by
  unfold Napplet.NapKeys.register
  split
  · exact hi
  · dsimp only
    constructor
    · intro b hb c hc
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (assign_safe hc).1
      · exact hi.no_reserved b hb c hc
    · intro b₁ h₁ b₂ h₂ c hc₁ hc₂
      rcases List.mem_cons.mp h₁ with rfl | h₁ <;> rcases List.mem_cons.mp h₂ with rfl | h₂
      · rfl
      · exact absurd hc₂ ((assign_safe hc₁).2 b₂ h₂)
      · exact absurd hc₁ ((assign_safe hc₂).2 b₁ h₁)
      · exact hi.unique b₁ h₁ b₂ h₂ c hc₁ hc₂

theorem Inv.unregister {s : KeysState} (hi : Inv s) (sender : Endpoint) (aid : String) :
    Inv (unregister s sender aid).1 := by
  constructor
  · intro b hb c hc
    simp only [Napplet.NapKeys.unregister, List.mem_filter] at hb
    exact hi.no_reserved b hb.1 c hc
  · intro b₁ h₁ b₂ h₂ c hc₁ hc₂
    simp only [Napplet.NapKeys.unregister, List.mem_filter] at h₁ h₂
    exact hi.unique b₁ h₁.1 b₂ h₂.1 c hc₁ hc₂

theorem register_duplicate_rejected {s : KeysState} {sender : Endpoint} {id aid label : String}
    {dk : Option Combo} {b : Binding} (hb : b ∈ s.bindings) (ho : b.owner = sender)
    (ha : b.actionId = aid) :
    register s sender id aid label dk =
      (s, [.registerResult sender id aid none (some "duplicate action ID")]) := by
  have h : s.bindings.any (fun b => b.owner == sender && b.actionId == aid) = true := by
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨b, hb, ho, ha⟩
  simp only [register, h, ↓reduceIte]

/-- Registration never changes another napplet's bindings. -/
theorem register_other_napplets_untouched {s : KeysState} {sender : Endpoint}
    {id aid label : String} {dk : Option Combo} {b : Binding} (hb : b ∈ s.bindings) :
    b ∈ (register s sender id aid label dk).1.bindings := by
  unfold register
  split
  · exact hb
  · exact List.mem_cons_of_mem _ hb

/-- The pushed `keys.bindings` is the napplet's complete current list. -/
theorem bindings_push_complete {s : KeysState} {sender : Endpoint} {id aid label : String}
    {dk : Option Combo} {l : List (String × Combo)}
    (h : KeysOut.bindings sender l ∈ (register s sender id aid label dk).2) :
    l = bindingsOf (register s sender id aid label dk).1 sender := by
  unfold register at h ⊢
  split at h
  · simp at h
  · rename_i hn
    simp only [hn]
    simp at h
    exact h

/-! ### Smart forwarding (shim) -/

structure KeyEvent where
  combo : Combo
  inTextInput : Bool
  bareModifier : Bool
  composing : Bool
  deriving DecidableEq, Repr

inductive Decision where
  /-- Default browser handling inside the napplet; nothing leaves. -/
  | default
  /-- `preventDefault()` and run the local action handler. -/
  | localAction
  /-- Send `keys.forward` to the shell. -/
  | forward
  deriving DecidableEq, Repr

def route (suppress : List Combo) (ev : KeyEvent) : Decision :=
  if ev.inTextInput || ev.bareModifier || ev.composing then .default
  else if ev.combo ∈ reserved then .forward
  else if ev.combo ∈ suppress then .localAction
  else .forward

/-- Keystrokes in text inputs never leave the napplet (no credential leakage). -/
theorem text_input_never_forwarded (sup : List Combo) (ev : KeyEvent) (h : ev.inTextInput = true) :
    route sup ev = .default := by
  simp [route, h]

/-- Reserved keys are never suppressed, whatever the suppress list says. -/
theorem reserved_never_suppressed (sup : List Combo) (ev : KeyEvent) (h : ev.combo ∈ reserved) :
    route sup ev ≠ .localAction := by
  unfold route
  split
  · simp
  · simp_all

/-- In a shell satisfying `Inv`, the suppress list built from its bindings contains
no reserved combo. -/
theorem suppress_list_safe {s : KeysState} (hi : Inv s) (e : Endpoint) :
    ∀ p ∈ bindingsOf s e, p.2 ∉ reserved := by
  intro p hp
  simp only [bindingsOf, List.mem_filterMap] at hp
  obtain ⟨b, hb, hm⟩ := hp
  split at hm
  · simp only [Option.map_eq_some_iff] at hm
    obtain ⟨c, hc, rfl⟩ := hm
    exact hi.no_reserved b hb c hc
  · simp at hm

end Napplet.NapKeys
