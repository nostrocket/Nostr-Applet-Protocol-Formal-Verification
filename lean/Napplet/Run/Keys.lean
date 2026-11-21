/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Keys

/-!
# NAP-KEYS runtime component

Upstream: `napplet/naps` PR #9, `naps/NAP-KEYS.md` at `8869a4cf`.

Wire (napplet → shell): `keys.forward {key, code, ctrl, alt, shift, meta}` (no `id`),
`keys.registerAction {id, action: {id, label, defaultKey?}}`,
`keys.unregisterAction {actionId}` (no `id`).
Wire (shell → napplet): `keys.registerAction.result {id, actionId, binding?, error?}`,
`keys.bindings {bindings: [{actionId, key}]}` (the napplet's complete list, not a
diff), `keys.action {actionId}`.

Combos. A combo string is `+`-separated tokens: modifiers `Alt`, `Ctrl`, `Shift`,
`Meta` in any order, then the key (`KeyboardEvent.key`). The runtime parses with
`NapKeys.parse` and always emits the canonical order `Alt+Ctrl+Shift+Meta+Key`
(`NapKeys.render`). A one-character key is upper-cased before parsing and
matching (`normKey`), so `Ctrl+s`, `Ctrl+S` and a forwarded `{key: "s", ctrl: true}`
are the same combo (as in kehto); a trailing `++` names the `+` key (`Ctrl++`).

Behaviour.
* `keys.forward` is handed to the host as `Effect.nap .keys "input"` (processed as
  if it happened in the shell). If the combo is bound to an action, the owner of
  that binding also gets `keys.action` (at most one owner, by `NapKeys.Inv`). The
  keystroke itself is never sent to any napplet.
* `keys.registerAction` uses `NapKeys.register`: a duplicate `(napplet, action id)`
  gets `error: "duplicate action ID"`; otherwise the action is stored and bound to
  `defaultKey` when that combo is not reserved and not bound by anyone, else left
  unbound; the result carries the canonical `binding` when bound, and the
  napplet's complete `keys.bindings` follows. A malformed request (no `action`
  object, non-string `action.id`/`label`/`defaultKey`) or an unparseable
  `defaultKey` gets `error: "invalid action"` with `actionId` echoing `action.id`
  (or `""`). This is not `errorReply`, because upstream makes `actionId` a
  required result field.
* `keys.unregisterAction` for a registered action removes it and pushes
  `keys.bindings`; for an unknown action it does nothing (no change, no push).
* Malformed `keys.forward` / `keys.unregisterAction` (fire-and-forget) and a
  `keys.registerAction` without a string `id`: dropped (`.reject []`).

State: the bindings, owned by the registering endpoint (`mentions`). Teardown
removes every binding of the endpoint and tells the host.
-/

/-! ## Host operations

All host-facing arguments name the endpoint by `port` (the `PortId` of the bound
port, which the host learned from `Output.bound`).

* `Effect.nap .keys "input" {port, key, code, ctrl, alt, shift, meta}`: a keystroke
  the napplet forwarded. The host processes it as if it occurred in the shell's own
  context (global hotkeys, command palette, workspace switching). It MUST NOT
  deliver it to any napplet. Fields are those of the wire message
  (`KeyboardEvent.key`, `KeyboardEvent.code`, modifier flags).
* `Effect.nap .keys "bindings" {port, actions: [{actionId, label, key?}]}`: the
  complete list of actions this endpoint has registered, with the current canonical
  combo for bound ones. Emitted whenever it changes and on teardown (then empty).
  The host shows labels in its own UI (keymap editor, command palette) and listens
  for the bound combos in its own context.
* `HostEvent.nap .keys "combo" {key}`: the user pressed combo `key` in the shell's own
  context (or a global hotkey fired). The runtime sends `keys.action` to the owner
  of the binding for that combo, if any.
* `HostEvent.nap .keys "trigger" {port, actionId}`: the user invoked an action from
  shell UI (for example a command palette). Sent as `keys.action` if that endpoint
  has registered the action.
* `HostEvent.nap .keys "rebind" {port, actionId, key}`: the user changed the binding of
  a registered action; `key` is a combo string, or `null` to unbind. A combo that is
  unparseable, reserved, or bound by any action is refused (nothing changes);
  otherwise the binding changes and the owner gets the new `keys.bindings`.
-/

namespace Napplet.Run.Keys

open NapKeys

structure St where
  ks : KeysState

def St.init : St := ⟨⟨[]⟩⟩

inductive Req where
  | forward (key code : String) (ctrl alt shift metaKey : Bool)
  | registerAction (id actionId label : String) (defaultKey : Option String)
  | unregisterAction (actionId : String)
  deriving DecidableEq, Repr

/-! ### Combo strings -/

/-- One-character keys are matched case-insensitively (upper-cased). -/
def normKey (k : String) : String := if k.length = 1 then k.toUpper else k

/-- A trailing `++` is the `+` key. -/
def fixPlus : List String → List String
  | ["", ""] => ["+"]
  | t :: ts => t :: fixPlus ts
  | [] => []

def comboOf? (s : String) : Option Combo := parse ((fixPlus (s.splitOn "+")).map normKey)

def comboStr (c : Combo) : String := "+".intercalate (render c)

/-- The combo a forwarded keystroke denotes. -/
def forwardCombo (key : String) (ctrl alt shift metaKey : Bool) : Combo :=
  { alt, ctrl, shift, metaKey, key := normKey key }

/-! ### Codec -/

def requestTypes : List String := ["keys.forward", "keys.registerAction", "keys.unregisterAction"]

def optStr (j : Json) (k : String) : Option (Option String) :=
  match j.get? k with
  | none => some none
  | some (.str s) => some (some s)
  | some _ => none

def registerError (id actionId error : String) : Json :=
  Json.msg "keys.registerAction.result"
    [("id", some (.str id)), ("actionId", some (.str actionId)), ("error", some (.str error))]

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some "keys.forward" =>
    match j.getStr? "key", j.getStr? "code", (j.get? "ctrl").bind Json.asBool?,
        (j.get? "alt").bind Json.asBool?, (j.get? "shift").bind Json.asBool?,
        (j.get? "meta").bind Json.asBool? with
    | some k, some c, some ct, some al, some sh, some me => .ok (.forward k c ct al sh me)
    | _, _, _, _, _, _ => .reject []
  | some "keys.registerAction" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      let a := (j.get? "action").getD .null
      match a.getStr? "id", a.getStr? "label", optStr a "defaultKey" with
      | some aid, some label, some dk => .ok (.registerAction id aid label dk)
      | aid, _, _ => .reject [registerError id (aid.getD "") "invalid action"]
  | some "keys.unregisterAction" =>
    match j.getStr? "actionId" with
    | some aid => .ok (.unregisterAction aid)
    | none => .reject []
  | _ => .unknown

def encodeReq : Req → Json
  | .forward k c ct al sh me => Json.msg "keys.forward"
      [("key", some (.str k)), ("code", some (.str c)), ("ctrl", some (.bool ct)),
       ("alt", some (.bool al)), ("shift", some (.bool sh)), ("meta", some (.bool me))]
  | .registerAction id aid label dk => Json.msg "keys.registerAction"
      [("id", some (.str id)),
       ("action", some (Json.mkObj [("id", some (.str aid)), ("label", some (.str label)),
                                    ("defaultKey", dk.map .str)]))]
  | .unregisterAction aid => Json.msg "keys.unregisterAction" [("actionId", some (.str aid))]

def actionJson (aid : String) : Json := Json.msg "keys.action" [("actionId", some (.str aid))]

/-- `keys.bindings`, oldest registration first (the runtime keeps newest first). -/
def bindingsJson (l : List (String × Combo)) : Json :=
  Json.msg "keys.bindings"
    [("bindings", some (.arr (l.reverse.map fun p => .obj [("actionId", .str p.1), ("key", .str (comboStr p.2))])))]

def encodeOut : KeysOut → Eff
  | .registerResult to id aid binding error =>
    .send to (Json.msg "keys.registerAction.result"
      [("id", some (.str id)), ("actionId", some (.str aid)),
       ("binding", binding.map (.str ∘ comboStr)), ("error", error.map .str)])
  | .bindings to l => .send to (bindingsJson l)

/-- The host's view of one endpoint's actions. -/
def hostBindings (s : KeysState) (p : PortId) : Eff :=
  .effect (.nap .keys "bindings" (.obj [("port", Json.nat p),
    ("actions", .arr ((s.bindings.filter (·.owner == p)).map fun b =>
      Json.mkObj [("actionId", some (.str b.actionId)), ("label", some (.str b.label)),
                  ("key", b.combo.map (.str ∘ comboStr))]))]))

def inputArgs (p : PortId) (k c : String) (ct al sh me : Bool) : Json :=
  .obj [("port", Json.nat p), ("key", .str k), ("code", .str c), ("ctrl", .bool ct),
        ("alt", .bool al), ("shift", .bool sh), ("meta", .bool me)]

/-! ### Component -/

/-- `keys.action` to the owner of every binding of `c` (at most one under `Inv`). -/
def fire (s : KeysState) (c : Combo) : List Eff :=
  (s.bindings.filter (·.combo == some c)).map fun b => .send b.owner (actionJson b.actionId)

def handle (_h : Host) (_w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .forward k c ct al sh me =>
    (s, .effect (.nap .keys "input" (inputArgs cx.port k c ct al sh me)) ::
        fire s.ks (forwardCombo k ct al sh me))
  | .registerAction id aid label dk =>
    match dk.map comboOf? with
    | some none => (s, [.send cx.port (registerError id aid "invalid action")])
    | dk' =>
      let (ks', outs) := register s.ks cx.port id aid label dk'.join
      (⟨ks'⟩, outs.map encodeOut ++ [hostBindings ks' cx.port])
  | .unregisterAction aid =>
    if s.ks.bindings.any (fun b => b.owner == cx.port && b.actionId == aid) then
      let (ks', outs) := unregister s.ks cx.port aid
      (⟨ks'⟩, outs.map encodeOut ++ [hostBindings ks' cx.port])
    else (s, [])

def onReply (_h : Host) (_w : World) (s : St) (_n : Nat) (_r : Reply) : St × List Eff := (s, [])

/-- A user rebind: move the action to `key` (or unbind it). Refused when the combo
is reserved or taken (`NapKeys.assign`). -/
def others (s : KeysState) (p : PortId) (aid : String) : List NapKeys.Binding :=
  s.bindings.filter fun b => !(b.owner == p && b.actionId == aid)

def rebind (s : KeysState) (p : PortId) (aid : String) (key : Option Combo) :
    Option KeysState :=
  match s.bindings.find? (fun b => b.owner == p && b.actionId == aid) with
  | none => none
  | some b =>
    match key with
    | none => some ⟨⟨p, aid, b.label, none⟩ :: others s p aid⟩
    | some c =>
      match assign ⟨others s p aid⟩ (some c) with
      | none => none
      | some c' => some ⟨⟨p, aid, b.label, some c'⟩ :: others s p aid⟩

def onEvent (_h : Host) (_w : World) (s : St) : HostEvent → St × List Eff
  | .nap .keys "combo" args =>
    match (args.getStr? "key").bind comboOf? with
    | some c => (s, fire s.ks c)
    | none => (s, [])
  | .nap .keys "trigger" args =>
    match (args.get? "port").bind Json.asNat?, args.getStr? "actionId" with
    | some p, some aid =>
      if s.ks.bindings.any (fun b => b.owner == p && b.actionId == aid) then
        (s, [.send p (actionJson aid)])
      else (s, [])
    | _, _ => (s, [])
  | .nap .keys "rebind" args =>
    let key : Option (Option Combo) :=
      match args.get? "key" with
      | some .null => some none
      | some (.str k) => (comboOf? k).map some
      | _ => none
    match (args.get? "port").bind Json.asNat?, args.getStr? "actionId", key with
    | some p, some aid, some k =>
      match rebind s.ks p aid k with
      | some ks' => (⟨ks'⟩, [.send p (bindingsJson (bindingsOf ks' p)), hostBindings ks' p])
      | none => (s, [])
    | _, _, _ => (s, [])
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  let ks' : KeysState := ⟨s.ks.bindings.filter (·.owner != p)⟩
  (⟨ks'⟩, if s.ks.bindings.any (·.owner == p) then [hostBindings ks' p] else [])

def mentions (s : St) (p : PortId) : Bool := s.ks.bindings.any (·.owner == p)

/-! ### Properties: codec and per-endpoint state -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r with
  | forward => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]
  | registerAction id aid label dk =>
    cases dk <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
      Json.lookup, reqId?, optStr]
  | unregisterAction => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

theorem register_owners {s : KeysState} {p : PortId} {id aid label : String} {dk : Option Combo}
    {b : NapKeys.Binding} (hb : b ∈ (register s p id aid label dk).1.bindings) :
    b ∈ s.bindings ∨ b.owner = p := by
  unfold register at hb
  split at hb
  · exact .inl hb
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact .inr rfl
    · exact .inl hb

theorem rebind_owners {s : KeysState} {p : PortId} {aid : String} {k : Option Combo}
    {ks' : KeysState} (hr : rebind s p aid k = some ks') {b : NapKeys.Binding} (hb : b ∈ ks'.bindings) :
    b ∈ s.bindings ∨ b.owner = p := by
  unfold rebind at hr
  split at hr
  · simp at hr
  · split at hr
    · simp only [Option.some.injEq] at hr; subst hr
      rcases List.mem_cons.mp hb with rfl | hb
      · exact .inr rfl
      · exact .inl (List.mem_filter.mp hb).1
    · split at hr
      · simp at hr
      · simp only [Option.some.injEq] at hr; subst hr
        rcases List.mem_cons.mp hb with rfl | hb
        · exact .inr rfl
        · exact .inl (List.mem_filter.mp hb).1

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp only [drop, mentions, List.any_eq_true, List.mem_filter, beq_iff_eq] at h ⊢
  obtain ⟨b, ⟨hb, -⟩, hq⟩ := h
  exact ⟨b, hb, hq⟩

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  simp only [mentions, List.any_eq_true, beq_iff_eq] at hm ⊢
  obtain ⟨b, hb, rfl⟩ := hm
  have key : b ∈ s.ks.bindings ∨ b.owner = cx.port := by
    cases r with
    | forward => exact .inl hb
    | registerAction id aid label dk =>
      simp only [handle] at hb
      split at hb
      · exact .inl hb
      · exact register_owners hb
    | unregisterAction aid =>
      simp only [handle] at hb
      split at hb
      · simp only [unregister, List.mem_filter] at hb; exact .inl hb.1
      · exact .inl hb
  rcases key with hb | ho
  · exact .inl ⟨b, hb, rfl⟩
  · exact .inr ⟨cx, hcx, ho.symm⟩

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := .inl hm

/-- Host events never add bindings for a new endpoint: a rebind only changes an
existing binding of that endpoint. -/
theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  simp only [mentions, List.any_eq_true, beq_iff_eq] at hm ⊢
  obtain ⟨b, hb, rfl⟩ := hm
  -- the only state change is a successful rebind of an action `p` already owns
  have : ∀ p aid k ks', rebind s.ks p aid k = some ks' → b ∈ ks'.bindings →
      ∃ x ∈ s.ks.bindings, x.owner = b.owner := by
    intro p aid k ks' hr hb'
    rcases rebind_owners hr hb' with hb' | ho
    · exact ⟨b, hb', rfl⟩
    · unfold rebind at hr
      split at hr
      · simp at hr
      · rename_i x hx
        have hx' := List.find?_some hx
        simp only [Bool.and_eq_true, beq_iff_eq] at hx'
        exact ⟨x, List.mem_of_find?_eq_some hx, hx'.1.trans ho.symm⟩
  match e with
  | .userChanged _ => exact ⟨b, hb, rfl⟩
  | .themeChanged _ => exact ⟨b, hb, rfl⟩
  | .nap d ev args =>
    simp only [onEvent] at hb
    split at hb
    · split at hb <;> exact ⟨b, hb, rfl⟩
    · split at hb
      · split at hb <;> exact ⟨b, hb, rfl⟩
      · exact ⟨b, hb, rfl⟩
    · split at hb
      · split at hb
        · rename_i ks' hr; exact this _ _ _ _ hr hb
        · exact ⟨b, hb, rfl⟩
      · exact ⟨b, hb, rfl⟩
    · exact ⟨b, hb, rfl⟩

/-! ### Properties: the binding invariant -/

theorem rebind_inv {s : KeysState} (hi : NapKeys.Inv s) {p : PortId} {aid : String} {k : Option Combo}
    {ks' : KeysState} (hr : rebind s p aid k = some ks') : NapKeys.Inv ks' := by
  have hrest : NapKeys.Inv ⟨others s p aid⟩ :=
    ⟨fun b hb => hi.no_reserved b (List.mem_filter.mp hb).1,
     fun b₁ h₁ b₂ h₂ => hi.unique b₁ (List.mem_filter.mp h₁).1 b₂ (List.mem_filter.mp h₂).1⟩
  unfold rebind at hr
  split at hr
  · simp at hr
  · split at hr
    · simp only [Option.some.injEq] at hr; subst hr
      constructor
      · intro b hb c hc
        rcases List.mem_cons.mp hb with rfl | hb
        · simp at hc
        · exact hrest.no_reserved b hb c hc
      · intro b₁ h₁ b₂ h₂ c hc₁ hc₂
        rcases List.mem_cons.mp h₁ with rfl | h₁
        · simp at hc₁
        rcases List.mem_cons.mp h₂ with rfl | h₂
        · simp at hc₂
        exact hrest.unique b₁ h₁ b₂ h₂ c hc₁ hc₂
    · split at hr
      · simp at hr
      · rename_i c c' hc
        simp only [Option.some.injEq] at hr; subst hr
        have hs := assign_safe hc
        constructor
        · intro b hb c₀ hc₀
          rcases List.mem_cons.mp hb with rfl | hb
          · simp only [Option.some.injEq] at hc₀; subst hc₀; exact hs.1
          · exact hrest.no_reserved b hb c₀ hc₀
        · intro b₁ h₁ b₂ h₂ c₀ hc₁ hc₂
          rcases List.mem_cons.mp h₁ with rfl | h₁ <;> rcases List.mem_cons.mp h₂ with rfl | h₂
          · rfl
          · simp only [Option.some.injEq] at hc₁; subst hc₁; exact absurd hc₂ (hs.2 b₂ h₂)
          · simp only [Option.some.injEq] at hc₂; subst hc₂; exact absurd hc₁ (hs.2 b₁ h₁)
          · exact hrest.unique b₁ h₁ b₂ h₂ c₀ hc₁ hc₂

/-- `NapKeys.Inv` (no reserved combo bound, no combo bound twice) is preserved by
every request. -/
theorem handle_inv (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (hi : NapKeys.Inv s.ks) :
    NapKeys.Inv (handle h w cx s r).1.ks := by
  cases r with
  | forward => exact hi
  | registerAction id aid label dk =>
    simp only [handle]
    split
    · exact hi
    · exact NapKeys.Inv.register hi _ _ _ _ _
  | unregisterAction aid =>
    simp only [handle]
    split
    · exact NapKeys.Inv.unregister hi _ _
    · exact hi

theorem onEvent_inv (h : Host) (w : World) (s : St) (e : HostEvent) (hi : NapKeys.Inv s.ks) :
    NapKeys.Inv (onEvent h w s e).1.ks := by
  match e with
  | .userChanged _ => exact hi
  | .themeChanged _ => exact hi
  | .nap d ev args =>
    simp only [onEvent]
    split
    · split <;> exact hi
    · split
      · split <;> exact hi
      · exact hi
    · split
      · split
        · rename_i ks' hr; exact rebind_inv hi hr
        · exact hi
      · exact hi
    · exact hi

theorem drop_inv (s : St) (p : PortId) (hi : NapKeys.Inv s.ks) : NapKeys.Inv (drop s p).1.ks :=
  ⟨fun b hb => hi.no_reserved b (List.mem_filter.mp hb).1,
   fun b₁ h₁ b₂ h₂ => hi.unique b₁ (List.mem_filter.mp h₁).1 b₂ (List.mem_filter.mp h₂).1⟩

/-- No `keys.bindings` list the runtime can push contains a reserved combo, so a
napplet's suppress list never swallows Tab, Shift+Tab, Escape or browser
shortcuts (`NapKeys.suppress_list_safe`). Every push is `bindingsOf` of the new state. -/
theorem bindings_never_reserved (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req)
    (hi : NapKeys.Inv s.ks) (p : PortId) :
    ∀ x ∈ bindingsOf (handle h w cx s r).1.ks p, x.2 ∉ reserved :=
  suppress_list_safe (handle_inv h w cx s r hi) p

/-! ### Properties: routing -/

theorem fire_owner {s : KeysState} {c : Combo} {p : PortId} {m : Json} (hm : Eff.send p m ∈ fire s c) :
    ∃ b ∈ s.bindings, b.owner = p ∧ b.combo = some c ∧ m = actionJson b.actionId := by
  simp only [fire, List.mem_map, List.mem_filter, beq_iff_eq, Eff.send.injEq] at hm
  obtain ⟨b, ⟨hb, hc⟩, ho, hm⟩ := hm
  exact ⟨b, hb, ho, hc, hm.symm⟩

/-- A forwarded keystroke reaches no napplet: the only messages a `keys.forward`
produces are `keys.action` to the owner of the binding for that combo. -/
theorem forward_only_actions (h : Host) (w : World) (cx : Ctx) (s : St) (k c : String)
    (ct al sh me : Bool) (p : PortId) (m : Json)
    (hm : Eff.send p m ∈ (handle h w cx s (.forward k c ct al sh me)).2) :
    ∃ b ∈ s.ks.bindings, b.owner = p ∧ b.combo = some (forwardCombo k ct al sh me) ∧
      m = actionJson b.actionId := by
  simp only [handle, List.mem_cons, reduceCtorEq, false_or] at hm
  exact fire_owner hm

/-- `keys.action` from a host event goes only to an endpoint that registered that
action (and, for a combo, owns its binding). -/
theorem action_only_owner (h : Host) (w : World) (s : St) (e : HostEvent) (p : PortId) (m : Json)
    (hm : Eff.send p m ∈ (onEvent h w s e).2) (hn : ∀ l, m ≠ bindingsJson l) :
    ∃ b ∈ s.ks.bindings, b.owner = p ∧ m = actionJson b.actionId := by
  match e with
  | .userChanged _ => simp [onEvent] at hm
  | .themeChanged _ => simp [onEvent] at hm
  | .nap d ev args =>
    simp only [onEvent] at hm
    split at hm
    · split at hm
      · obtain ⟨b, hb, ho, -, hm⟩ := fire_owner hm; exact ⟨b, hb, ho, hm⟩
      · simp at hm
    · split at hm
      · split at hm
        · rename_i hany
          simp only [List.mem_singleton, Eff.send.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hany
          obtain ⟨b, hb, ho, ha⟩ := hany
          exact ⟨b, hb, ho, ha ▸ rfl⟩
        · simp at hm
      · simp at hm
    · split at hm
      · split at hm
        · simp only [List.mem_cons, Eff.send.injEq, hostBindings, reduceCtorEq, List.not_mem_nil,
            or_false] at hm
          exact absurd hm.2 (hn _)
        · simp at hm
      · simp at hm
    · simp at hm

/-- Results and pushes for a request go only to the requester; host input goes
only to the host. -/
theorem register_replies_to_requester (h : Host) (w : World) (cx : Ctx) (s : St)
    (id aid label : String) (dk : Option String) (p : PortId) (m : Json)
    (hm : Eff.send p m ∈ (handle h w cx s (.registerAction id aid label dk)).2) : p = cx.port := by
  simp only [handle] at hm
  split at hm
  · simp only [List.mem_singleton, Eff.send.injEq] at hm; exact hm.1
  · rename_i dk' _
    simp only [List.mem_append, List.mem_map, hostBindings, List.mem_singleton, reduceCtorEq,
      or_false] at hm
    obtain ⟨o, ho, he⟩ := hm
    unfold register at ho
    split at ho
    · simp only [List.mem_singleton] at ho; subst ho; simp [encodeOut] at he; exact he.1.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> simp [encodeOut, bindingsJson] at he <;> exact he.1.symm

/-! ### Vectors (upstream examples) -/

def sampleCtx : Ctx :=
  { port := 7, window := 1, identity := { dTag := some "app", artifactHash := "h" },
    exposed := [.keys], inst := 0 }

def sampleWorld : World := { now := 0, live := [sampleCtx], user := "" }

def sampleHost : Host :=
  { crypto := { sha256 := fun _ => "", verifySig := fun _ => false }, verifyEvent := fun _ => false,
    sniff := fun _ => "application/octet-stream", rasterize := fun _ => none,
    looksCiphertext := fun _ => false, encryptedWith := fun _ => none, transform := id }

def sentJson : List Eff → List Json
  | [] => []
  | .send _ m :: es => m :: sentJson es
  | _ :: es => sentJson es

def step (s : St) (j : Json) : St × List Json :=
  match decode j with
  | .ok r => let (s', es) := handle sampleHost sampleWorld sampleCtx s r; (s', sentJson es)
  | .reject rs => (s, rs)
  | .unknown => (s, [])

def regReq : Json := Json.parse! "{ \"type\": \"keys.registerAction\", \"id\": \"r1\", \"action\": { \"id\": \"editor.save\", \"label\": \"Save\", \"defaultKey\": \"Ctrl+S\" } }"
def regRes : Json := Json.parse! "{ \"type\": \"keys.registerAction.result\", \"id\": \"r1\", \"actionId\": \"editor.save\", \"binding\": \"Ctrl+S\" }"
def undoReq : Json := Json.parse! "{ \"type\": \"keys.registerAction\", \"id\": \"r2\", \"action\": { \"id\": \"editor.undo\", \"label\": \"Undo\", \"defaultKey\": \"Ctrl+Z\" } }"
def bindingsPush : Json := Json.parse! "{ \"type\": \"keys.bindings\", \"bindings\": [
     { \"actionId\": \"editor.save\", \"key\": \"Ctrl+S\" },
     { \"actionId\": \"editor.undo\", \"key\": \"Ctrl+Z\" }
   ]}"
def fwdReq : Json := Json.parse! "{ \"type\": \"keys.forward\", \"key\": \"j\", \"code\": \"KeyJ\", \"ctrl\": false, \"alt\": false, \"shift\": false, \"meta\": false }"
def unregReq : Json := Json.parse! "{ \"type\": \"keys.unregisterAction\", \"actionId\": \"editor.save\" }"
def unregPush : Json := Json.parse! "{ \"type\": \"keys.bindings\", \"bindings\": [
     { \"actionId\": \"editor.undo\", \"key\": \"Ctrl+Z\" }
   ]}"
def actionPush : Json := Json.parse! "{ \"type\": \"keys.action\", \"actionId\": \"editor.save\" }"
def dupRes : Json := Json.parse! "{ \"type\": \"keys.registerAction.result\", \"id\": \"r1\", \"actionId\": \"editor.save\", \"error\": \"duplicate action ID\" }"

def s1 : St := (step St.init regReq).1
def s2 : St := (step s1 undoReq).1

#guard decode regReq matches .ok (.registerAction "r1" "editor.save" "Save" (some "Ctrl+S"))
#guard decode fwdReq matches .ok (.forward "j" "KeyJ" false false false false)
#guard decode unregReq matches .ok (.unregisterAction "editor.save")
#guard decode (Json.parse! "{ \"type\": \"keys.onAction\", \"actionId\": \"x\" }") matches .unknown
#guard match (step St.init regReq).2 with
  | [m, _] => Json.same m regRes | _ => false
-- After registering save then undo, the save binding list is complete and canonical.
#guard match (step s1 undoReq).2 with
  | [_, m] => Json.same m bindingsPush | _ => false
#guard match (step s2 unregReq).2 with
  | [m] => Json.same m unregPush | _ => false
#guard (step s2 fwdReq).2 == []
#guard match (handle sampleHost sampleWorld sampleCtx s2 (.forward "s" "KeyS" true false false false)).2 with
  | [.effect (.nap .keys "input" _), .send 7 m] => Json.same m actionPush | _ => false
#guard match (onEvent sampleHost sampleWorld s2 (.nap .keys "combo" (.obj [("key", .str "Ctrl+S")]))).2 with
  | [.send 7 m] => Json.same m actionPush | _ => false
#guard match (step s1 regReq).2 with
  | [m] => Json.same m dupRes | _ => false
-- Reserved and malformed hints.
#guard match (step St.init (Json.parse! "{ \"type\": \"keys.registerAction\", \"id\": \"r3\", \"action\": { \"id\": \"a\", \"label\": \"A\", \"defaultKey\": \"Escape\" } }")).2 with
  | [m, _] => Json.same m (Json.parse! "{ \"type\": \"keys.registerAction.result\", \"id\": \"r3\", \"actionId\": \"a\" }") | _ => false
#guard match (step St.init (Json.parse! "{ \"type\": \"keys.registerAction\", \"id\": \"r4\", \"action\": { \"id\": \"a\", \"label\": \"A\", \"defaultKey\": \"Ctrl+Ctrl\" } }")).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"keys.registerAction.result\", \"id\": \"r4\", \"actionId\": \"a\", \"error\": \"invalid action\" }") | _ => false
#guard (comboOf? "Shift+Ctrl+p").map comboStr == some "Ctrl+Shift+P"
#guard (comboOf? "Ctrl++").map comboStr == some "Ctrl++"
#guard (comboOf? "Ctrl+w") ∈ [some ⟨false, true, false, false, "W"⟩]

end Napplet.Run.Keys
