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
  `defaultKey` when that combo is not reserved (`Cfg.reservedSet`: `NapKeys.reserved`
  plus the shell's `Cfg.browserReserved`) and not bound by anyone, else left
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

Reserved keys. Upstream reserves Tab, Shift+Tab, Escape and "browser-reserved
shortcuts", naming Ctrl+W/T/L only as examples. The browser-reserved set is shell
policy: `Cfg.browserReserved` (default `defaultBrowserReserved`, the Windows/Linux and
macOS browser shortcuts) adds to `NapKeys.reserved`. The component invariant `Inv`
(`handle_inv'`, `onEvent_inv'`, `drop_inv'`) says no combo of the full set is ever
bound, so none is pushed in `keys.bindings` (`bindings_never_reserved'`), none is
suppressed by a shim using that list (`reserved_never_suppressed'`), and none fires an
action (`fire_reserved`).

State: the bindings, owned by the registering endpoint (`mentions`), and the policy
`cfg` (`St.init cfg`). Teardown
removes every binding of the endpoint and tells the host.
-/

/-! ## Host operations

All host-facing arguments name the endpoint by `port` (the `PortId` of the bound
port, which the host learned from `Output.bound`).

The host supplies its platform's browser-reserved shortcuts as `Cfg.browserReserved`
(default `defaultBrowserReserved`, the union of Windows/Linux and macOS browser
shortcuts); together with Tab, Shift+Tab, Escape and Ctrl+W/T/L they are never bound,
pushed in `keys.bindings`, or fired, and host rebinds to them are refused.

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
  unparseable, reserved (`NapKeys.reserved` or `Cfg.browserReserved`), or bound by any
  action is refused (nothing changes);
  otherwise the binding changes and the owner gets the new `keys.bindings`.
-/

namespace Napplet.Run.Keys

open NapKeys

/-- One-character keys are matched case-insensitively (upper-cased). -/
def normKey (k : String) : String := if k.length = 1 then k.toUpper else k

/-- A combo with its key normalised as the runtime matches it (`normKey`). -/
def normCombo (c : Combo) : Combo := { c with key := normKey c.key }

/-- The default browser-reserved shortcuts: the union over the major desktop platforms
of the shortcuts browsers intercept before page script (or never deliver to it), with
`Ctrl` for Windows/Linux and `Meta` (Cmd) for macOS:
* close / new / new window / location bar / quit / reload: `Ctrl`/`Meta` + `W`, `T`, `N`,
  `L`, `Q`, `R`;
* tab switching: `Ctrl+Tab`, `Ctrl+Shift+Tab`, `Ctrl+PageUp`, `Ctrl+PageDown`, and
  `Meta+Tab` (macOS application switcher);
* reopen closed tab / private window / close window: `Ctrl`/`Meta` + `Shift` + `T`, `N`,
  `W`;
* reload: `F5`, `Ctrl+F5`, `Ctrl+Shift+R`, `Meta+Shift+R`;
* history: `Alt+ArrowLeft`, `Alt+ArrowRight`, `Meta+[`, `Meta+]`;
* window: `Alt+F4`, `Meta+H`, `Meta+M`, `F11`.
`NapKeys.reserved` (Tab, Shift+Tab, Escape, Ctrl+W/T/L) is always reserved as well. -/
def defaultBrowserReserved : List Combo :=
  (["W", "T", "N", "L", "Q", "R"].flatMap fun k =>
    [{ ctrl := true, key := k }, { metaKey := true, key := k }]) ++
  (["T", "N", "W", "R"].flatMap fun k =>
    [{ ctrl := true, shift := true, key := k }, { shift := true, metaKey := true, key := k }]) ++
  [{ ctrl := true, key := "Tab" }, { ctrl := true, shift := true, key := "Tab" },
   { ctrl := true, key := "PageUp" }, { ctrl := true, key := "PageDown" },
   { metaKey := true, key := "Tab" },
   { key := "F5" }, { ctrl := true, key := "F5" }, { key := "F11" },
   { alt := true, key := "ArrowLeft" }, { alt := true, key := "ArrowRight" },
   { metaKey := true, key := "[" }, { metaKey := true, key := "]" },
   { alt := true, key := "F4" }, { metaKey := true, key := "H" }, { metaKey := true, key := "M" }]

/-- Shell keyboard policy. -/
structure Cfg where
  /-- Browser-reserved shortcuts of the shell's platform, in addition to
  `NapKeys.reserved`. Never bound (from `defaultKey` or a rebind) and never fired.
  Keys are compared after `normKey`, so `Ctrl+w` and `Ctrl+W` are the same entry. -/
  browserReserved : List Combo := defaultBrowserReserved

/-- The extra reserved combos, normalised as the runtime matches combos. -/
def Cfg.extra (cfg : Cfg) : List Combo := cfg.browserReserved.map normCombo

/-- Every combo the component treats as reserved. -/
def Cfg.reservedSet (cfg : Cfg) : List Combo := reserved ++ cfg.extra

structure St where
  ks : KeysState
  cfg : Cfg := {}

def St.init (cfg : Cfg := {}) : St := ⟨⟨[]⟩, cfg⟩

inductive Req where
  | forward (key code : String) (ctrl alt shift metaKey : Bool)
  | registerAction (id actionId label : String) (defaultKey : Option String)
  | unregisterAction (actionId : String)
  deriving DecidableEq, Repr

/-! ### Combo strings -/

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

/-- A `defaultKey` hint that names a browser-reserved combo is dropped before
`NapKeys.register` (which already refuses `NapKeys.reserved`). -/
def screen (cfg : Cfg) : Option Combo → Option Combo
  | some c => if c ∈ cfg.extra then none else some c
  | none => none

def handle (_h : Host) (_w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .forward k c ct al sh me =>
    (s, .effect (.nap .keys "input" (inputArgs cx.port k c ct al sh me)) ::
        fire s.ks (forwardCombo k ct al sh me))
  | .registerAction id aid label dk =>
    match dk.map comboOf? with
    | some none => (s, [.send cx.port (registerError id aid "invalid action")])
    | dk' =>
      let (ks', outs) := register s.ks cx.port id aid label (screen s.cfg dk'.join)
      ({ s with ks := ks' }, outs.map encodeOut ++ [hostBindings ks' cx.port])
  | .unregisterAction aid =>
    if s.ks.bindings.any (fun b => b.owner == cx.port && b.actionId == aid) then
      let (ks', outs) := unregister s.ks cx.port aid
      ({ s with ks := ks' }, outs.map encodeOut ++ [hostBindings ks' cx.port])
    else (s, [])

def onReply (_h : Host) (_w : World) (s : St) (_n : Nat) (_r : Reply) : St × List Eff := (s, [])

/-- A user rebind: move the action to `key` (or unbind it). Refused when the combo
is reserved (`NapKeys.reserved` or `cfg.browserReserved`) or taken (`NapKeys.assign`). -/
def others (s : KeysState) (p : PortId) (aid : String) : List NapKeys.Binding :=
  s.bindings.filter fun b => !(b.owner == p && b.actionId == aid)

def rebind (cfg : Cfg) (s : KeysState) (p : PortId) (aid : String) (key : Option Combo) :
    Option KeysState :=
  match s.bindings.find? (fun b => b.owner == p && b.actionId == aid) with
  | none => none
  | some b =>
    match key with
    | none => some ⟨⟨p, aid, b.label, none⟩ :: others s p aid⟩
    | some c =>
      match assign ⟨others s p aid⟩ (screen cfg (some c)) with
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
      match rebind s.cfg s.ks p aid k with
      | some ks' => ({ s with ks := ks' }, [.send p (bindingsJson (bindingsOf ks' p)), hostBindings ks' p])
      | none => (s, [])
    | _, _, _ => (s, [])
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  let ks' : KeysState := ⟨s.ks.bindings.filter (·.owner != p)⟩
  ({ s with ks := ks' }, if s.ks.bindings.any (·.owner == p) then [hostBindings ks' p] else [])

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

theorem rebind_owners {cfg : Cfg} {s : KeysState} {p : PortId} {aid : String} {k : Option Combo}
    {ks' : KeysState} (hr : rebind cfg s p aid k = some ks') {b : NapKeys.Binding} (hb : b ∈ ks'.bindings) :
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
  have : ∀ p aid k ks', rebind s.cfg s.ks p aid k = some ks' → b ∈ ks'.bindings →
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

theorem rebind_inv {cfg : Cfg} {s : KeysState} (hi : NapKeys.Inv s) {p : PortId} {aid : String} {k : Option Combo}
    {ks' : KeysState} (hr : rebind cfg s p aid k = some ks') : NapKeys.Inv ks' := by
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

/-! ### Properties: the extended reserved set

`NapKeys.Inv` covers only `NapKeys.reserved`. The component invariant adds the shell's
`cfg.browserReserved`, so the full reserved set is `cfg.reservedSet`. -/

/-- Component invariant: `NapKeys.Inv`, and no binding on a configured browser-reserved
combo. -/
structure Inv (s : St) : Prop where
  base : NapKeys.Inv s.ks
  no_extra : ∀ b ∈ s.ks.bindings, ∀ c, b.combo = some c → c ∉ s.cfg.extra

theorem Inv.init (cfg : Cfg) : Inv (St.init cfg) :=
  ⟨⟨fun _ hb => by simp [St.init] at hb, fun _ hb => by simp [St.init] at hb⟩,
   fun _ hb => by simp [St.init] at hb⟩

/-- Under `Inv`, no bound combo is in the full reserved set. -/
theorem Inv.no_reservedSet {s : St} (hi : Inv s) :
    ∀ b ∈ s.ks.bindings, ∀ c, b.combo = some c → c ∉ s.cfg.reservedSet := by
  intro b hb c hc hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hi.base.no_reserved b hb c hc hm
  · exact hi.no_extra b hb c hc hm

theorem assign_eq {s : KeysState} {dk : Option Combo} {c : Combo} (h : assign s dk = some c) :
    dk = some c := by
  unfold assign at h
  split at h
  · split at h
    · simp at h
    · exact h
  · simp at h

theorem screen_safe {cfg : Cfg} {dk : Option Combo} {c : Combo} (h : screen cfg dk = some c) :
    c ∉ cfg.extra := by
  unfold screen at h
  split at h
  · split at h
    · simp at h
    · rename_i hc; cases h; exact hc
  · simp at h

theorem register_mem {s : KeysState} {p : PortId} {id aid label : String} {dk : Option Combo}
    {b : NapKeys.Binding} (hb : b ∈ (register s p id aid label dk).1.bindings) :
    b ∈ s.bindings ∨ b.combo = assign s dk := by
  unfold register at hb
  split at hb
  · exact .inl hb
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact .inr rfl
    · exact .inl hb

theorem rebind_mem {cfg : Cfg} {s : KeysState} {p : PortId} {aid : String} {k : Option Combo}
    {ks' : KeysState} (hr : rebind cfg s p aid k = some ks') {b : NapKeys.Binding}
    (hb : b ∈ ks'.bindings) : b ∈ s.bindings ∨ ∀ c, b.combo = some c → c ∉ cfg.extra := by
  unfold rebind at hr
  split at hr
  · simp at hr
  · split at hr
    · simp only [Option.some.injEq] at hr; subst hr
      rcases List.mem_cons.mp hb with rfl | hb
      · exact .inr fun c hc => by simp at hc
      · exact .inl (List.mem_filter.mp hb).1
    · split at hr
      · simp at hr
      · rename_i c c' hc
        simp only [Option.some.injEq] at hr; subst hr
        rcases List.mem_cons.mp hb with rfl | hb
        · refine .inr fun c₀ hc₀ => ?_
          simp only [Option.some.injEq] at hc₀; subst hc₀
          have := assign_eq hc
          exact screen_safe this
        · exact .inl (List.mem_filter.mp hb).1

theorem handle_cfg (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    (handle h w cx s r).1.cfg = s.cfg := by
  cases r with
  | forward => rfl
  | registerAction => simp only [handle]; split <;> rfl
  | unregisterAction => simp only [handle]; split <;> rfl

theorem onEvent_cfg (h : Host) (w : World) (s : St) (e : HostEvent) :
    (onEvent h w s e).1.cfg = s.cfg := by
  match e with
  | .userChanged _ => rfl
  | .themeChanged _ => rfl
  | .nap d ev args =>
    simp only [onEvent]
    split
    · split <;> rfl
    · split
      · split <;> rfl
      · rfl
    · split
      · split <;> rfl
      · rfl
    · rfl

/-- The component invariant is preserved by every request: neither `NapKeys.reserved`
nor a configured browser-reserved combo is ever bound, and no combo is bound twice. -/
theorem handle_inv' (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (hi : Inv s) :
    Inv (handle h w cx s r).1 := by
  refine ⟨handle_inv h w cx s r hi.base, ?_⟩
  rw [handle_cfg]
  intro b hb c hc
  cases r with
  | forward => exact hi.no_extra b hb c hc
  | registerAction id aid label dk =>
    simp only [handle] at hb
    split at hb
    · exact hi.no_extra b hb c hc
    · rcases register_mem hb with hb | hb
      · exact hi.no_extra b hb c hc
      · rw [hc] at hb; exact screen_safe (assign_eq hb.symm)
  | unregisterAction aid =>
    simp only [handle] at hb
    split at hb
    · simp only [unregister, List.mem_filter] at hb; exact hi.no_extra b hb.1 c hc
    · exact hi.no_extra b hb c hc

theorem onEvent_inv' (h : Host) (w : World) (s : St) (e : HostEvent) (hi : Inv s) :
    Inv (onEvent h w s e).1 := by
  refine ⟨onEvent_inv h w s e hi.base, ?_⟩
  rw [onEvent_cfg]
  intro b hb c hc
  match e with
  | .userChanged _ => exact hi.no_extra b hb c hc
  | .themeChanged _ => exact hi.no_extra b hb c hc
  | .nap d ev args =>
    simp only [onEvent] at hb
    split at hb
    · split at hb <;> exact hi.no_extra b hb c hc
    · split at hb
      · split at hb <;> exact hi.no_extra b hb c hc
      · exact hi.no_extra b hb c hc
    · split at hb
      · split at hb
        · rename_i ks' hr
          rcases rebind_mem hr hb with hb | hs
          · exact hi.no_extra b hb c hc
          · exact hs c hc
        · exact hi.no_extra b hb c hc
      · exact hi.no_extra b hb c hc
    · exact hi.no_extra b hb c hc

theorem drop_inv' (s : St) (p : PortId) (hi : Inv s) : Inv (drop s p).1 :=
  ⟨drop_inv s p hi.base, fun b hb => hi.no_extra b (List.mem_filter.mp hb).1⟩

/-- No `keys.bindings` list the runtime can push contains a combo of the full reserved
set (`NapKeys.reserved` plus `cfg.browserReserved`). -/
theorem bindings_never_reserved' (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req)
    (hi : Inv s) (p : PortId) :
    ∀ x ∈ bindingsOf (handle h w cx s r).1.ks p, x.2 ∉ s.cfg.reservedSet := by
  intro x hx
  have hi' := handle_inv' h w cx s r hi
  rw [← handle_cfg h w cx s r]
  simp only [bindingsOf, List.mem_filterMap] at hx
  obtain ⟨b, hb, hm⟩ := hx
  split at hm
  · simp only [Option.map_eq_some_iff] at hm
    obtain ⟨c, hc, rfl⟩ := hm
    exact hi'.no_reservedSet b hb c hc
  · simp at hm

/-- Smart forwarding with the suppress list the shell pushed (`bindingsOf`) never
swallows a combo of the full reserved set: `NapKeys.route` only suppresses combos in the
list, and under `Inv` the list holds no reserved combo. -/
theorem reserved_never_suppressed' {s : St} (hi : Inv s) (p : PortId) (ev : KeyEvent)
    (hr : ev.combo ∈ s.cfg.reservedSet) :
    route ((bindingsOf s.ks p).map Prod.snd) ev ≠ .localAction := by
  have hns : ev.combo ∉ (bindingsOf s.ks p).map Prod.snd := by
    intro hm
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
    simp only [bindingsOf, List.mem_filterMap] at hx
    obtain ⟨b, hb, hm⟩ := hx
    split at hm
    · simp only [Option.map_eq_some_iff] at hm
      obtain ⟨c, hc, rfl⟩ := hm
      simp only at he
      rw [← he] at hr
      exact hi.no_reservedSet b hb c hc hr
    · simp at hm
  unfold route
  split
  · simp
  · split
    · simp
    · simp

/-- Under `Inv`, a reserved combo (pressed in the shell or forwarded) fires no action. -/
theorem fire_reserved {s : St} (hi : Inv s) {c : Combo} (hc : c ∈ s.cfg.reservedSet) :
    fire s.ks c = [] := by
  simp only [fire, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
  intro b hb hbc
  exact hi.no_reservedSet b hb c hbc hc

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
-- K1: browser-reserved shortcuts beyond Ctrl+W/T/L are never bound from a hint.
def hint (dk : String) : Json := Json.parse! ("{ \"type\": \"keys.registerAction\", \"id\": \"h\", \"action\": { \"id\": \"a\", \"label\": \"A\", \"defaultKey\": \"" ++ dk ++ "\" } }")
def unboundRes : Json := Json.parse! "{ \"type\": \"keys.registerAction.result\", \"id\": \"h\", \"actionId\": \"a\" }"
#guard ["Meta+W", "Ctrl+n", "Shift+Ctrl+T", "Meta+Shift+N", "Ctrl+Q", "F5", "Ctrl+Tab", "Alt+ArrowLeft"].all fun dk =>
  match (step St.init (hint dk)).2 with
  | [m, _] => Json.same m unboundRes | _ => false
-- With an empty platform list only `NapKeys.reserved` applies, so Meta+W is bound.
#guard match decode (hint "Meta+W") with
  | .ok r => match (handle sampleHost sampleWorld sampleCtx (St.init { browserReserved := [] }) r).2 with
    | .send _ m :: _ => m.getStr? "binding" == some "Meta+W" | _ => false
  | _ => false
-- A configured entry matches case-insensitively (`normCombo`).
#guard match decode (hint "Ctrl+K") with
  | .ok r => match (handle sampleHost sampleWorld sampleCtx (St.init { browserReserved := [{ ctrl := true, key := "k" }] }) r).2 with
    | .send _ m :: _ => Json.same m unboundRes | _ => false
  | _ => false
-- A host rebind to a browser-reserved combo is refused; to a free one it succeeds.
#guard (onEvent sampleHost sampleWorld s1 (.nap .keys "rebind" (.obj [("port", Json.nat 7), ("actionId", .str "editor.save"), ("key", .str "Meta+T")]))).2 == []
#guard ((onEvent sampleHost sampleWorld s1 (.nap .keys "rebind" (.obj [("port", Json.nat 7), ("actionId", .str "editor.save"), ("key", .str "Ctrl+K")]))).2).length == 2
-- The default list is reserved, so it never fires.
#guard (onEvent sampleHost sampleWorld s2 (.nap .keys "combo" (.obj [("key", .str "Ctrl+N")]))).2 == []
#guard (comboOf? "Shift+Ctrl+p").map comboStr == some "Ctrl+Shift+P"
#guard (comboOf? "Ctrl++").map comboStr == some "Ctrl++"
#guard (comboOf? "Ctrl+w") ∈ [some ⟨false, true, false, false, "W"⟩]

end Napplet.Run.Keys
