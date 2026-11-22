# NAP-KEYS conformance

Upstream: `napplet/naps` PR #9, branch `nub-keys`, `naps/NAP-KEYS.md` at
`8869a4cf77b023f4b049f47c546910a0280dc1a6`.

Lean: `Napplet/Run/Keys.lean` (component), `Napplet/Nap/Keys.lean` (pure model, including
the napplet shim's `route`), `Napplet/Host.lean` §KEYS (lines 399-423). "README" means
`lean/README.md` (decisions 20-21 and the KEYS paragraph).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | `Action` `id`, `label` required, `defaultKey?` | REQUIRED | OK | `decode` :127-142 (missing or ill-typed gives `"invalid action"`) |
| 2 | `RegisterResult.actionId` required, `binding?` | REQUIRED | OK | `encodeOut` :166, `registerError` :123 (always carries `actionId`, `""` if unusable) |
| 3 | "`defaultKey` is a hint only; the shell decides" / "MAY defer binding" | MAY | OK | `NapKeys.assign` (`Nap/Keys.lean:128`); README decision 21 |
| 4 | `unregisterAction`: "The shell removes any binding for it and updates the napplet's suppress list" | (normative) | OK | `handle .unregisterAction` :200 → `NapKeys.unregister` (pushes `keys.bindings`); unknown action: nothing (README KEYS paragraph) |
| 5 | `keys.forward` fire-and-forget; `keys.unregisterAction` fire-and-forget | — | OK | `decode` :129-146 |
| 6 | `keys.bindings` "Contains the complete binding list — not a diff" | (normative) | OK | `bindingsOf` (`Nap/Keys.lean:124`); theorem `bindings_push_complete` |
| 7 | "Shells MUST normalize combos to alphabetical modifier order: `Alt+Ctrl+Shift+Meta+Key`" | MUST | OK / DECISION | `NapKeys.render` (`Nap/Keys.lean:43`), `comboStr` :107; theorems `parse_render`, `normalize_idem`, `normalize_order_free`. "Alphabetical" vs the stated order: README decision 20 |
| 8 | "Napplets SHOULD use this order in `defaultKey` hints" | SHOULD | NAPPLET | Shell accepts any order (`NapKeys.parse`) |
| 9 | Key matching uses `key` (shell decides which field) | — | OK | `forwardCombo` :110 uses `key`; single-character case folding (`normKey` :97) is a README KEYS decision |
| 10 | Smart forwarding steps 1-6 (text input, bare modifier, IME, suppress list, forward) | (shim) | NAPPLET | Modelled as `NapKeys.route` (`Nap/Keys.lean:240`); theorem `text_input_never_forwarded`. Not wired into `Binding.lean` |
| 11 | "The following keys MUST NOT be suppressed by smart forwarding" (Tab, Shift+Tab, Escape, browser-reserved) | MUST | NAPPLET | `NapKeys.route` checks `reserved` before the suppress list; theorem `reserved_never_suppressed` (`Nap/Keys.lean:252`). Shell side: `bindings_never_reserved` :449 (no reserved combo is ever pushed) |
| 12 | "Shells MUST NOT bind actions to reserved keys" (Tab, Shift+Tab, Escape, "browser-reserved shortcuts (e.g., Ctrl+W, Ctrl+T, Ctrl+L)") | MUST | RESOLVED (was MISMATCH) (partial) | `NapKeys.reserved` (`Nap/Keys.lean:94`) is a fixed list: Tab, Shift+Tab, Escape, Ctrl+W/T/L. `Inv.no_reserved`, `handle_inv` :408, `onEvent_inv` :423 and `rebind_inv` :368 prove that list is never bound. Other browser-reserved shortcuts (for example Meta+W/T/L on macOS, Ctrl+N, Ctrl+Shift+N/T, Ctrl+Q) can be bound from `defaultKey` or a host rebind. See the fix below |
| 13 | "Napplets MUST NOT use reserved keys in `defaultKey` hints" | MUST | NAPPLET | The shell refuses such hints (`assign`), and the action stays unbound (vector :584) |
| 14 | `keys.registerAction.result` on error: "`binding` is undefined" | (normative) | OK | `registerError` :123 has no `binding`; duplicate path `register` (`Nap/Keys.lean:136`) gives `binding = none` |
| 15 | Common errors `"duplicate action ID"`, `"invalid action"` | — | OK | theorem `register_duplicate_rejected`; `handle` :196, `decode` :142. Duplicate (kehto replaces instead) is in the README KEYS paragraph |
| 16 | "MUST accept `keys.forward` and process the keystroke as if it occurred in the shell's own context" | MUST | OK + HOST | `handle .forward` :191 emits `Effect.nap .keys "input"` for every well-formed forward, whatever the bindings; Host.lean:404-408 |
| 17 | "MUST respond to `keys.registerAction` with a result carrying the same `id`" | MUST | OK | `handle .registerAction` :194; theorem `register_replies_to_requester` :507; malformed with `id` :142; without a string `id` dropped (README decision 31) |
| 18 | "MUST push `keys.bindings` whenever the binding set changes (initial load, user rebind, action register/unregister)" | MUST | OK | register (`Nap/Keys.lean:140`), unregister (`Nap/Keys.lean:146`), host `rebind` (`onEvent` :246). Bindings never change for another endpoint (`register_other_napplets_untouched`; `assign` never steals). Initial load: bindings are per endpoint and start empty, so there is nothing to push |
| 19 | "MAY assign a binding immediately using `defaultKey`, or MAY leave the action unbound" | MAY | OK | `assign`; README decision 21 |
| 20 | "MAY send `keys.action` to trigger a napplet's registered action from outside" | MAY | OK | `fire` :187 (host `combo` event, bound forwarded combo), host `trigger` :230; theorem `action_only_owner` :474. A bound forwarded combo also fires (README KEYS paragraph) |
| 21 | "MAY enforce ACL checks on `keys` capabilities" | MAY | OK | domain exposure in `Runtime` (only `keys`-exposed bound ports reach `handle`) |
| 22 | "MUST silently ignore `keys.forward` from napplets it has not mapped to an identity" | MUST | OK | `Runtime.message_unbound_silent` (`Runtime.lean:451`): a message on an unbound port gives `(s, [])` |
| 23 | "SHOULD NOT forward keystrokes to other napplets" | SHOULD | OK + HOST | theorem `forward_only_actions` :464 (a forward produces only `keys.action` to a binding owner, never the keystroke); Host.lean:406-407 ("MUST NOT deliver it to any napplet") |
| 24 | "Shells MAY cap the number of actions per napplet" | MAY | OPTIONAL | No cap. Not in README's optional list (README gap only) |
| 25 | "SHOULD display action labels in a shell-controlled UI" | SHOULD | HOST | `hostBindings` :174; Host.lean:409-413 |
| 26 | "the shell MUST NOT rely on the napplet to suppress correctly for security-critical bindings" | MUST | OK | `handle .forward` :191 processes every forward the same way and checks no napplet-side state; host processing is independent of the suppress list |
| 27 | "napplet ... SHOULD validate the `actionId` against its own registered actions" | SHOULD | NAPPLET | Not modelled in `Binding`; shell sends `keys.action` only for registered actions (`action_only_owner`) |
| 28 | Text inputs: forwarding suppressed to prevent credential leakage | (normative) | NAPPLET | `NapKeys.route`, theorem `text_input_never_forwarded` |

## MISMATCH items (all resolved; see README decisions 35–47 and Host.lean)

**K1. Browser-reserved shortcuts are a fixed three-combo list (#12).**
Upstream: "Shells MUST NOT bind actions to reserved keys (Tab, Shift+Tab, Escape,
browser-reserved shortcuts)". The browser-reserved set is open ("e.g., `Ctrl+W`, `Ctrl+T`,
`Ctrl+L`") and depends on the platform. `NapKeys.reserved` hard-codes only the three
examples, so `defaultKey: "Meta+W"`, `"Ctrl+N"` or `"Ctrl+Shift+T"` is bound
(`NapKeys.assign`), and so is the same combo in a host `rebind`. README decision 20 mentions
only the case-folding of Ctrl+W/T/L. It does not say the set is closed.

Minimal fix, either:
- **Behaviour.** Make the set shell policy. Add a `Cfg` to `Run/Keys.lean` with
  `browserReserved : List Combo`, defaulting to at least Ctrl+W/T/L/N/Q, Ctrl+Shift+N/T/W
  and the same with `Meta` for macOS. Thread it into `assign` and `route` as
  `reserved ++ cfg.browserReserved`, and generalise `Inv.no_reserved` and
  `reserved_never_suppressed` over the list. Document the host's duty to supply its
  platform's reserved combos in Host.lean §KEYS.
- **Documentation only.** Add a README decision: "KEYS: the browser-reserved set is
  exactly Ctrl+W, Ctrl+T, Ctrl+L, the upstream examples. Other shortcuts the browser
  intercepts can be bound, but never fire inside a napplet." This is weaker, because a
  binding the browser always swallows can never fire.
