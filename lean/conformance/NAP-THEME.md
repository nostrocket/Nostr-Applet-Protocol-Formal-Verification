# NAP-THEME conformance

Upstream: `napplet/naps` `naps/NAP-THEME.md` at `377bf939c6c906817084b43dd21d424de646dbc2`.
Lean: `Napplet/Run/Theme.lean` (component), `Napplet/Nap/Theme.lean` (pure model),
`Napplet/Host.lean` §SHELL, THEME, STORAGE (`HostEvent.themeChanged`).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | `ThemeColors.background`, `.text`, `.primary`: required | schema | OK | `Nap/Theme.lean:18-21`; `Run/Theme.lean:64` `themeOf?` rejects a theme without all three |
| 2 | `ThemeFont.name`, `.url`: required | schema | OK | `Nap/Theme.lean:24-26`; `Run/Theme.lean:42` `fontOf?` |
| 3 | `ThemeBackground.url`, `.mode`, `.mime`: required | schema | OK | `Nap/Theme.lean:29-32`; `Run/Theme.lean:72-73` |
| 4 | `ThemeFonts.body`, `.title`; `Theme.fonts`, `.background`, `.title`: optional | schema | OK | `Nap/Theme.lean:35-40`; `Run/Theme.lean:50-60` `themeJson` omits absent fields; theorem `themeOf?_themeJson` (120) |
| 5 | "There is no wire subscribe or unsubscribe operation" | wire | OK | `Run/Theme.lean:79-84` decodes only `theme.get` |
| 6 | `theme.get` / `theme.get.result` use `id`; `theme.changed` has no `id` | wire | OK | `Run/Theme.lean:89-92` `encodeOut` |
| 7 | "Every napplet to which the runtime exposes `theme` automatically receives `theme.changed`"; `R`/`O` not required | wire | OK | `Run/Theme.lean:103-107`; theorem `broadcast_complete` (`Nap/Theme.lean:75`) |
| 8 | "Any result message MAY include an `error` field ... When `error` is present, other result fields are undefined" | MAY | OK | `Run/Theme.lean:91` (`error: "no active theme"`, no `theme`); theorem `get_theme_xor_error` (`Nap/Theme.lean:59`) |
| 9 | "The shell MUST respond to `theme.get` with a `theme.get.result` carrying the same `id`" | MUST | OK | `Run/Theme.lean:98-99`; theorem `get_same_id` (`Nap/Theme.lean:54`). A `theme.get` without a string `id` is dropped (decision 31) |
| 10 | "The shell MUST include `colors` with all three fields ... in every theme payload" | MUST | OK | theorem `payload_has_colors` (`Run/Theme.lean:147`) |
| 11 | "`fonts`, `background`, and `title` ... MAY be omitted" | MAY | OK | `Run/Theme.lean:50-60` |
| 12 | "The shell MUST broadcast `theme.changed` when the active theme changes to all napplets to which it exposes `theme`" | MUST | OK | `Run/Theme.lean:103-107`; theorem `broadcast_complete` (`Nap/Theme.lean:75`) |
| 13 | "It MUST NOT deliver these messages to napplets without that domain" | MUST NOT | OK | theorems `changed_only_exposed` (`Run/Theme.lean:127`), `broadcast_only_exposed` (`Nap/Theme.lean:67`) |
| 14 | "It MUST NOT infer grants from `R` or `O` tags" | MUST NOT | OK | Uses `Ctx.exposed` only (`Run/Theme.lean:106`); `Capability.lean:46` |
| 15 | "The shell MAY source the theme from any origin" | MAY | HOST | `HostEvent.themeChanged` (`Host.lean:234-235`, `Host.lean:253-255`) |
| 16 | Kind 16767: shells sourcing from it "SHOULD map event tags to the typed theme payload as follows" | SHOULD | HOST | Theme sourcing is the host's (`Host.lean:253-255`); not restated |
| 17 | "Shells MUST strip these prefixes [`url `, `mode `, `m `] when extracting values" | MUST (conditional) | RESOLVED (was MISMATCH) (host doc) | The host builds the `Theme` JSON, but `Host.lean:253-255` does not state the kind 16767 mapping or the prefix-stripping rule |
| 18 | "shells that source themes from other origins MUST still deliver a valid Theme payload" | MUST | OK | Invalid host themes are ignored (`Run/Theme.lean:105-107`), so only valid payloads are sent |
| 19 | "Napplets cannot modify the shell's active theme" | normative prose | OK | No request changes `St.current` (`Run/Theme.lean:98-99`) |
| 20 | "Shells SHOULD validate [font and background URLs] and MAY provide resources through their mediated resource policy" | SHOULD | OPTIONAL (not listed) | URLs passed through unvalidated (`Run/Theme.lean:42,72`); README's optional list does not mention it |
| 21 | "Napplets MUST NOT assume external URLs are directly loadable; they SHOULD fall back to colors and local fonts" | MUST NOT / SHOULD | NAPPLET | — |
| 22 | "A napplet cannot influence what theme other napplets receive" | normative prose | OK | Row 19 |
| 23 | "Napplets SHOULD validate hex color format" | SHOULD | NAPPLET | — |
| 24 | "The shell MAY enforce ACL checks before responding to `theme.get`" | MAY | OK | Not done (allowed); exposure gates the domain |
