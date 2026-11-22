# NAP-LINK conformance

Upstream: `napplet/naps` `naps/NAP-LINK.md` at `100e5c939ae6b1ea82cc58587c6da45a1cf8a760`.
Lean: `Napplet/Run/Link.lean` (component), `Napplet/Nap/Link.lean` (pure model),
`Napplet/Host.lean` §LINK (host contract).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | "Parsers that turn external URLs into clickable UI SHOULD route those clicks to `link.open`" | SHOULD | NAPPLET | Constrains napplet code; binding surface `BindingApi.lean:208` |
| 2 | Schema `LinkOpenOptions.label`: required no | schema | OK | `Run/Link.lean:177` `labelOf` (absent, non-object `options`, non-string `label` all give `none`) |
| 3 | Schema `LinkOpenResult.status` required, `"opened"`/`"denied"` | schema | OK | `Run/Link.lean:182` `resultJson` always sets `status` |
| 4 | `error`: "absent when `status` is `"opened"`" | schema | OK | `Run/Link.lean:218,239` (`resultJson id true none`); theorem `handle_effs`, `answer_effs` |
| 5 | "`url` MUST be an absolute URL" | MUST | NAPPLET (enforced by shell too) | Constrains caller; shell side is row 13 |
| 6 | "`label` ... is not trusted policy input" | normative prose | OK | `Run/Link.lean:464` theorem `label_irrelevant`; `Nap/Link.lean:127` |
| 7 | "`error`, when present on the wire, is passed through unchanged" | binding | NAPPLET | `BindingApi.lean:208` (binding returns the result payload) |
| 8 | Wire `link.open` fields `id`, `url`, `options?` | wire | OK | `Run/Link.lean:187` `decode`; theorem `decode_encodeReq` (`:261`) |
| 9 | Wire `link.open.result` fields `id`, `status`, `error?` | wire | OK | `Run/Link.lean:182` `resultJson`; upstream examples `:529`, `:535`; E2E `Test/E2E.lean:302-310` |
| 10 | "`id` correlates the request and result" | wire | OK | `Run/Link.lean:476` `handle_answers`, `:487` `onReply_answers`; `Pending.id` |
| 11 | "The shell chooses the final target: new tab, external browser, in-shell browser, native handler, or denial" | design note | HOST | `Host.lean:437` `Effect.nap .link "open"` (host's choice of context) |
| 12 | "The shell MUST NOT expose `window.opener` or equivalent authority back to the napplet" | MUST | HOST | `Host.lean:437-442` (opened context MUST NOT get `window.opener`); `Run/Link.lean:447` `opened_only_via_open_effect` (no other navigation path); `Nap/Link.lean:136` `opened_noopener` |
| 13 | Error codes "`invalid-url`, `unsupported-scheme`, `blocked-by-policy`, `user-denied`" (MAY include) | MAY | OK | `Run/Link.lean:139` `schemeCheck`, `:166` `verdict`, `:234` `answer`; mapping per README decision 25 |
| 14 | "The shell MUST validate `url` before opening it" | MUST | OK | `Run/Link.lean:139` `schemeCheck` (scheme syntax, http(s) host present, scheme allowlist), re-run on prompt answer `:236`; theorems `handle_opened_scheme_safe` `:384`, `onReply_opened_scheme_safe` `:395`. Note: no further syntax check (e.g. spaces in host); the host's `open` receives the string as-is |
| 15 | "The shell MUST reject relative URLs" | MUST | OK | `Nap/Link.lean:29` `schemeOf` (none without scheme); `Run/Link.lean:141`; `Nap/Link.lean:121` `relative_rejected`; vector `Run/Link.lean:539` |
| 16 | "MUST reject `javascript:`, `data:`, `blob:`, `file:`, and other local or code-bearing schemes" | MUST | OK | `Nap/Link.lean:44` `forbidden` (plus `vbscript`, `about`, `chrome`, `filesystem`), refused even if configured; default allowlist only `https`/`http` (`Run/Link.lean:87`); theorem `forbidden_never_opened` `Run/Link.lean:407` |
| 17 | "The shell MUST respond to every request with a result message carrying the same `id`" | MUST | OK | `Run/Link.lean:476` `handle_answers`, `:487` `onReply_answers`; non-decision replies answer `blocked-by-policy` (`:242`); host replies once to every call (`Host.lean:22-27`). Requests without a string `id` cannot be answered and are dropped (README decision 31); pending prompts of a torn-down endpoint are cancelled (`drop`, `:253`) |
| 18 | "The shell SHOULD open web links in a context outside the napplet sandbox" | SHOULD | HOST | `Host.lean:437` ("outside the napplet sandbox") |
| 19 | "The shell SHOULD use `noopener` or an equivalent opener-isolation mechanism" | SHOULD | HOST | `Host.lean:438-441` |
| 20 | "The shell MAY prompt the user before opening a link" | MAY | OK | `Run/Link.lean:219-224` (`Call.prompt .link "open"`), `Cfg.prompt` `:91` |
| 21 | "The shell MAY persist user choices per napplet, per hostname, or per URL" | MAY | OK | `Run/Link.lean:68` `Target`, `:227` `ruleOf`; rules keyed by manifest key (README LINK paragraph) |
| 22 | "The shell MAY support non-web schemes such as `nostr:` or `mailto:` by policy" | MAY | OK | `Cfg.allowedSchemes` `Run/Link.lean:87`; `hostOf` none is fine for non-http schemes (`:143`) |
| 23 | Prompt choices MAY include allow once / allow napplet / allow hostname / deny once / deny napplet | MAY | OK | `Run/Link.lean:227` `ruleOf` (`"once"`, `"napplet"`, `"host"` allow-only, `"url"`); `Host.lean:427-436` |
| 24 | "Shells SHOULD require a user gesture or prompt unless policy already allows the request" | SHOULD | OK | `Run/Link.lean:166` `verdict` (`allow` only under an allow rule, else prompt or `blocked-by-policy`); theorems `handle_opened_requires_rule` `:423`, `onReply_opened_requires_user` `:435` |
| 25 | "Prompts SHOULD show the napplet name, stable napplet identifiers, author when known, and destination URL or hostname" | SHOULD | HOST | `Host.lean:427-431`; `Run/Link.lean:207` `promptDetails` passes `url`, `host`, `napplet` (catalog id) |
| 26 | "Shells SHOULD rate-limit denied or repeated link requests to prevent prompt spam" | SHOULD | OK | `Run/Link.lean:220` `Cfg.maxPrompts` outstanding-prompt cap gives `blocked-by-policy`; persisted deny rules answer without prompting. No time-based rate limit (unquantified SHOULD) |
| 27 | "Shells SHOULD treat IDN, punycode, redirects, and lookalike hostnames as phishing risks in prompt UI" | SHOULD | HOST | `Host.lean:430-431` (IDN, punycode, lookalike). Redirects are not named in the contract (they happen after the host opens the URL) |
| 28 | "`label` is napplet-supplied text. Shells MUST NOT use it as proof of destination or intent" | MUST NOT | OK | `Run/Link.lean:464` `label_irrelevant` (state and every effect except prompt text identical); `Host.lean:431-432` (label marked as napplet-supplied) |
| 29 | "NAP-LINK does not grant direct network access" | normative prose | OK | Component emits no fetch/network call: only `.prompt` and `Effect.nap .link "open"` (`Run/Link.lean:339` `handle_effs`, `:447`) |

Summary: OK 20, HOST 6, NAPPLET 3 (rows 1, 5, 7), OPTIONAL 0, DECISION 0 separately
(decision 25 and the README LINK paragraph back rows 13, 17, 21), RESOLVED (was MISMATCH) 0.
