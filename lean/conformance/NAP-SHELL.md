# NAP-SHELL conformance

Upstream: `napplet/naps` `naps/NAP-SHELL.md` at `377bf939c6c906817084b43dd21d424de646dbc2`; rows 25–40
are the additions of PR #142 (`nap-shell-compatibility` at `b9b0b7e38d99d9e3ad0b79e3de61b349156ee41f`).
Lean: `Napplet/Run/Shell.lean` (component), `Napplet/Nap/Shell.lean` (pure model),
`Napplet/Runtime.lean` (routing), `Napplet/Binding.lean` (napplet side), `Napplet/Host.lean`
§SHELL (`Host.services`).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | `ShellCapabilities.domains`: required, "Bare NAP domains exposed to this napplet at snapshot time" | schema | OK | `Run/Shell.lean:101-107` `envJson` / `environment` (`cx.exposed`, `Domain.name`) |
| 2 | `ShellEnvironment.capabilities`, `.services`: required | schema | OK | `Run/Shell.lean:101-104` (both always present) |
| 3 | "The environment ... MUST NOT grant domains or override the projection's availability signal" | MUST NOT | OK | `shell.init` is output only; dispatch is decided by the binding's exposure (`Shell.lean:158`), never by `Run.Shell.St` |
| 4 | `supports(domain)`: "synchronous and local, and MUST work before `shell.init`"; unknown/unexposed → `false` | MUST | OK (napplet side) | `Nap/Shell.lean:24` `supports` (pure, no wire message) |
| 5 | `services`: "empty until `shell.init` is received" | binding | NAPPLET | Not modelled in `Binding.lean` |
| 6 | `ready()`: "Repeated calls MUST NOT send additional signals" | MUST NOT | NAPPLET | Not modelled in `Binding.lean` (no automatic `shell.ready` send is modelled) |
| 7 | `onReady`: "A handler registered after delivery MUST receive the retained environment" | MUST | RESOLVED (was MISMATCH) (napplet side) | `Binding.lean:211,215`: `shell.init` is buffered, but `register` removes it from the buffer, so only the first late handler gets it; a second late `onReady` (and later `ready()`/`services` reads) get nothing (checked by `#eval`: `(1, 0)`) |
| 8 | "Neither readiness message carries an `id`; the environment is delivered once per napplet endpoint lifecycle" | wire | OK | `Run/Shell.lean:55-113`; theorem `init_exactly_once` (130); `drop` (119) clears on teardown |
| 9 | "`shell.ready` carries no identity or capability claims"; "`shell.init` reports only this napplet's environment" | wire | OK | `Run/Shell.lean:55-62` (extra members ignored); theorem `init_only_own_domains` (135) |
| 10 | "If the environment never arrives, a napplet MAY stop waiting" | MAY | NAPPLET | — |
| 11 | "it MUST NOT be interpreted as absence of other exposed domains or failure to establish napplet identity" | MUST NOT | NAPPLET | — |
| 12 | "A napplet MUST NOT gate unrelated domain calls on `ready()` or `onReady`" | MUST NOT | NAPPLET | — |
| 13 | "The runtime MAY omit `shell` while exposing other domains" | MAY | OK | `shell` is an ordinary domain in `exposedFor` (`Capability.lean:38`) |
| 14 | "The runtime MUST bind the endpoint to verified napplet identity before servicing any domain" | MUST | OK | `Runtime.lean:426-435`; theorems `message_unbound_silent` (451), `ctx_verified` (1240) |
| 15 | "It MUST NOT derive or alter identity from `shell.ready`" | MUST NOT | OK | `Run/Shell.lean:109-113` reads only `cx` (from `Ctx.ofBinding`, `Component.lean:48`) |
| 16 | "its binding MUST install the receiver before sending `shell.ready`" | MUST | NAPPLET | Not modelled in `Binding.lean` |
| 17 | "The runtime MUST send `shell.init` exactly once in response to the first `shell.ready` for that authenticated endpoint" | MUST | OK | `Run/Shell.lean:109-113`; theorems `init_exactly_once` (`Run/Shell.lean:130`, `Nap/Shell.lean:224`), `init_at_most_once` (`Nap/Shell.lean:228`); E2E `Test/E2E.lean:37-39` |
| 18 | "Duplicate `shell.ready` messages MUST NOT establish another session, change policy, or cause another `shell.init`" | MUST NOT | OK | `Run/Shell.lean:111` (state unchanged, no output); only `Run.Shell.St` changes (`Runtime.lean:234`, theorem `message_shellNap`) |
| 19 | "The environment MUST describe only domains and services exposed to that napplet. It MUST NOT expose another napplet's grants" | MUST | OK | theorems `init_only_own_domains` (`Run/Shell.lean:135`), `init_capabilities` (`Nap/Shell.lean:239`); services are `Host.services` (`Host.lean:147`) |
| 20 | "The binding MUST retain the environment for `ready`, `onReady`, and `services`" | MUST | RESOLVED (was MISMATCH) (napplet side) | Same as row 7: `Binding.lean:215` `register` consumes the buffered `shell.init`; nothing retains it for later reads |
| 21 | "The runtime MUST NOT gate other domain calls or their availability on this readiness exchange" | MUST NOT | OK | `Runtime.lean:233-271` `napStep` routes per domain; no component reads `shellNap` |
| 22 | "The readiness signal is untrusted input, not authentication or authorization" | normative prose | OK | Row 15 |
| 23 | "Manifest capability declarations and environment snapshots are not grants" | normative prose | OK | `Capability.lean:51` `exposure_ignores_declarations` |
| 24 | "Withholding `shell.init` MUST NOT serve as a substitute for enforcing policy on another domain" | MUST NOT | OK | Enforcement is `Shell.step` dispatch (`Shell.lean:158`, theorem `dispatch_domain_exposed` 244) |
| 25 | `domains()`: "a fresh, duplicate-free list of bare domains currently exposed to the calling napplet" | MUST | OK (napplet side) | `Nap/Shell.lean:60` `domains`; theorem `domains_nodup` (66) |
| 26 | `domains()`: "synchronous and local, MUST work before `shell.init`, and MUST agree with `supports(domain)`" | MUST | OK (napplet side) | theorem `domains_supports` (`Nap/Shell.lean:62`); no wire message (`BindingApi.lean` table) |
| 27 | `NappletManifest` is a signed NIP-5D manifest event; `ShellCompatibility` fields `status`, `missingRequired`, `missingOptional` all required | schema | OK | `Run/Shell.lean:87-103` `check`, `compatJson` (all three always present) |
| 28 | "The runtime MUST validate the manifest and its signature" | MUST | OK + HOST | `Run/Shell.lean:77` `target?`: `Host.verifyEvent` over the full event, then every NIP-5D manifest rule but the hash comparison (`Manifest.lean:408` `checkManifestEvent`) |
| 29 | "then assess its `R` and `O` domains using the same capability and policy rules used when loading that target, independently of the caller's exposed domains" | MUST | OK | `exposedFor` of the target identity under `Config.shell` (`Run/Shell.lean:87`); theorems `check_agrees_with_load` (219), `checkManifestEvent_agrees` (`Manifest.lean:417`), `assess_agrees_with_load` (`Nap/Shell.lean:169`), `check_caller_independent` (`Run/Shell.lean:182`) |
| 30 | "Availability that cannot be determined or disclosed is unknown" | normative | OK | `ShellConfig.undisclosed` (`Capability.lean:35`); `availability` (`Nap/Shell.lean:90`); decision 49 |
| 31 | "The result lists each known unavailable bare domain once in its corresponding list" | normative | OK | `knownMissing` (`Nap/Shell.lean:96`); theorems `mem_knownMissing` (108), `knownMissing_nodup` (112) |
| 32 | "`status` MUST be `incompatible` if any required domain is known unavailable; otherwise `compatible` if every required domain is known available, or `unknown`" | MUST | OK | theorems `assess_incompatible_iff` (`Nap/Shell.lean:116`), `assess_compatible_iff` (138) |
| 33 | "Missing optional domains do not affect `status`; no required domains means `compatible`" | normative | OK | theorems `assess_optional_irrelevant` (`Nap/Shell.lean:164`), `assess_no_required` (160) |
| 34 | "The check MUST work without `shell.init`" | MUST | OK | `Run/Shell.lean:109-113` (`check` never reads `sent`); theorem `check_caller_independent` (`Run/Shell.lean:182`) |
| 35 | "It MUST NOT fetch artifacts, install, launch, request consent, or grant capabilities" | MUST NOT | OK | theorem `check_one_reply` (`Run/Shell.lean:170`): one `send`, no call or effect, state unchanged |
| 36 | "The runtime MUST recheck requirements at load time; artifact verification and user consent remain separate" | MUST | OK | Load always runs `admit` (`Shell.lean:104`) with the hash check; `check` changes no state |
| 37 | "the runtime MUST reply to that endpoint with the same `id` and exactly one of `compatibility` or `error`" | MUST | OK | theorem `check_one_reply` (`Run/Shell.lean:170`); a request without a text `id` is dropped (decision 31) |
| 38 | "A missing, malformed, or invalidly signed manifest MUST return `error`: `\"invalid manifest\"`" | MUST | OK | theorem `check_invalid` (`Run/Shell.lean:190`); vectors at the end of `Run/Shell.lean` |
| 39 | "An unavailable operation, timeout, or error MUST NOT be interpreted as incompatibility" | MUST NOT | NAPPLET | — |
| 40 | "Compatibility checks MUST NOT reveal another napplet's existing grants or private state. Unavailable policy information MUST remain undisclosed" | MUST NOT | OK | Grants are never read (`check` reads only `ShellConfig` and the manifest); undisclosed domains are `unknown` and never listed (row 30) |
