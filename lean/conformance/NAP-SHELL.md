# NAP-SHELL conformance

Upstream: `napplet/naps` `naps/NAP-SHELL.md` at `377bf939c6c906817084b43dd21d424de646dbc2`.
Lean: `Napplet/Run/Shell.lean` (component), `Napplet/Nap/Shell.lean` (pure model),
`Napplet/Runtime.lean` (routing), `Napplet/Binding.lean` (napplet side), `Napplet/Host.lean`
§SHELL (`Host.services`).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | `ShellCapabilities.domains`: required, "Bare NAP domains exposed to this napplet at snapshot time" | schema | OK | `Run/Shell.lean:42-48` `envJson` / `environment` (`cx.exposed`, `Domain.name`) |
| 2 | `ShellEnvironment.capabilities`, `.services`: required | schema | OK | `Run/Shell.lean:42-45` (both always present) |
| 3 | "The environment ... MUST NOT grant domains or override the projection's availability signal" | MUST NOT | OK | `shell.init` is output only; dispatch is decided by the binding's exposure (`Shell.lean:158`), never by `Run.Shell.St` |
| 4 | `supports(domain)`: "synchronous and local, and MUST work before `shell.init`"; unknown/unexposed → `false` | MUST | OK (napplet side) | `Nap/Shell.lean:24` `supports` (pure, no wire message) |
| 5 | `services`: "empty until `shell.init` is received" | binding | NAPPLET | Not modelled in `Binding.lean` |
| 6 | `ready()`: "Repeated calls MUST NOT send additional signals" | MUST NOT | NAPPLET | Not modelled in `Binding.lean` (no automatic `shell.ready` send is modelled) |
| 7 | `onReady`: "A handler registered after delivery MUST receive the retained environment" | MUST | RESOLVED (was MISMATCH) (napplet side)) | `Binding.lean:211,215`: `shell.init` is buffered, but `register` removes it from the buffer, so only the first late handler gets it; a second late `onReady` (and later `ready()`/`services` reads) get nothing (checked by `#eval`: `(1, 0)`) |
| 8 | "Neither readiness message carries an `id`; the environment is delivered once per napplet endpoint lifecycle" | wire | OK | `Run/Shell.lean:36-53`; theorem `init_exactly_once` (70); `drop` (59) clears on teardown |
| 9 | "`shell.ready` carries no identity or capability claims"; "`shell.init` reports only this napplet's environment" | wire | OK | `Run/Shell.lean:36-37` (extra members ignored); theorem `init_only_own_domains` (75) |
| 10 | "If the environment never arrives, a napplet MAY stop waiting" | MAY | NAPPLET | — |
| 11 | "it MUST NOT be interpreted as absence of other exposed domains or failure to establish napplet identity" | MUST NOT | NAPPLET | — |
| 12 | "A napplet MUST NOT gate unrelated domain calls on `ready()` or `onReady`" | MUST NOT | NAPPLET | — |
| 13 | "The runtime MAY omit `shell` while exposing other domains" | MAY | OK | `shell` is an ordinary domain in `exposedFor` (`Capability.lean:33`) |
| 14 | "The runtime MUST bind the endpoint to verified napplet identity before servicing any domain" | MUST | OK | `Runtime.lean:426-435`; theorems `message_unbound_silent` (451), `ctx_verified` (1240) |
| 15 | "It MUST NOT derive or alter identity from `shell.ready`" | MUST NOT | OK | `Run/Shell.lean:50-53` reads only `cx` (from `Ctx.ofBinding`, `Component.lean:48`) |
| 16 | "its binding MUST install the receiver before sending `shell.ready`" | MUST | NAPPLET | Not modelled in `Binding.lean` |
| 17 | "The runtime MUST send `shell.init` exactly once in response to the first `shell.ready` for that authenticated endpoint" | MUST | OK | `Run/Shell.lean:50-53`; theorems `init_exactly_once` (`Run/Shell.lean:70`, `Nap/Shell.lean:49`), `init_at_most_once` (`Nap/Shell.lean:53`); E2E `Test/E2E.lean:37-39` |
| 18 | "Duplicate `shell.ready` messages MUST NOT establish another session, change policy, or cause another `shell.init`" | MUST NOT | OK | `Run/Shell.lean:52` (state unchanged, no output); only `Run.Shell.St` changes (`Runtime.lean:234`, theorem `message_shellNap`) |
| 19 | "The environment MUST describe only domains and services exposed to that napplet. It MUST NOT expose another napplet's grants" | MUST | OK | theorems `init_only_own_domains` (`Run/Shell.lean:75`), `init_capabilities` (`Nap/Shell.lean:64`); services are `Host.services` (`Host.lean:147`) |
| 20 | "The binding MUST retain the environment for `ready`, `onReady`, and `services`" | MUST | RESOLVED (was MISMATCH) (napplet side)) | Same as row 7: `Binding.lean:215` `register` consumes the buffered `shell.init`; nothing retains it for later reads |
| 21 | "The runtime MUST NOT gate other domain calls or their availability on this readiness exchange" | MUST NOT | OK | `Runtime.lean:233-271` `napStep` routes per domain; no component reads `shellNap` |
| 22 | "The readiness signal is untrusted input, not authentication or authorization" | normative prose | OK | Row 15 |
| 23 | "Manifest capability declarations and environment snapshots are not grants" | normative prose | OK | `Capability.lean:46` `exposure_ignores_declarations` |
| 24 | "Withholding `shell.init` MUST NOT serve as a substitute for enforcing policy on another domain" | MUST NOT | OK | Enforcement is `Shell.step` dispatch (`Shell.lean:158`, theorem `dispatch_domain_exposed` 244) |
