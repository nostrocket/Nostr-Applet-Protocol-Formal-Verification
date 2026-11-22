# NAP-IDENTITY conformance

Upstream: `napplet/naps` `naps/NAP-IDENTITY.md` at `377bf939c6c906817084b43dd21d424de646dbc2`; row 28
is PR #155 (`nap-identity` at `c13e8891ca6375bd0063b6dbd995ba42088df75e`).
Lean: `Napplet/Run/Identity.lean` (component), `Napplet/Nap/Identity.lean` (pure model),
`Napplet/Host.lean` §IDENTITY (`Call.nap .identity "query"`, `HostEvent.userChanged`).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | `RelayPermissions.read`, `.write`: required; `RelayMap` url → permissions | schema | HOST | Host answer `relays` (`Host.lean:259-264`); runtime checks it is an object (`Run/Identity.lean:113-128`) |
| 2 | `ProfileData` fields: all optional | schema | HOST | `Host.lean:263` ("kind 0 fields or `null`") |
| 3 | `ZapReceipt.eventId`, `.sender`, `.amount` required | schema | HOST | `Host.lean:265` (`zaps` from kind 9735 receipts); runtime checks only that it is an array |
| 4 | `Badge.id`, `.awardedBy` required | schema | HOST | `Host.lean:265` (`badges` from NIP-58) |
| 5 | "Napplets that need their bytes MUST use `resource.bytes` when the optional `resource` domain is exposed, and SHOULD use local placeholder artwork" | MUST / SHOULD | NAPPLET | — |
| 6 | `getPublicKey`: "Every shell that implements NAP-IDENTITY MUST support this method" | MUST | OK | `Run/Identity.lean:141` (answered from `World.user`) |
| 7 | `onChanged`: handler receives "a non-empty hex pubkey ... or `""`" | API | OK | `Run/Identity.lean:135,155-160` |
| 8 | `getProfile`: "Returns `null` if no profile is found" | API | OK | `Run/Identity.lean:106` default `null`; `typeOk` accepts `null`/object (110-116) |
| 9 | Other getters: data from kind 3 / NIP-51 / 9735 / 10000 / block list / NIP-58 | API | HOST | `Host.lean:259-266` |
| 10 | "All results include an optional `error` field for failure cases" | wire | OK | `Run/Identity.lean:122-130` `resultJson` passes host `error` |
| 11 | "`getPublicKey` ... MUST always succeed (no `error` field). It returns `pubkey: \"\"` when no shell-user identity is currently connected" | MUST | OK | theorem `getPublicKey_no_error` (`Run/Identity.lean:175`; `Nap/Identity.lean:75`); `World.user` is `""` when none (`Component.lean:71-72`) |
| 12 | "`getProfile` returns `profile: null` if no kind 0 is found -- this is not an error" | wire | OK | Row 8 |
| 13 | "Napplets SHOULD NOT poll `identity.getPublicKey`" | SHOULD NOT | NAPPLET | — |
| 14 | "Shells MUST use `identity.changed` to notify already-loaded napplets when the shell-user identity changes" | MUST | OK | `Run/Identity.lean:155-160`; theorem `change_notifies` (`Nap/Identity.lean:84`) |
| 15 | "When `error` is present, the primary result field contains a sensible default" | wire | OK | `Run/Identity.lean:103-128` `primary` defaults; vector at 241 |
| 16 | "`identity.getPublicKey.result` MUST NOT include an `error` field" | MUST NOT | OK | Row 11 |
| 17 | "The shell MUST respond to every `identity.*` request with the corresponding `*.result` message carrying the same `id`" | MUST | OK | `Run/Identity.lean:139-153`; theorems `reply_to_requester` (189), `resultJson_id` (180), `handle_same_id` (`Nap/Identity.lean:68`); non-`json` host reply → `"relay timeout"` (147); missing `listType` → `"invalid request"` (91); no string `id` → dropped (decision 31) |
| 18 | "The shell MUST return `pubkey` for `identity.getPublicKey` without error. If no user/signer is connected, `pubkey` MUST be the empty string" | MUST | OK | Row 11; `Host.lean:232-233` (`userChanged ""`) |
| 19 | "The shell MUST emit `identity.changed` to loaded napplets whenever the shell-user identity changes" | MUST | OK | `Run/Identity.lean:155-160` (to every live endpoint with `identity` exposed); theorems `change_notifies`, `change_only_exposed` (`Nap/Identity.lean:84,95`) |
| 20 | "The shell MUST emit `identity.changed` with `pubkey: \"\"` when the shell-user identity is cleared, the signer disconnects, or the user signs out" | MUST | OK + HOST | theorem `signout_notifies` (`Nap/Identity.lean:90`); host reports `userChanged ""` (`Host.lean:232-233`) |
| 21 | "The shell MAY emit an initial `identity.changed` after napplet load, but napplets MUST NOT depend on that initial push" | MAY / MUST NOT | OK / NAPPLET | Not emitted (allowed) |
| 22 | "The shell SHOULD resolve identity queries from its local cache"; "MAY fetch data from relays"; "MAY return stale data" | SHOULD / MAY | HOST | `Host.lean:261-262` ("from the shell's cache or relays") |
| 23 | "The shell MAY enforce ACL checks"; "MAY return empty results for queries it does not support"; MAY redact sensitive lists | MAY | HOST | `Host.lean:266-267` ("MAY redact or empty sensitive lists") |
| 24 | "The shell MUST NOT expose the user's private key or any signing capability through this interface" | MUST NOT | OK | `Nap/Identity.lean:19-28` (no such request); unknown types ignored (vector `Run/Identity.lean:253`) |
| 25 | "The shell MUST NOT provide encrypt or decrypt operations through this interface" | MUST NOT | OK | Row 24 |
| 26 | "`identity.changed` ... does not change or renegotiate the napplet's NIP-5D session identity" | normative prose | OK | `Run/Identity.lean:155-160` touches no binding |
| 27 | "Shells SHOULD consider whether to expose zap data to all napplets" | SHOULD | HOST | Row 23 |
| 28 | "`profile` is always present: a `ProfileData` object, or `null` when no profile is found or when `error` is set" | wire | OK | `Run/Identity.lean:122` `resultJson`; theorem `profile_present` (246); decision 52 |
