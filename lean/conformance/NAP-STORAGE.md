# NAP-STORAGE conformance

Upstream: `napplet/naps` PR #3, `naps/NAP-STORAGE.md` at `4f4cf0ca7ecbd24c284a5d63bcd85e3de6af37ca`.
Lean: `Napplet/Run/Storage.lean` (component), `Napplet/Nap/Storage.lean` (pure model),
`Napplet/Component.lean` (`Ctx.storage`), `Napplet/Host.lean` (persistence, `inst`).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | `getItem`: "Returns `null` if the key does not exist" | API | OK | `Run/Storage.lean:95` (`v.elim .null .str`); `Nap/Storage.lean:99` |
| 2 | `setItem`: "Throws if the napplet exceeds its storage quota" | API | OK (shell side) | `Nap/Storage.lean:100-103` `"quota exceeded"`; the binding rejects on `error` (`Binding.lean:198`) |
| 3 | `removeItem`: "No-op if the key does not exist" | API | OK | `Nap/Storage.lean:104-105` |
| 4 | "Each request includes a correlation ID (`id`); the shell responds with a matching ID" | API | OK | theorem `handle_same_id` (`Nap/Storage.lean:108`), `handle_reply` (`Run/Storage.lean:127`) |
| 5 | "The runtime MUST derive scope from the authenticated endpoint's verified manifest and artifact" (named: publisher, kind, `d`; root: publisher, kind; snapshot: event id; plus `artifactHash`) | MUST | OK | `Basic.lean:120` `Identity.key`; `Nap/Storage.lean:48` `EndpointCtx.ofIdentity`; `Component.lean:62` `Ctx.storage`; identity verified: `Runtime.lean:1240` `ctx_verified` |
| 6 | "A bare `d` value MUST NOT identify a scope" | MUST NOT | OK | theorem `bare_d_not_scope` (`Nap/Storage.lean:207`) |
| 7 | "A napplet MUST NOT supply or override manifest or artifact identity fields in a request" | MUST NOT | OK | `Nap/Storage.lean:60-65` (no identity fields); decoder ignores extra members (`Run/Storage.lean:53-70`) |
| 8 | "Different publishers, manifest keys, and artifact hashes MUST remain isolated" | MUST | OK | theorems `handle_isolated` (`Nap/Storage.lean:113`), `bare_d_not_scope` (207), `artifact_hash_isolated` (212) |
| 9 | "Every request carries an optional `scope`: `\"shared\"` (default) or `\"instance\"`" | wire | OK | `Run/Storage.lean:46-51` `selOf?`; other values → `"invalid request"` |
| 10 | "Result messages carry no `scope`" | wire | OK | `Run/Storage.lean:89-97` `encodeResult` |
| 11 | "Any result message MAY include an `error` field ... When `error` is present, other result fields are undefined" | MAY | OK | `Run/Storage.lean:92` (error only) |
| 12 | Instance "Unique — instances MUST NOT share an instance namespace or read each other's instance-scoped keys" | MUST | OK (given host) + RESOLVED (was MISMATCH) (host doc, minor) | theorem `instances_isolated` (`Nap/Storage.lean:201`) for distinct `inst`. Distinctness comes from the host's `inst` (`Runtime.lean:140,419`), but `Host.lean:61-62` only calls it "the host's stable identifier for this napplet instance"; it does not require two coexisting instances of the same napplet to get different values |
| 13 | Instance "Stable — the same instance MUST resolve to the same namespace across reloads and sessions" | MUST | HOST | `Host.lean:61-62` (`inst` stable); `Component.lean:38-39` |
| 14 | "Instance storage lives as long as the instance; the shell MAY reclaim it on destroy" | MAY | OK | Not reclaimed (allowed); `Run/Storage.lean:109` `drop` keeps data |
| 15 | "The shell MUST scope storage by the verified manifest and artifact scope. Different napplet types and different versions ... MUST have isolated storage" | MUST | OK | Rows 5, 8 |
| 16 | "For `scope: \"instance\"` requests, the shell MUST further isolate the namespace per instance"; absent/`"shared"` "MUST address the napplet-wide namespace" | MUST | OK | `Nap/Storage.lean:56-58` `scopeFor`; theorems `shared_ne_instance` (198), `instances_isolated` (201) |
| 17 | "The shell MUST enforce a per-napplet storage quota. A recommended default is 512 KB measured in UTF-8 byte count" | MUST | OK | `Nap/Storage.lean:93,96,100-103`; theorem `quota_preserved` (126), `handle_quota` (`Run/Storage.lean:138`). Quota applies per scope (shared and each instance separately), which upstream leaves to the implementation |
| 18 | "The shell MUST persist storage so data survives page reloads" | MUST | OK + HOST | `Host.lean:46-49` (NAP-STORAGE values persistent); store keyed by scope, not port (`Run/Storage.lean:26-27`); `Persist.Persisted.storage` is durable; `Persist.persist_restore`, `Persist.Quota.restore`; the host snapshots `Persist.persist` after every step that changes it (`Host.lean` §Persistence) |
| 19 | "The shell MUST respond to every request with a result message carrying the same `id`" | MUST | OK + DECISION | Row 4; malformed with string `id` → `"invalid request"` (`Run/Storage.lean:57`); no string `id` → dropped (decision 31) |
| 20 | "The shell MUST return an `error` field in the result message for quota violations and invalid requests" | MUST | OK | `Nap/Storage.lean:103`; `Run/Storage.lean:57,62,68-69`; vector at 165-167 |
| 21 | "The shell MUST enforce isolation so a napplet cannot read or write another napplet's data. For `scope: \"instance\"` ... additionally ... between instances" | MUST | OK | Rows 8, 12, 16 |
| 22 | "The shell SHOULD NOT attempt to parse or execute stored content" | SHOULD NOT | OK | Values are opaque strings (`Nap/Storage.lean:85-90`) |
| 23 | "The shell MAY enforce ACL checks on `storage:read` and `storage:write`" | MAY | OK | Not done (allowed); domain exposure gates access |
| 24 | "Napplets that need confidential storage should encrypt values" | advisory | NAPPLET | — |
