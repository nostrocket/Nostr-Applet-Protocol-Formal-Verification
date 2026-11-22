# NAP-RESOURCE conformance

Upstream: `napplet/naps` PR #80, `naps/NAP-RESOURCE.md` at `ae5b9c64ab8a4d8909f288829a01e99d6bd713bc`.
Lean: `Napplet/Run/Resource.lean` (component), `Napplet/Nap/Resource.lean` (pure model),
`Napplet/Host.lean` §RESOURCE and `Call.fetch` (host contract), `Napplet/Binding.lean` (napplet shim).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | "This domain MUST NOT grant raw network access" | MUST | OK | The only network operation is `Call.fetch` of a policy-checked napplet URL (`launch` `Run/Resource.lean:672`); `data:` never reaches the host (`initSlot` `:709-712`) |
| 2 | "... or expose upstream `Content-Type`" | MUST | OK | `FetchOutcome.upstreamType` is never read (`Nap/Resource.lean:101-102`); theorem `bytes_mime_sniffed_not_svg` (`Nap/Resource.lean:271`) |
| 3 | "A projection MUST enforce direct-network denial before exposing this domain" | MUST | HOST | `Host.lean:57-58` (`sandbox="allow-scripts"`, NIP-5D CSP `meta` first in `head`) |
| 4 | `info()`: "Napplets MAY call it ... but MUST NOT be required to call it before `bytes` or `bytesMany`" | MUST | OK | No preflight state: `handle` `:723-733` |
| 5 | "Late terminal envelopes for cancelled IDs MUST be dropped" | MUST | OK | `handle .cancel` `:734-737`, `onReply` `:746`; theorem `cancel_drops_late` (`:1009`) |
| 6 | "Each URL MUST be processed as if it were an independent `bytes(url)` request" | MUST | OK | Per-slot `initSlot` `:704`, `itemOf` `:523`; theorems `jobItems_ok` (`:885`), `bytesMany_items` (`Nap/Resource.lean:305`). The quota is shared per envelope (row 54) |
| 7 | "One failed URL MUST NOT discard successful siblings" | MUST | OK | As row 6; `applyQuota` keeps errors in place (`:531`), `applyQuota_length` (`:875`) |
| 8 | "A napplet MUST NOT read another napplet's resource cache" | MUST | OK | The runtime keeps no cache (single-flight is optional, README l.249); jobs are keyed by port (`inUse` `:715`). The shim cache is per instance (`Binding.lean:104`) |
| 9 | "The runtime MUST derive scope from the authenticated endpoint's verified manifest and artifact" | MUST | OK | All state is keyed by the bound `Ctx.port` (`Job.port` `:563`); no payload field affects scope |
| 10 | "A bare `d` value MUST NOT identify a scope" | MUST | OK | Vacuous: no scope-keyed state |
| 11 | "A napplet MUST NOT supply or override manifest or artifact identity fields in a request" | MUST | OK | `decode` `:586-603` reads only `id`, `url`, `urls` |
| 12 | "Different publishers, manifest keys, and artifact hashes MUST remain isolated" | MUST | OK | Per-port jobs (stronger than per scope); no shared state |
| 13 | "Every wire `blob` field MUST use [canonical padded base64]" | MUST | OK | `Base64.encode` `:158` used by `itemJson` `:626`, `finishMsg` `:649`; theorems `decode?_encode` (`:323`), `encode_decode?` (`:329`) |
| 14 | "Receivers MUST reject non-canonical encodings" | MUST | OK | Runtime side: `data:` base64 via strict `Base64.dec` (`dataBytes?` `:429`), theorem `encode_decode?`. Shim side is NAPPLET |
| 15 | "Host byte objects and integer arrays MUST NOT appear in these wire fields" | MUST | OK | `blob` is always `.str` (`:626`, `:649`) |
| 16 | "Hash verification applies to fetched content before transformation" | rule | OK | `Nap/Resource.lean:170` (hash on fetched `b`, then `finish`) |
| 17 | "Resource byte limits and quotas apply to decoded bytes" | rule | OK | `fetchChecked` `Nap/Resource.lean:141`, `applyQuota` `:531` (byte lengths) |
| 18 | Web binding "MUST NOT encode the base64 characters themselves as the Blob contents" | MUST | NAPPLET | Web binding; not modelled in `Binding.lean` |
| 19 | "Every `resource.info`, `resource.bytes`, and `resource.bytesMany` request gets one terminal result or error envelope unless cancelled" | rule | DECISION | One envelope per job: `flush` `:694`, theorems `finishMsg_id` (`:942`), `onReply_sends` (`:996`). A duplicate in-flight `id` is ignored (`start` `:718`): README decision 13 |
| 20 | "`resource.info` is advisory and MUST NOT be a required preflight" | MUST | OK | As row 4 |
| 21 | "`bytesMany.result.items` MUST preserve input order and length" | MUST | OK | `finishMsg` `:645`; theorem `jobItems_length` (`:928`) |
| 22 | "`ok: true` items MUST include `blob` and `mime`" | MUST | OK | `itemJson` `:626` |
| 23 | "`ok: false` items MUST include `error` and MUST NOT include `blob`" | MUST | OK | `itemJson` `:628-629` |
| 24 | "`mime` MUST be runtime-classified by byte sniffing, never upstream header" | MUST | OK | `Nap/Resource.lean:126` `finish`; theorem `bytes_mime_sniffed_not_svg`; `Host.sniff` contract `Host.lean:129-132` |
| 25 | "Unsupported schemes still fail per request with `unsupported-scheme`" | rule | OK | `precheck` `:473-475` per slot |
| 26 | `data:` "MAY decode in the napplet shim" | MAY | OK | Decoded in the runtime instead (README "RESOURCE" l.157) |
| 27 | `data:` "MUST be size-limited, MIME-sniffed, rasterized when SVG, quota-checked, and otherwise policy-checked. No network access." | MUST | OK | `initSlot` `:709-712` builds a local outcome that goes through `NapResource.bytes` (`itemOf` `:526`) and `applyQuota`; never `Call.fetch` |
| 28 | `https:` "Full Default Resource Policy applies" | rule | OK | `itemOf` → `NapResource.bytes`; DNS/connect rules HOST (row 43) |
| 29 | `blossom:` "Runtime MUST verify SHA-256 before delivery" | MUST | OK | `Nap/Resource.lean:164-170`; theorems `blossom_hash_verified` (`Nap/Resource.lean:277`), `itemOf_blossom` (`:916`) |
| 30 | BUD-10 hints "are advisory and never bypass policy, size limits, or the hash check" | rule | OK | Size and hash are checked in the model whatever the host did; hint handling HOST `Host.lean:590-591` |
| 31 | `htree:`/`hashtree:` "verifies hashes and decryption before delivery, and MUST NOT leak keys" | MUST | HOST | `Host.lean:594-596`, `Run/Resource.lean:64-67` |
| 32 | `nostr:` "MUST NOT recursively follow URLs or `nostr:` references in the result" | MUST | HOST | `Host.lean:591-592`; the model also refuses `nsec` (`nostrOk` `:456`) |
| 33 | "Unknown schemes MUST return `unsupported-scheme`" | MUST | OK | theorem `unknown_scheme_unsupported` (`:936`) |
| 34 | "`http:` ... MUST NOT be enabled by default" | MUST | OK | `Policy.httpEnabled := false`; theorem `http_unsupported_by_default` (`:932`) |
| 35 | "A runtime offering Hashtree reads MUST accept these forms" (`hashtree:<nhash>`, bare `nhash`, `htree://<npub or 64-hex>/<tree>…`) | MUST | OK | `norm` `:467`, `hashtreeOk` `:432`, `htreeOk` `:444`, `htreeIdOk` `:440`. Note: hex is accepted in lowercase only (`hex64` `:393`) |
| 36 | "creation-only `#link-visible` MUST be rejected by this read API" | MUST | OK | `htreeFragOk` `:437`; vector `:1091` |
| 37 | "Immutable `nhash` input MUST validate its Bech32 checksum and HTS-01 TLV fields" | MUST | OK | Checksum: `hashtreeOk` (`Bech32.hrp?` `:370`). TLV fields: HOST `Host.lean:604-605` (`invalid-request`) |
| 38 | "Tree names and entry segments MUST follow upstream URL encoding: split segments before decoding" | MUST | OK | `htreeOk` `:451-453` (`splitOn '/'` then `escapesOk`) |
| 39 | "Query strings, malformed escapes, unknown fragments, and colon-separated mutable paths MUST return `invalid-request`" | MUST | OK | `htreeOk` `:449-450`, `precheck` `:479`; vectors `:1115-1118` |
| 40 | "Directories do not yield file bytes and MUST return `invalid-request`" | MUST | HOST | `Host.lean:604-605` |
| 41 | "`self` and petname aliases MAY be accepted only when runtime policy can resolve them unambiguously; otherwise return `invalid-request`" | MAY | OK | Not accepted: `htreeIdOk` `:440` (README "RESOURCE" l.160) |
| 42 | "Hashtree support MUST advertise both `htree` and `hashtree` in `info.schemes` when disclosed" | MUST | OK | `infoJson` `:620` |
| 43 | Private IP block (MUST): "Enforce after DNS resolution and before connection. Re-check every redirect. Block RFC1918, loopback, link-local, ULA, and `169.254.169.254`." | MUST | OK | Before connect: HOST `Host.lean:597-599`. The model re-checks every reported hop (`fetchChecked` `Nap/Resource.lean:138`, `isPrivate` `:49`); theorems `bytes_no_private_hop` (`Nap/Resource.lean:254`), `jobItems_policy` (`:907`); wider classes: README decision 12 |
| 44 | MIME sniffing (MUST): "Classify bytes by sniffing. Enforce scheme-appropriate allowlists." | MUST | RESOLVED (was MISMATCH) | Sniffing: OK (row 24). No MIME allowlist exists, per scheme or at all. `NapResource.finish` (`Nap/Resource.lean:126`) delivers any sniffed type except SVG. Not covered by README |
| 45 | "Never pass upstream `Content-Type` through" | MUST | OK | As row 2 |
| 46 | SVG rasterization (MUST): "Raw `image/svg+xml` MUST NOT be delivered. Rasterize ... in an isolated execution context with no network access." | MUST | OK | `finish` `Nap/Resource.lean:126-131`; theorem `bytes_mime_sniffed_not_svg`; isolation HOST `Host.lean:133-134` |
| 47 | Blossom hash check (MUST): "Hash mismatch returns `decode-failed`" | MUST | OK | `Nap/Resource.lean:170` |
| 48 | Hashtree verification (MUST): verify root, nodes, chunks, CHK; "mismatch returns `decode-failed`" | MUST | HOST | `Host.lean:594-595`, `:605-606` (`decode-failed` reply, mapped by `outcomeOf` `:507`) |
| 49 | Response size cap (SHOULD): "Recommended 10 MiB. Exceed returns `too-large`." | SHOULD | OK | `Policy.maxBytes` `Nap/Resource.lean:112`, `fetchChecked` `:141` |
| 50 | Fetch timeout (SHOULD): "Recommended 30 s per URL. Exceed returns `timeout`." | SHOULD | OK | `Cfg.timeoutSecs` `:547` (host sets `timedOut`), `fetchChecked` `Nap/Resource.lean:136` |
| 51 | Concurrency/rate limit (SHOULD): "10 in-flight and 60 requests/minute per napplet. Bulk counts per URL" | SHOULD | OK | `Cfg.maxInFlight` `:545`, `pump` `:689` (per URL). Per-minute rate: OPTIONAL, README l.158-159, l.249 |
| 52 | Bulk URL cap (SHOULD): "Recommended 100 URLs. Exceed returns top-level `resource.bytesMany.error` with `too-large`." | SHOULD | OK | `handle` `:731-732` |
| 53 | Redirect cap (SHOULD): "<= 5 hops. Re-check private IP policy per hop." | SHOULD | OK | `fetchChecked` `Nap/Resource.lean:137-138`; theorem `bytes_redirects_capped` |
| 54 | Blob quota (SHOULD): "Recommended 50 MiB outstanding per napplet. Exceed returns `quota-exceeded`." | SHOULD | OK | `applyQuota` `:531`, `Cfg.quota` `:543`. Counted per envelope, not across a napplet's concurrent requests; the README does not record this reading |
| 55 | Single-flight cache (SHOULD/MAY) | SHOULD | OPTIONAL | README "Optional behaviours" (l.249) |
| 56 | "SVG rasterization SHOULD cap input bytes, output dimensions, and wall-clock time" | SHOULD | HOST | `Host.lean:133-134`, `Run/Resource.lean:83-84`. A cap overflow or timeout comes back as `none` and is reported as `decode-failed`, not `too-large`/`timeout` |
| 57 | "The runtime MAY hydrate resource cache entries before the napplet asks for them" | MAY | OPTIONAL | README "Not modelled" (l.239-240) |
| 58 | "A carrier MUST separately declare its optional `resource` wire dependency" | MUST | OK | No carrier in the model sends `sidecar.resources` (RELAY/OUTBOX `resultJson`) |
| 59 | "SVG sidecars MUST already be rasterized" | MUST | OK | Vacuous (row 58) |
| 60 | "Shims MUST hydrate sidecars before invoking the napplet event handler" | MUST | NAPPLET | `Binding.lean:209` |
| 61 | "Sidecars do not change cache scope" | rule | NAPPLET | `Binding.lean:104` (per-instance cache) |
| 62 | "Napplets that need deduplication SHOULD pass canonical URL strings" | SHOULD | NAPPLET | Constrains napplet code |
| 63 | Error codes: malformed payload or empty `urls` top-level; "An invalid URL/reference fails only its bulk item" | table | OK | `decode` `:598-602`, `handle` `:730`; per-slot `precheck` |
| 64 | Security: "Upstream `Content-Type` is attacker-controlled and MUST NOT be trusted" | MUST | OK | As row 2 |
| 65 | "Raw SVG ... MUST be rasterized before delivery" | MUST | OK | As row 46 |
| 66 | Hashtree keys: "Runtimes MUST keep them client-side and MUST NOT forward them to relays, storage servers, FIPS peers, or HTTP request bodies" | MUST | HOST | `Host.lean:594-596` |
| 67 | "Cache scope comes from runtime-bound napplet identity, never napplet payload" | rule | OK | As rows 9 and 11 |
| 68 | "Runtimes MAY redact schemes or round limits for untrusted napplets" | MAY | OK | `Cfg.discloseInfo`, `discloseLimits` (`:549-551`), `handle` `:727` |
| 69 | "`resource.info.schemes` ... does not grant fetch authority. Each ... URL still passes through scheme dispatch and policy checks" | rule | OK | `precheck` and `NapResource.bytes` run for every URL whatever `info` said |

Notes

- Row 56: the upstream error table assigns `too-large` to rasterisation caps and `timeout` to rasterisation
  timeouts. `Host.rasterize : Bytes → Option Bytes` cannot tell these apart, so the model reports
  `decode-failed` for all three. These are SHOULD-level caps, so this is not listed as a mismatch.
- Row 54: the quota is counted per envelope. Record this in README "RESOURCE".
