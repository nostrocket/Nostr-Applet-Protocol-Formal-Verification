# NAP-OUTBOX conformance

Upstream: `napplet/naps` PR #32, `naps/NAP-OUTBOX.md` at `8865f73d52a4864afee145f28d26520476273927`.
Lean: `Napplet/Run/Outbox.lean` (component), `Napplet/Nap/Outbox.lean` (pure model),
`Napplet/Host.lean` §OUTBOX (host contract).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | getEvent: "If `options.author` is present, the shell SHOULD use that author's outbox relays as the primary read target" | SHOULD | OK | `stepReq` `Run/Outbox.lean:514-519` (author looked up), `readPlan` `:418` (author's write relays) |
| 2 | "If no author is known, the shell MAY use relay hints, cache, policy relays, fallback relays, or relay intelligence" | MAY | OK | `readPlan` `:422-423` (fallback, allowed hints; empty plan means the pool, `complete` `:453`) |
| 3 | "The shell validates the event ID and signature before returning it" | prose | OK | `pick` `:228`, `stepReply` `:582`, `onReply` `:627`; theorem `getEventMsg_sound` (`:980`) |
| 4 | publish: "When `options.toInboxes` is non-empty, the shell MUST resolve those authors' NIP-65 read relays and include each resolved, policy-allowed relay" | MUST | OK | `stepReq` `:545` (one lookup per author), `NapOutbox.plan` `Nap/Outbox.lean:111`; theorem `plan_includes_inboxes` (`Nap/Outbox.lean:190`) |
| 5 | "If the shell cannot satisfy a required publish fanout target, it MUST report the failure through `OutboxPublishResult`" | MUST | OK | Unresolved authors: `stepReply` `:606-610` (`error: "relay list unavailable"`), theorem `missing_inbox_reported` (`Nap/Outbox.lean:197`), README decision 14. Per-relay failures: `relays` map from host acks (`pubMsg` `:273`). Empty plan: `complete` `:457` |
| 6 | resolveRelays: "napplets SHOULD prefer `query`, `subscribe`, or `publish`" | SHOULD | NAPPLET | Constrains napplet code |
| 7 | "`options.relays` ... never bypasses shell ACLs" | design note | OK | Read hints filtered by `Cfg.allowed` (`readPlan` `:423`); publish relays filtered in `NapOutbox.plan`; theorems `plan_allowed` (`Nap/Outbox.lean:179`), `onReply_publish_relays` (`:864`) |
| 8 | "`OutboxPublishOptions.toOutbox` defaults to `true`" | design note | OK | `pubOptsOf` `:414` |
| 9 | Schema: `OutboxRelayPlan.relays`, `source` required | schema | OK | `planMsg` `:280` always sets both, including on error (`:330`, `:548`) |
| 10 | Schema: `OutboxResult.events` required | schema | OK | `queryMsg` `:258`, `queryErr` `:264` (`events: []` on error) |
| 11 | Schema: `OutboxPublishResult.ok` required | schema | OK | `pubMsg` `:273` |
| 12 | "Result messages MAY include `error`" | MAY | OK | `getEventMsg` `:245`, `queryMsg` `:258`, `pubMsg` `:273`, `planMsg` `:280` |
| 13 | "If the shell returns partial results ... it SHOULD set `incomplete: true` and still return events it found" | SHOULD | OK | Missing lists: `complete` `:452`; pool `closed`: `stepReply` `:597-599` |
| 14 | "The shell MUST resolve relay plans according to NIP-65 relay list metadata when available" | MUST | OK | `Call.relayList` lookups (`lookups` `:464`), `readPlan` `:418`, `resolvePlan` `:425`, `envOf` `:403` → `NapOutbox.plan` |
| 15 | "The shell MUST verify that an event returned by `outbox.getEvent` matches the requested `eventId`" | MUST | OK | `stepReply` `:582`, `pick` `:228`; theorems `getEventMsg_sound` (`:980`), `getEvent_matches` (`Nap/Outbox.lean:263`) |
| 16 | "The shell MUST deduplicate events by event ID before returning `outbox.query.result`" | MUST | OK | `queryEvents` `:238`; theorem `queryEvents_nodup` (`:1027`) |
| 17 | "The shell MUST validate event signatures before delivering events to napplets" | MUST | OK | `onReply` `:627` (`unverified`); theorems `onReply_unverified` (`:744`), `onReply_unverified_silent` (`:1048`), `queryEvents_sound` (`:1036`) |
| 18 | "The shell MUST sign event templates submitted through `outbox.publish`; napplets do not receive signing keys" | MUST | OK | `complete` `:459` (`Call.sign`), `stepReply` `:601-604`; theorems `handle_no_publish` (`:788`), `handle_sign`/`onReply_sign` (`:917`, `:940`, no napplet ciphertext signed) |
| 19 | "The shell MUST publish at most one signed event for each `outbox.publish` request" | MUST | OK | theorem `onReply_single_publish` (`:851`); `Nap/Outbox.lean:142` `publish_single_event` |
| 20 | "The shell MUST include the shell-user's NIP-65 write relays ... unless `toOutbox` is `false`" | MUST | OK | `NapOutbox.ownSet` (`Nap/Outbox.lean:100`); theorem `plan_includes_outbox` (`Nap/Outbox.lean:183`) |
| 21 | "The shell MUST resolve NIP-65 read relays for every author in `toInboxes` when `toInboxes` is non-empty" | MUST | OK | `stepReq` `:545`, `lookups` `:464` |
| 22 | "The shell MUST include every resolved, policy-allowed `toInboxes` relay in `outbox.publish` fanout or report failure" | MUST | OK | As rows 4 and 5 |
| 23 | "The shell MUST deduplicate `outbox.publish` relay URLs ... before publishing" | MUST | OK | `NapOutbox.plan` (`dedup`); theorems `plan_nodup` (`Nap/Outbox.lean:170`), `onReply_publish_relays` (`:864`) |
| 24 | "The shell MUST respond to every request with a result or lifecycle message carrying the same `id` or `subId`" | MUST | RESOLVED (was MISMATCH) | getEvent, query, publish, resolveRelays and close are always answered. A successful `outbox.subscribe` whose stream matches nothing never gets any message: EOSE is swallowed (`stepReply` `:593`) and upstream removed `outbox.eose` (changelog `70515a5`). Not covered by README |
| 25 | "The shell MUST deliver matching subscription events as `outbox.event` until the napplet sends `outbox.close` or the shell terminates the stream with `outbox.closed`" | MUST | OK | `stepReply` `:584-586`, `:600`; `stopSub` `:505` |
| 26 | "The shell SHOULD merge observed relay URLs into `sidecar.relayHints` after deduplication" | SHOULD | OK | query/getEvent: `merge` `:440`. Subscriptions deliver each id once with its first relay (`:585-586`, README "OUTBOX" l.149-154) |
| 27 | "The shell MAY include pre-resolved byte resources in `sidecar.resources`; NAP-RELAY's default-off ... applies" | MAY | OPTIONAL | Never: `resultJson` `:216` carries `relayHints` only; README "RELAY" (l.143-145) |
| 28 | "The shell SHOULD cache relay lists and refresh them according to shell policy" | SHOULD | HOST | `Host.lean:193-195` (`Call.relayList` "from cache or relays"); `Host.lean:540-541` |
| 29 | "The shell SHOULD fall back to configured relays when NIP-65 data is absent ... for read targets and for the shell-user's own write set. Fallback never substitutes for a `toInboxes` read relay." | SHOULD/rule | OK | `readPlan` `:422`, `NapOutbox.ownSet`; theorem `fallback_not_for_inboxes` (`Nap/Outbox.lean:203`); README decision 15 |
| 30 | Security: "`options.relays` MUST be subject to shell validation. Napplets MUST NOT be able to force connections to private network relays or disallowed hosts." | MUST | RESOLVED (was MISMATCH) | Validation hook exists (`Cfg.allowed` `:103`, theorem `plan_allowed`), but its default is `u.startsWith "wss://"`: `wss://192.168.0.1` and `wss://localhost` in `options.relays` reach `Call.publish` (checked by `#eval`). `Host.lean`'s `Call.publish`/`Call.subscribe` contract does not require refusing private addresses |
| 31 | "The shell MAY use NIP-66 or other relay intelligence" | MAY | OPTIONAL | Not modelled; a host may apply it inside `Call.subscribe … none`. Not listed in README |
| 32 | "The shell MAY enforce ACL checks for outbox read, subscribe, publish, relay override, and relay discovery" | MAY | OK | `Cfg.canRead`/`canWrite` (`:100-101`); theorem `handle_read_denied` (`:961`) |
| 33 | "Shells SHOULD limit broad outbox queries and apply user or napplet-specific policy for sensitive authors and filters" | SHOULD | OPTIONAL | Not done. Not listed in README "Optional behaviours" |
| 34 | "Shells SHOULD enforce timeouts, fallback limits, and policy checks before expanding beyond hinted or known relays" | SHOULD | OPTIONAL | Timeouts: host ends the stream (README "OUTBOX" l.153). A `getEvent` without an author goes to the whole pool (`complete` `:453`). Limits not listed in README |
| 35 | "Shells SHOULD enforce limits, timeouts, and maximum subscription counts" | SHOULD | OPTIONAL | Only the napplet's own `options.limit` is applied (`queryEvents` `:242`). Not listed in README |
| 36 | "Shells SHOULD show consent UI or require prior policy approval before signing and publishing" | SHOULD | OK | Prior policy approval: `Cfg.canWrite` (`:101`, checked `:536`) |
| 37 | "Shells MAY redact relay URLs or return a policy-derived plan" | MAY | OPTIONAL | Plans are not redacted (`planMsg` `:280`); hints can be switched off (`Cfg.relayHints`) |

Notes

- `Run/Outbox.lean:71-72` says that "a replaced `subId`" is answered with `outbox.closed {subId}`.
  The code does not do this. `stepReq` `.subscribe` (`:525-531`) only sends the unsubscribe and cancel
  effects (checked by `#eval`). The docstring is wrong. Sending `outbox.closed` would also be wrong,
  because it would close the new handle.
- `Host.lean` §POW (`Call.prompt .pow "publish"`) says "Same publish consent as NAP-OUTBOX `publish`".
  OUTBOX has no publish prompt; it gates publishing with `Cfg.canWrite` only.
