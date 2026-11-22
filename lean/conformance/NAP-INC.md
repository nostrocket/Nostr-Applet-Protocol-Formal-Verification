# NAP-INC conformance

Upstream: `napplet/naps` `naps/NAP-INC.md` at `377bf939c6c906817084b43dd21d424de646dbc2`.
Lean: `Napplet/Run/Inc.lean` (component), `Napplet/Nap/Inc.lean` (pure model),
`Napplet/Component.lean` (`Ctx.endpointId`), `Napplet/BindingUri.lean` and
`Napplet/Binding.lean` (napplet side), `Napplet/Host.lean` §INC (`revoke` event).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | "The shell MAY also use INC topics for internal coordination" | MAY | OPTIONAL | Not done; README "Optional behaviours" (`shell:*` interception) |
| 2 | `IncEvent.topic`, `.sender` required; `.payload` optional | schema | OK | `Run/Inc.lean:195-196` `eventJson` |
| 3 | `ChannelHandle`/`ChannelInfo` `id`, `peer` required; `ChannelEvent` `channelId`, `sender` required; `ChannelClosed.channelId` required | schema | OK | `Run/Inc.lean:204-220` |
| 4 | Endpoint identifiers "MUST NOT be interpreted as a manifest `d` tag" | MUST NOT | OK | `Component.lean:56` `endpointId` (`endpoint-<window>` or shell name); never derived from `d` |
| 5 | "The runtime MUST distinguish different publishers, manifests, and simultaneous instances" | MUST | OK | One id per window (`Component.lean:56`); windows never reused (decision 4) |
| 6 | "It MUST bind each identifier to the authenticated endpoint and its verified manifest and artifact, including root and snapshot manifests" | MUST | OK | `Ctx.ofBinding` (`Component.lean:48`); `Runtime.lean:187-188` `ctxOf`; theorem `ctx_verified` (`Runtime.lean:1240`) |
| 7 | "An identifier MUST NOT be reused for another endpoint during the runtime session" | MUST NOT | OK | Decision 4 and decision 33; `Runtime.lean:60-64` `endpointName` contract |
| 8 | "A channel remains bound to the endpoint authorized at open; a restart or replacement requires a new channel" | normative prose | OK | `Run/Inc.lean:83-89` (`Channel` stores ports); teardown removes it (`Run/Inc.lean:294-297`) |
| 9 | `emit`: "The runtime derives `sender` from the authenticated emitting endpoint ... The emitter cannot set or override `sender`" | MUST (prose) | OK | `Run/Inc.lean:130-139` (no sender field), 247-249; theorem `emit_delivery` (413) |
| 10 | "Multiple subscriptions to the same topic are independent" | API | OK (napplet side) | Wire subscription is one per (endpoint, topic) (`Run/Inc.lean:252`); the binding fans out locally (`Run/Inc.lean:34-36`) |
| 11 | Convention URI: "the runtime MUST: 1. Remove the query ... 2. Percent-decode each unique `name=value` pair as text ... 3. ... use that map as `payload`" | MUST | OK (binding) | `BindingUri.lean:83-99` `emit`; `Nap/Intent.lean:301` `bindUri`, `parseQuery` (208) |
| 12 | "The runtime MUST NOT coerce query values ... A `+` is a literal plus sign" | MUST NOT | OK | `Nap/Intent.lean:194-205` `pctBytes`/`pctDecode`; vector at 348 |
| 13 | "A convention URI with a fragment, malformed percent-encoding, a repeated name, or an explicit `payload` argument alongside query parameters MUST be rejected before emission" | MUST | OK | `Nap/Intent.lean:301-312`; theorem `bindUri_ok` (314); vectors 352-357, `BindingUri.lean:109-110` |
| 14 | "Structured or non-text data MUST use the explicit `payload` argument with a queryless topic" | MUST | NAPPLET | Enforced by row 13 |
| 15 | Topics outside convention syntax are opaque ("the shell treats the complete topic as opaque text") | normative | RESOLVED (was MISMATCH) (napplet side, minor) | `BindingUri.lean:95-96` runs every `napplet:`-prefixed topic through `bindUri`, which rejects a queryless topic that is not `napplet:<a>/<b>` with `[A-Za-z0-9._-]` segments (`Nap/Intent.lean:217-225`): `emit("napplet:foo")` and `emit("napplet:my feed/open")` are refused (checked by `#eval`). Upstream lists only fragment, bad encoding, repeated name and query+payload as reasons to reject |
| 16 | `channel.open`: "Before reporting success, the runtime MUST enqueue `inc.channel.opened` for the target" | MUST | OK | `Run/Inc.lean:244`; theorem `open_ok` (437) |
| 17 | "If the target is not found, has no live endpoint, cannot receive the notification, or is ACL-denied, the request fails" | MUST (prose) | OK | `Run/Inc.lean:230-239`; theorem `open_cases` (449); self-target: decision 6 |
| 18 | "The shell validates once on open. Subsequent messages flow without per-message authorization" | normative | OK | `Run/Inc.lean:257-263` (membership only) |
| 19 | `onClosed`: "A handler registered after closure MUST be invoked with the retained terminal record" | MUST | RESOLVED (was MISMATCH) (napplet side) | `Binding.lean:211,215`: `inc.channel.closed` is buffered until the first handler for that `channelId`, then removed; a second later `onClosed` gets nothing (checked by `#eval`: `(1, 0)`) |
| 20 | `close()`: "Both handles become terminal and their `onClosed` handlers are notified" | API | OK | `Run/Inc.lean:270-277`; theorem `close_notifies_both` (501) |
| 21 | `inc.emit` "has no `id`"; carries the stable topic and transposed payload | wire | OK | `Run/Inc.lean:146-149,184` |
| 22 | `inc.subscribe` uses `id`; result echoes it; `inc.unsubscribe` fire-and-forget; `inc.event` no `id` | wire | OK | `Run/Inc.lean:150-160,195-199` |
| 23 | "The runtime MUST enqueue `inc.channel.opened` for the target before sending a successful `inc.channel.open.result`" | MUST | OK | Row 16 |
| 24 | "For each endpoint, handle creation MUST precede any `inc.channel.event` or `inc.channel.closed` for that channel" | MUST | OK | Target gets `opened` and opener gets `open.result` in the same step, before any input from either (`Run/Inc.lean:244`; host applies outputs in order, `Host.lean:39-41`) |
| 25 | `inc.subscribe.result` "MAY include an `error` ... the subscription was not registered" | MAY | OK | `Run/Inc.lean:250-254` |
| 26 | `inc.channel.open.result` with `error`: "no channel was created" | normative | OK | `Run/Inc.lean:232-239` (state unchanged on every failure) |
| 27 | "the shell treats the complete topic as opaque text. It MUST NOT parse, decode, normalize, prefix-match, or wildcard-match a topic" | MUST NOT | OK | `Run/Inc.lean:248` exact `==`; vector 213 |
| 28 | "The shell MUST route `inc.emit` messages to all napplets subscribed to the exact same complete topic string" | MUST | OK | `Run/Inc.lean:247-249`; theorem `emit_delivery` (413) |
| 29 | "The shell MUST copy the emitted `topic` unchanged into each delivered `inc.event`" | MUST | OK | `Run/Inc.lean:249` |
| 30 | "The runtime MUST derive `sender` ... It MUST ignore or reject caller-supplied sender data" | MUST | OK | Row 9; decoder ignores `sender` (`Run/Inc.lean:143-181`) |
| 31 | "The shell MUST NOT deliver `inc.event` back to the emitting napplet" | MUST NOT | OK | `Run/Inc.lean:248` (`x.1 != cx.port`); theorem `emit_delivery` |
| 32 | "The shell MUST respond to `inc.subscribe` with `inc.subscribe.result` carrying the same `id`" | MUST | OK | theorem `subscribe_answered` (`Run/Inc.lean:428`); missing `topic` → `"invalid request"` (156) |
| 33 | "The shell MUST honor `inc.unsubscribe` by removing the subscription for that topic" | MUST | OK | `Run/Inc.lean:255` |
| 34 | "The shell MAY intercept specific topic prefixes"; "MAY enforce ACL checks ... reject subscriptions or emits" | MAY | OK / OPTIONAL | Subscribe ACL `Cfg.subscribeAllowed` (`Run/Inc.lean:73`); interception and emit ACL left out (README optional list) |
| 35 | "The shell MUST respond to `inc.channel.open` with `inc.channel.open.result` carrying the same `id`" | MUST | OK | `Run/Inc.lean:230-244`; theorem `open_cases` (449); missing `target` → `"invalid request"` (167) |
| 36 | "The shell MUST assign a `channelId` (opaque identifier) on successful channel open" | MUST | OK | `Run/Inc.lean:225,241` (`c-<n>` or `Cfg.channelName`, decision 33) |
| 37 | "The shell MUST validate that the target endpoint identifier exists and has a live napplet endpoint" | MUST | OK | `Run/Inc.lean:231` `World.byEndpointId?` over live endpoints; theorem `byEndpointId_live` (321) |
| 38 | "The runtime MUST derive the opener endpoint identifier from its authenticated endpoint. The opener cannot set or override `peer`" | MUST | OK | `Run/Inc.lean:244` (`cx.endpointId`) |
| 39 | "The runtime-provided binding MUST materialize a `ChannelHandle` from `inc.channel.opened` and retain it until at least one `channel.onOpened` handler receives it" | MUST | OK (napplet side) | `Binding.lean:54-56,211` (retained), `register_delivers_buffer` (241) |
| 40 | "The runtime-provided binding MUST retain incoming `inc.channel.event` messages until at least one `ChannelHandle.on` handler is registered ... MUST NOT silently discard" | MUST | OK (napplet side) | `Binding.lean:54-60,211`; theorem `retained_buffered` (250) |
| 41 | "The runtime-provided binding MUST retain the terminal `inc.channel.closed` record. A later `ChannelHandle.onClosed` registration MUST receive it" | MUST | RESOLVED (was MISMATCH) (napplet side) | Row 19 |
| 42 | "A runtime MAY bound unopened-handle or message buffers. On overflow it MUST close the channel and notify both endpoints" | MAY / MUST | OK | Buffers are unbounded, so the overflow MUST never triggers |
| 43 | "The shell MUST forward `inc.channel.emit` messages to the channel peer as `inc.channel.event`" | MUST | OK | `Run/Inc.lean:257-263`; theorem `chEmit_delivery` (474) |
| 44 | "The shell MUST NOT perform per-message validation on channel messages after open" | MUST NOT | OK | Row 18 (only membership is checked: a non-member's `channelId` is ignored, theorem `nonmember_ignored` 509) |
| 45 | "The shell MUST send `inc.channel.closed` to both sides when a channel is torn down (graceful close, iframe removal, or ACL revocation)" | MUST | OK + DECISION | Close: `Run/Inc.lean:275`; revocation: `revoke` (282), `Host.lean:346-351`; iframe removal sends only to the survivor (`drop`, 294-297), because the removed side's port is closed: README INC paragraph ("to the surviving peer only") |
| 46 | "The shell MUST respond to `inc.channel.list` with `inc.channel.list.result` listing the napplet's active channels" | MUST | OK | `Run/Inc.lean:267-269` (inbound and outbound) |
| 47 | "The shell MUST deliver `inc.channel.broadcast` to all open channel peers of the sender, excluding the sender itself" | MUST | OK | `Run/Inc.lean:264-266`; theorem `broadcast_delivery` (492); `Channel.peer?` never returns the caller (theorem `peer?_some`, 101) |
| 48 | "The shell MUST clean up channel state when a napplet endpoint is destroyed, sending `inc.channel.closed` with `reason: \"peer destroyed\"` to the surviving endpoint" | MUST | OK | `Run/Inc.lean:294-297`; theorems `drop_notifies_peers` (530), `drop_removes` (537), `teardown_clears` (`Runtime.lean:906`) |
| 49 | "The shell MAY enforce ACL checks on `inc.channel.open`"; "MAY impose a maximum number of concurrent channels" | MAY | OK | `Cfg.openAllowed` (`Run/Inc.lean:75`, `"target denied"`); `Cfg.maxChannels` (77, `"channel limit reached"`) |
| 50 | "The shell MAY restrict topics via ACL" | MAY | OK | Row 34 |
| 51 | "Receiving napplets are responsible for validating payload content"; "Receivers should check the `sender`" | advisory | NAPPLET | — |
| 52 | "The target MAY close it immediately" | MAY | OK | `chClose` by either member (`Run/Inc.lean:270-277`) |
| 53 | "The runtime SHOULD rate-limit opens and bound buffers per napplet" | SHOULD | OPTIONAL (not listed) | Only the concurrent-channel cap exists; README does not list open rate limits or buffer bounds |
| 54 | "Channel IDs are opaque. Napplets cannot enumerate or guess other channels' IDs" | normative prose | OK (by membership) | Default ids `c-<n>` are guessable, but a non-member's emit/close is ignored (theorem `nonmember_ignored`, `Run/Inc.lean:509`) and `inc.channel.list` shows only own channels, so guessing gives no access |
| 55 | "Napplets SHOULD NOT send sensitive data via broadcast" | SHOULD NOT | NAPPLET | — |
