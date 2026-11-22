/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Binding

/-!
# Napplet side: the `window.napplet.<domain>` method surface

The web projection surfaces domain `X` as the object `window.napplet.X`, present
exactly when the shell exposes `X` (NIP-5D §Transport; `Runtime.Output.iframeCreated`
lists the domains). Each method maps to the wire as follows: a request method builds
its envelope with the domain component's `encodeReq` for the matching `Req`
constructor (`Napplet/Run/<Name>.lean`), sends it with `Binding.request` (fresh `id`),
and resolves with the result envelope `Binding.receive` settles; fire-and-forget
methods post `encodeReq` without an id; `on…` handlers register with
`Binding.register` under the push type (and routing field) listed; convention URI
methods go through `BindingUri`. Methods marked local in the tables have no wire
message.

The tables are the upstream API tables at the commits in `lean/README.md`, verbatim
(NAP-SHELL with PR #142's `domains` and `check`, NAP-INTENT with PR #148's `launch`).
`shell.domains()` is `NapShell.domains` over the injected domain objects and agrees with
`supports` (`NapShell.domains_supports`). In the web projection `intent.launch` takes a
bare NIP-19 `naddr` (`BindingUri.launch`).

### `window.napplet.shell` (NAP-SHELL)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `supports` | `domain` (`text`) | `boolean` | local projection availability query |
| `domains` | none | list of text | local projection availability query |
| `check` | `manifest` (`NappletManifest`) | `ShellCompatibility` | `shell.check` / `shell.check.result` |
| `services` | none | list of text service names | local read of `shell.init` |
| `ready` | none | `ShellEnvironment` | resolves after `shell.ready` / `shell.init` |
| `onReady` | handler for `ShellEnvironment` | `Subscription` handle | fires after `shell.init` |

### `window.napplet.intent` (NAP-INTENT)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `invoke` | convention URI (`text`), optional options (`IntentInvokeOptions`) | `IntentResult` | `intent.invoke` / `intent.invoke.result` |
| `open` | convention URI whose intent is `open` (`text`), optional options (`IntentInvokeOptions`) | `IntentResult` | sugar over `invoke` |
| `available` | archetype (`text`) | `IntentAvailability` | `intent.available` / `intent.available.result` |
| `handlers` | none | list of `IntentAvailability` | `intent.handlers` / `intent.handlers.result` |
| `onChanged` | handler for `IntentAvailability` | `Subscription` handle | `intent.changed` |
| `onDelivery` | handler for `IntentDelivery` | `Subscription` handle | `intent.deliver` |
| `launch` | target (`IntentTarget`), optional behavior (`IntentBehavior`) | `IntentLaunchResult` | `intent.launch` / `intent.launch.result` |

### `window.napplet.inc` (NAP-INC)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `emit` | `topic` or convention URI (`tstr`), optional `payload` (`any`) | none | `inc.emit` |
| `on` | `topic` (`tstr`), event handler for `IncEvent` | `Subscription` handle | `inc.subscribe` / `inc.subscribe.result` |
| `channel.open` | `target` (`tstr`, peer endpoint identifier) | `ChannelHandle` | `inc.channel.open` / `inc.channel.open.result` |
| `channel.onOpened` | handler for inbound `ChannelHandle` | `Subscription` handle | `inc.channel.opened` |
| `channel.list` | none | list of `ChannelInfo` | `inc.channel.list` / `inc.channel.list.result` |
| `channel.broadcast` | `payload` (`any`) | none | `inc.channel.broadcast` |
| `ChannelHandle.emit` | `payload` (`any`) | none | `inc.channel.emit` |
| `ChannelHandle.on` | event handler for `ChannelEvent` | `Subscription` handle | `inc.channel.event` |
| `ChannelHandle.onClosed` | handler for `ChannelClosed` | `Subscription` handle | `inc.channel.closed` |
| `ChannelHandle.close` | none | none | `inc.channel.close` |

### `window.napplet.theme` (NAP-THEME)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `get` | none | `Theme` | `theme.get` / `theme.get.result` |
| `onChanged` | handler for `Theme` | `Subscription` handle | `theme.changed` |

### `window.napplet.identity` (NAP-IDENTITY)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `getPublicKey` | none | `tstr` public key, or `""` when no signer is connected | `identity.getPublicKey` / `identity.getPublicKey.result` |
| `onChanged` | handler for `tstr` public key | `Subscription` handle | `identity.changed` |
| `getRelays` | none | `RelayMap` | `identity.getRelays` / `identity.getRelays.result` |
| `getProfile` | none | `ProfileData` or `null` | `identity.getProfile` / `identity.getProfile.result` |
| `getFollows` | none | list of `tstr` pubkeys | `identity.getFollows` / `identity.getFollows.result` |
| `getList` | `type` (`tstr`) | list of `tstr` entries | `identity.getList` / `identity.getList.result` |
| `getZaps` | none | list of `ZapReceipt` | `identity.getZaps` / `identity.getZaps.result` |
| `getMutes` | none | list of `tstr` pubkeys | `identity.getMutes` / `identity.getMutes.result` |
| `getBlocked` | none | list of `tstr` pubkeys | `identity.getBlocked` / `identity.getBlocked.result` |
| `getBadges` | none | list of `Badge` | `identity.getBadges` / `identity.getBadges.result` |

### `window.napplet.relay` (NAP-RELAY)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `subscribe` | `filters` (`NostrFilter` or list), optional `options` (`RelaySubscribeOptions`) | `Subscription` handle streaming `RelayEventResult` | `relay.subscribe` plus `relay.event` / `relay.eose` |
| `publish` | `template` (`EventTemplate`) | `NostrEvent` | `relay.publish` / `relay.publish.result` |
| `publishEncrypted` | `template` (`EventTemplate`), `recipient` (`tstr`), optional `encryption` (`RelayEncryption`) | `NostrEvent` | `relay.publishEncrypted` / `relay.publishEncrypted.result` |
| `query` | `filters` (`NostrFilter` or list) | list of `RelayEventResult` | `relay.query` / `relay.query.result` |
| `Subscription.close` | none | none | `relay.close` |

### `window.napplet.storage` (NAP-STORAGE)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `getItem` | `key` (`tstr`) | `tstr` or `null` | `storage.get` / `storage.get.result` |
| `setItem` | `key` (`tstr`), `value` (`tstr`) | none | `storage.set` / `storage.set.result` |
| `removeItem` | `key` (`tstr`) | none | `storage.remove` / `storage.remove.result` |
| `keys` | none | list of `tstr` keys | `storage.keys` / `storage.keys.result` |
| `instance.getItem` | `key` (`tstr`) | `tstr` or `null` | `storage.get` / `storage.get.result` with `scope: "instance"` |
| `instance.setItem` | `key` (`tstr`), `value` (`tstr`) | none | `storage.set` / `storage.set.result` with `scope: "instance"` |
| `instance.removeItem` | `key` (`tstr`) | none | `storage.remove` / `storage.remove.result` with `scope: "instance"` |
| `instance.keys` | none | list of `tstr` keys | `storage.keys` / `storage.keys.result` with `scope: "instance"` |

### `window.napplet.keys` (NAP-KEYS)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `registerAction` | `action` (`Action`) | `RegisterResult` | `keys.registerAction` / `keys.registerAction.result` |
| `unregisterAction` | `actionId` (`tstr`) | none | `keys.unregisterAction` |
| `forward` | keyboard event fields | none | `keys.forward` |
| `onAction` | `actionId` (`tstr`), local callback | `Subscription` handle | local helper; not a wire message |

### `window.napplet.media` (NAP-MEDIA)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `createSession` | `options` (`MediaSessionCreate`) | `MediaSessionResult` | `media.session.create` / `media.session.create.result` |
| `updateSession` | `sessionId` (`text`), partial `metadata` (`MediaMetadata`) | none | `media.session.update` |
| `destroySession` | `sessionId` (`text`) | none | `media.session.destroy` |
| `reportState` | `sessionId` (`text`), `state` (`MediaState`) | none | `media.state` |
| `reportCapabilities` | `sessionId` (`text`), `actions` (list of `MediaAction`) | none | `media.capabilities` |
| `command` | `sessionId` (`text`), command (`MediaCommand`) | none | `media.command` |
| `onState` | `sessionId` (`text`), handler for `MediaState` | `Subscription` handle | `media.state` |
| `onCapabilities` | `sessionId` (`text`), handler for list of `MediaAction` | `Subscription` handle | `media.capabilities` |
| `onCommand` | `sessionId` (`text`), handler for `MediaCommand` | `Subscription` handle | `media.command` |
| `onControls` | `sessionId` (`text`), handler for list of `MediaAction` | `Subscription` handle | `media.controls` |
| `onEnded` | `sessionId` (`text`), handler for `MediaSessionEnded` | `Subscription` handle | `media.session.ended` |

### `window.napplet.notify` (NAP-NOTIFY)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `send` | `notification` (`NotificationPayload`) | `NotificationResult` | `notify.send` / `notify.send.result` |
| `dismiss` | `notificationId` (`tstr`) | none | `notify.dismiss` |
| `badge` | `count` (`uint`) | none | `notify.badge` |
| `registerChannel` | `channel` (`NotificationChannel`) | none | `notify.registerChannel` |
| `requestPermission` | optional `channel` (`tstr`) | `PermissionResult` | `notify.requestPermission` / `notify.requestPermission.result` |
| `onAction` | handler for `notificationId` and `actionId` | `Subscription` handle | `notify.action` |
| `onClicked` | handler for `notificationId` | `Subscription` handle | `notify.clicked` |
| `onDismissed` | handler for `notificationId` and optional reason | `Subscription` handle | `notify.dismissed` |
| `onControls` | handler for list of `NotifyControl` | `Subscription` handle | `notify.controls` |

### `window.napplet.resource` (NAP-RESOURCE)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `info` | none | `ResourceInfo` | `resource.info` |
| `bytes` | `url`, `opts?` | one complete byte sequence | `resource.bytes` |
| `bytesMany` | non-empty `urls`, `opts?` | ordered per-URL results | `resource.bytesMany` |

### `window.napplet.config` (NAP-CONFIG)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `registerSchema` | `schema` (`ConfigSchema`), optional `version` (`uint`) | none; errors arrive through `onSchemaError` | `config.registerSchema` / `config.registerSchema.result` |
| `get` | none | `ConfigValues` | `config.get` / `config.values` |
| `subscribe` | handler for `ConfigValues` | `Subscription` handle | `config.subscribe` / `config.values` |
| `onSchemaError` | handler for `ConfigSchemaError` | `Subscription` handle | `config.schemaError` |
| `openSettings` | optional `section` (`tstr`) | none | `config.openSettings` |
| `schema` | none | `ConfigSchema` or `null` | local read of currently registered schema |

### `window.napplet.upload` (NAP-UPLOAD)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `info` | none | `UploadInfo` | `upload.info` / `upload.info.result` |
| `upload` | `request` (`UploadRequest`) | `UploadResult` | `upload.upload` / `upload.upload.result` |
| `status` | `uploadId` (`tstr`) | `UploadStatus` | `upload.status` / `upload.status.result` |
| `onStatus` | handler for `UploadStatus` | `Subscription` handle | `upload.status.changed` |

### `window.napplet.value` (NAP-VALUE)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `send` | `request` (`ValueRequest`) | `ValueResult` | `value.send` / `value.send.result` |
| `quote` | `request` (`ValueRequest`) | `ValueQuote` | `value.quote` / `value.quote.result` |
| `status` | `transferId` (`tstr`) | `ValueStatus` | `value.status` / `value.status.result` |
| `onStatus` | handler for `ValueStatus` | `Subscription` handle | `value.status.changed` |

### `window.napplet.outbox` (NAP-OUTBOX)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `getEvent` | `eventId` (`tstr`), optional `options` (`OutboxEventOptions`) | `OutboxEventResult` | `outbox.getEvent` / `outbox.getEvent.result` |
| `query` | `filters` (`NostrFilter` or list), optional `options` (`OutboxQueryOptions`) | `OutboxResult` | `outbox.query` / `outbox.query.result` |
| `subscribe` | `filters` (`NostrFilter` or list), optional `options` (`OutboxSubscribeOptions`) | `OutboxSubscription` handle | `outbox.subscribe` plus push messages |
| `publish` | `template` (`EventTemplate`), optional `options` (`OutboxPublishOptions`) | `OutboxPublishResult` | `outbox.publish` / `outbox.publish.result` |
| `resolveRelays` | `target` (`OutboxTarget`) | `OutboxRelayPlan` | `outbox.resolveRelays` / `outbox.resolveRelays.result` |

### `window.napplet.cvm` (NAP-CVM)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `discover` | optional `query` (`CvmDiscoverQuery`) | list of `CvmServer` | `cvm.discover` / `cvm.discover.result` |
| `request` | `server` (`CvmServerRef`), `message` (`McpMessage`), optional `options` (`CvmRequestOptions`) | `McpMessage` or `null` | `cvm.request` / `cvm.request.result` |
| `listTools` | `server` (`CvmServerRef`), optional `options` (`CvmRequestOptions`) | list of `McpTool` | wrapper over `request` |
| `callTool` | `server` (`CvmServerRef`), `name` (text), optional `args` (`JsonObject`), optional `options` (`CvmRequestOptions`) | `McpToolResult` | wrapper over `request` |
| `listResources` | `server` (`CvmServerRef`), optional `options` (`CvmRequestOptions`) | list of `McpResource` | wrapper over `request` |
| `readResource` | `server` (`CvmServerRef`), `uri` (text), optional `options` (`CvmRequestOptions`) | list of `McpResourceContent` | wrapper over `request` |
| `close` | `server` (`CvmServerRef`) | none | `cvm.close` / `cvm.close.result` |
| `onEvent` | handler for `CvmEvent` | `Subscription` handle | `cvm.event` |
| `registry.list` | optional `query` (`CvmRegistryQuery`) | list of `CvmRegistryEntry` | `cvm.registry.list` / result |
| `registry.has` | `selector` (`CvmRegistrySelector`), optional `options` (`CvmRegistryOptions`) | boolean | `cvm.registry.has` / result |
| `registry.describe` | `selector` (`CvmRegistrySelector`), optional `options` (`CvmRegistryOptions`) | `CvmRegistryEntry` | `cvm.registry.describe` / result |
| `registry.call` | `selector` (`CvmRegistrySelector`), `tool` (text), optional `args` (`JsonObject`), optional `options` (`CvmRegistryCallOptions`) | `McpToolResult` | `cvm.registry.call` / result |

### `window.napplet.link` (NAP-LINK)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `open` | `url` (`text`), optional `options` (`LinkOpenOptions`) | `LinkOpenResult` | `link.open` / `link.open.result` |

### `window.napplet.pow` (NAP-POW)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `mine` | `template` (`EventTemplate`), `target` (`uint`), optional `opts` (`PowOptions`) | `PowJob` handle | `pow.mine` plus push messages |
| `mineAndPublish` | `template` (`EventTemplate`), `target` (`uint`), optional `opts` (`PowOptions`) | `PowJob` handle | `pow.mineAndPublish` plus push messages |
| `queue` | none | list of `PowJobSummary` | `pow.queue` / `pow.queue.result` |
| `job` | `jobId` (`tstr`) | `PowProgress` | `pow.job` / `pow.job.result` |
| `hashrate` | none | `PowHashrate` | `pow.hashrate` / `pow.hashrate.result` |
| `cancel` | `jobId` (`tstr`) | `bool` | `pow.cancel` / `pow.cancel.result` |
| `pause` | optional `jobId` (`tstr`) | none | `pow.pause` / `pow.pause.result` |
| `resume` | optional `jobId` (`tstr`) | none | `pow.resume` / `pow.resume.result` |
| `formatHashRate` | `hashesPerSecond` (`number`) | `tstr` | local helper; no wire message |

### `window.napplet.display` (NAP-DISPLAY)

| Operation | Parameters | Result | Wire |
|-----------|------------|--------|------|
| `list` | none | list of `DisplayDevice` | `display.list` / `display.list.result` |
| `push` | `displayId` (text), `pixels` (list of `Pixel`) | `null` | `display.push` / `display.push.result` |

-/

namespace Napplet.BindingApi

/-- Request types that settle by result (everything except fire-and-forget and the
subscription streams); used by `Binding.request`. -/
def settles (t : String) : Bool := !(t ∈ Binding.noResult)

#guard settles "storage.get" && !settles "relay.subscribe"

end Napplet.BindingApi
