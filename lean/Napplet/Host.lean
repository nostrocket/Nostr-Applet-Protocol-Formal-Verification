/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Event
import Napplet.Manifest
import Napplet.Nap.Resource

/-!
# The host interface

Everything the composed runtime (`Napplet.Runtime.step`) needs from outside the
model is in this file, each item with its contract. An implementation supplies
exactly these; everything else is defined by the Lean definitions.

The host supplies four kinds of thing.

1. **Pure functions** (`Host`): deterministic, local computations. The runtime
   calls them inside a step and uses the answer immediately.
2. **Calls** (`Call` → `Reply`): operations that complete later, because they
   touch the network, the user's signer, the wallet, a storage server or the
   user. The runtime emits `Output.call tag c`; the host later feeds back
   `Input.reply tag r`, once (or, for a relay subscription, as a stream until it
   ends). The runtime ignores replies whose tag it no longer holds, so a reply for
   a torn-down napplet or a cancelled request has no effect.
3. **Effects** (`Effect`): fire-and-forget instructions to the host (show a
   notification, open a link, stop a subscription).
4. **Events** (`HostEvent`): things the host reports unprompted (the user
   changed, the theme changed, a key binding fired).

Browser events (iframe creation, `load`, window messages, ports) and the clock
are runtime inputs (`Napplet.Runtime.Input`); their meaning is fixed by NIP-5D
and the browser.

## Global contracts

* **Atomic steps.** The host feeds one input at a time and applies the outputs
  of a step, in order, before feeding the next input. Within one step's outputs,
  `send` messages to the same port keep their order.
* **Clock.** `Input.tick now` sets the runtime clock to `now` (Unix seconds,
  non-decreasing). The host sends it whenever its clock has advanced before
  feeding another input. Timeouts are host calls that fail with a timeout reply;
  the runtime does not count time itself.
* **Persistence.** The runtime state (`RtState`) is the durable state. Fields
  documented as persistent (NAP-STORAGE values, NAP-CONFIG values and schemas,
  user preferences such as intent defaults) MUST survive reloads; the host
  stores them. Everything keyed by port or window is per session.
* **Tags.** A tag (`CallTag`) is unique among the calls the runtime has outstanding.
  The host echoes it unchanged and never invents one.
* **Standards.** Where a contract names a standard the host implements that
  standard; the model does not restate it. The complete list the host interface
  relies on:
  - Nostr: NIP-01 (events, ids, filters, relay protocol), NIP-04, NIP-44 (payload
    encryption), NIP-07 / NIP-46 (signer access, host side only), NIP-13 (proof of
    work), NIP-17 / NIP-59 (which incoming events are encrypted), NIP-19 / NIP-21
    (bech32 entities, `nostr:` URIs), NIP-47 (NWC), NIP-51 (lists), NIP-57 (zaps),
    NIP-58 (badges), NIP-65 (relay lists), NIP-92 / NIP-94 (media metadata), NIP-96
    (HTTP file storage), NIP-98 (HTTP auth).
  - Blossom BUD-02 (upload), BUD-10 (`blossom:` URIs), BUD-11 (auth); Hashtree HTS-01
    and its URL-ENCODING note; LNURL LUD-06 / LUD-16; ContextVM CEP-4, CEP-6, CEP-8,
    CEP-15, CEP-17, CEP-35 and MCP 2025-11-25.
  - BIP-340 (Schnorr signatures), BIP-173 (bech32), FIPS 180-4 (SHA-256), RFC 8259
    (JSON), RFC 4648 (base64), RFC 2397 (`data:` URLs), WHATWG MIME Sniffing.
  - Browser behaviour of the web projection (HTML iframe `sandbox`/`srcdoc`,
    `postMessage`, `MessageChannel`, structured clone, `MessageEvent.source`, Content
    Security Policy Level 3) is fixed by NIP-5D and the HTML standard.
-/

namespace Napplet

open NapResource (FetchOutcome)

/-- NIP-44 (default) or NIP-04 (fallback) payload encryption. -/
inductive Encryption where
  | nip44
  | nip04
  deriving DecidableEq, Repr, Inhabited

def Encryption.name : Encryption → String
  | .nip44 => "nip44"
  | .nip04 => "nip04"

def Encryption.ofName? : String → Option Encryption
  | "nip44" => some .nip44
  | "nip04" => some .nip04
  | _ => none

/-- A NIP-65 relay list entry. -/
structure RelayEntry where
  url : String
  read : Bool
  write : Bool
  deriving DecidableEq, Repr

/-! ## 1. Pure functions -/

/-- Deterministic host functions. -/
structure Host where
  /-- `crypto.sha256`: FIPS 180-4 SHA-256, lowercase hex.
  `crypto.verifySig`: the manifest event's NIP-01 `id` is the SHA-256 of its
  serialisation and its `sig` is a valid BIP-340 signature by `pubkey` over `id`. -/
  crypto : Crypto
  /-- NIP-01 id check plus BIP-340 signature check for any event. -/
  verifyEvent : NostrEvent → Bool
  /-- WHATWG MIME Sniffing over the bytes alone (never an upstream `Content-Type`).
  Returns an essence such as `image/png`; `application/octet-stream` when unknown. -/
  sniff : Bytes → String
  /-- Rasterise SVG to PNG or WebP in an isolated context with no network access,
  within the SVG caps of NAP-RESOURCE. `none` on failure or cap overflow. -/
  rasterize : Bytes → Option Bytes
  /-- Does napplet-supplied event content look like NIP-04 (`<base64>?iv=<base64>`) or
  NIP-44 (version-prefixed base64 payload) ciphertext? Used to refuse signing
  ciphertext a napplet supplied (NIP-5D §Security 7). May over-approximate. -/
  looksCiphertext : String → Bool
  /-- Which scheme, if any, encrypts this incoming event to the user (NIP-04 kind 4,
  NIP-44 payloads per NIP-17/NIP-59). `none` for plaintext events. -/
  encryptedWith : NostrEvent → Option Encryption
  /-- NAP-UPLOAD: metadata stripping (for example EXIF) the shell applies unless the
  request sets `noTransform`. The identity function is a valid choice. -/
  transform : Bytes → Bytes
  /-- NAP-SHELL `services`: service names this shell reports. -/
  services : List String := []

/-! ## 2. Calls and replies -/

/-- A call's correlation tag: the issuing domain and a number unique among that
domain's outstanding calls. -/
structure CallTag where
  domain : Domain
  n : Nat
  deriving DecidableEq, Repr

/-- Operations that complete later with a `Reply`. -/
inductive Call where
  /-- Sign with the user's key (local key, NIP-07 or NIP-46). Reply: `signed`.
  Contract: `signed (some e)` has `e.pubkey, e.createdAt, e.kind, e.tags, e.content`
  equal to the input, `e.id` its NIP-01 id and `e.sig` a BIP-340 signature by the
  user's key; `signed none` if there is no signer or it refused. -/
  | sign (ev : UnsignedEvent)
  /-- Encrypt `plaintext` from the user to `recipient` (NIP-44 v2 or NIP-04).
  Reply: `text (some ciphertext)`, or `text none` on failure. The host MUST NOT fall
  back to another scheme on its own. -/
  | encrypt (scheme : Encryption) (recipient : Pubkey) (plaintext : String)
  /-- Decrypt an incoming event's `content` with the user's key. Reply: `text`. -/
  | decrypt (scheme : Encryption) (ev : NostrEvent)
  /-- Fetch one URL for NAP-RESOURCE. Reply: `fetched`. Contract: the host resolves
  the scheme (`https:` with DNS; `blossom:` per BUD-10 from servers it chooses;
  `nostr:` one NIP-19 hop; `hashtree:`/`htree:` per HTS-01 with root, node, chunk
  and CHK checks; `data:` locally) and reports every address it connected to, in
  order, *before* connecting to the next; it stops at the runtime's redirect cap.
  It never sends hashtree keys to relays, servers or peers. A failure the outcome
  cannot express is replied as `json {error, message?}` with a NAP-RESOURCE error code
  (`network-error`, `invalid-request`, `decode-failed`, ...). -/
  | fetch (url : String)
  /-- Ask the user. Reply: `decision`. The prompt shows the requesting napplet's
  verified identity and the `details`; the host never answers on the user's
  behalf except from a rule the user configured. Prompting MUST NOT block other
  inputs. -/
  | prompt (domain : Domain) (kind : String) (details : Json)
  /-- Open a relay subscription with NIP-01 filters, on the shell's pool or on the
  listed relays. Replies (a stream, same tag): `event` per matching stored or live
  event (NIP-01 signature already verified), one `eose` when stored events are
  exhausted, and `closed` if the pool ends it. Stopped by `Effect.unsubscribe`. -/
  | subscribe (filters : List Json) (relays : Option (List String))
  /-- Send a signed event to the shell's pool or to the listed relays.
  Reply: `published acks` with one `(relay, accepted)` per relay tried. -/
  | publish (ev : NostrEvent) (relays : Option (List String))
  /-- Resolve a pubkey's NIP-65 relay list (from cache or relays).
  Reply: `relayList (some entries)`, or `relayList none` if unavailable. -/
  | relayList (pubkey : Pubkey)
  /-- A NAP-specific host operation, named `op` in domain `domain`. Its arguments,
  reply (`json`) and contract are listed in the table of NAP operations below. -/
  | nap (domain : Domain) (op : String) (args : Json)
  deriving DecidableEq, Repr

/-- Replies to calls. -/
inductive Reply where
  | signed (ev : Option NostrEvent)
  | text (s : Option String)
  | fetched (o : FetchOutcome)
  | decision (allowed : Bool) (choice : Option String)
  /-- Subscription stream: one event and the relay it was observed on. -/
  | event (ev : NostrEvent) (relay : String)
  | eose
  | closed (reason : Option String)
  | published (acks : List (String × Bool))
  | relayList (entries : Option (List RelayEntry))
  | json (j : Json)

/-! ## 3. Effects -/

/-- Fire-and-forget instructions to the host. -/
inductive Effect where
  /-- Stop the relay subscription opened under this tag. -/
  | unsubscribe (tag : CallTag)
  /-- Abandon an outstanding call (for example a cancelled fetch); a later reply is
  ignored anyway. -/
  | cancel (tag : CallTag)
  /-- A NAP-specific instruction, listed in the table of NAP operations below. -/
  | nap (domain : Domain) (op : String) (args : Json)
  deriving DecidableEq, Repr

/-! ## 4. Events -/

/-- Things the host reports unprompted. -/
inductive HostEvent where
  /-- The shell user changed; `""` means signed out or no signer (NAP-IDENTITY). -/
  | userChanged (pubkey : String)
  /-- The active theme changed (NAP-THEME `Theme` JSON), or there is none. -/
  | themeChanged (theme : Option Json)
  /-- A NAP-specific event, listed in the table of NAP operations below. -/
  | nap (domain : Domain) (ev : String) (args : Json)
  deriving DecidableEq, Repr

/-! ## NAP operations

`Call.nap`, `Call.prompt`, `Effect.nap` and `HostEvent.nap` entries, and each NAP's use of
the core calls, by domain. Each entry gives the JSON arguments, the reply, and the
contract the host must meet. (The same text is kept next to each component in
`Napplet/Run/<Name>.lean`; `scripts/collect_host_ops.py` regenerates this section.)

Shell policy that is not asynchronous (enabled rails, limits, allowlists, display
devices, rate limits) is configuration, not a host call: `Runtime.Config` and each
component's `Cfg`, every field with a default taken from the upstream recommendation.

### SHELL, THEME, STORAGE

No NAP-specific operations. SHELL reports `Host.services`. THEME reads
`HostEvent.themeChanged` (a NAP-THEME `Theme` JSON object; one without all three
colours is ignored). STORAGE's store is persistent runtime state.

### IDENTITY (`Napplet/Run/Identity.lean`)

* `Call.nap .identity "query" {query, listType?}` → `json`. `query` is one of
  `getRelays`, `getProfile`, `getFollows`, `getList`, `getZaps`, `getMutes`,
  `getBlocked`, `getBadges`. Answer from the shell's cache or relays for the current
  user: an object with the NAP-IDENTITY primary field (`relays` NIP-65 map url →
  `{read, write}`, `profile` kind 0 fields or `null`, `pubkeys` from kind 3 / kind 10000 /
  the block list, `entries` from the NIP-51 list named by `listType`, `zaps` from kind
  9735 receipts, `badges` from NIP-58) and optionally `error` (`"relay timeout"`,
  `"not found"`, `"unsupported list type"`). The host MAY redact or empty sensitive
  lists. `identity.getPublicKey` never reaches the host: it is answered from the
  runtime's user (`HostEvent.userChanged`).

### CONFIG (`Napplet/Run/Config.lean`)

All in domain `config`.

* Effect `openSettings {window, section?, schema, values}`: open the shell's own settings
  UI for the napplet in `window` (a JSON number). `section` is present only when it is
  declared by some property's `x-napplet-section`; otherwise the UI opens at its default
  entry. `schema` is the registered schema JSON (render with the NAP-CONFIG SHOULDs:
  group by `x-napplet-section`, sort by `x-napplet-order` then key, show
  `deprecationMessage`, render `markdownDescription` as markdown and never as HTML,
  `format` only as a widget hint); `values` is the current delivered snapshot, absent if
  required properties are unresolved. The host SHOULD honour the request only when the
  napplet has (or would have) focus and SHOULD rate-limit it; it MUST mask
  `x-napplet-secret: true` fields, MUST NOT show a default for them, and SHOULD keep
  their values out of logs. Only sent when a schema is registered for the scope.
* Event `edited {window, values}`: the user committed the settings of the napplet in
  `window` (debounced, recommended ~100 ms). `values` is the full settings object (not a
  diff). The runtime drops undeclared members, persists the result for the napplet's
  scope if it yields a valid snapshot (otherwise the commit is ignored), and pushes
  `config.values` to every subscribed endpoint of that scope. The host validates input
  against the schema in its UI; this event is the only way values are ever written
  (the shell is the sole writer).

Persistence: `St.schemas` and `St.values` are persistent (keyed by scope); the host keeps
them across reloads. Secret values MAY be kept in a hardened store.

### CVM (`Napplet/Run/Cvm.lean`)

`client` is always the requesting endpoint's `Ctx.endpointId`. The host keeps one
ContextVM client signing key per `client` (fresh, ephemeral, never the user's key),
and all session state (initialisation, server-request correlation, CEP-8 payment
mode and paid authorisations) per `client` and server.

| Operation | Args (JSON) | Reply | Contract |
|---|---|---|---|
| `Call.nap .cvm "timer" {ms}` | `ms`: uint | `json {}` | Reply once, `ms` milliseconds after the call. |
| `Call.nap .cvm "discover" {query?}` | `query` = `CvmDiscoverQuery` (`kinds` already checked against `Cfg.kinds`) | `json {servers: [CvmServer]}` or `json {error}` | NAP-CVM §Discovery over CEP-6 announcements (kinds 11316–11320) and CEP-17 relay lists; honour `kinds` and `limit`; `capabilities` are MCP capability names only; `paymentRequired` per CEP-8 pricing (omit when unknown). The shell truncates to `limit` again. |
| `Call.nap .cvm "request" a` | `a` = `{client, server: CvmServerRef, message, initialize?, payment}`; `message` is the validated MCP message, a client request's `id` replaced by the transport id (an integer) | `json {message}` (the MCP response, request form only), `json {published: true}` (notification and response forms, after publication), `json {payment: offer}`, or `json {error}` | ContextVM transport (kind 25910, CEP-4 encryption when supported), signed with the client key; verify the response comes from `server` by pubkey; initialise the MCP session when needed or asked (`initialize`); negotiate CEP-8/CEP-35 `payment_interaction` per session (`payment` is the requested mode name). A CEP-8 payment gate (`-32042` or `notifications/payment_required`) for this request is not answered by the host: it replies `{payment: offer}` where `offer` has `amount` (uint, the offer's unit) and `method` (payment method id), and keeps the request open. `error` strings are NAP-CVM's (`server not found`, `initialization failed`, `payment required`, `provider unavailable`, ...). |
| `Call.nap .cvm "pay" a` | `a` = `{client, server, offer}` | as `request` | Settle exactly this offer once (CEP-8; NWC or another backend), then (transparent mode) await the original response or (explicit gating) retry the same method and params with a fresh internal id, restoring the transport id; reply as `request`. Never settle twice; never replay after an uncertain execution. |
| `Call.prompt .cvm "payment" d` | `d` = `{server, method, amount, paymentMethod, offer}` | `decision` | NAP-CVM: consent for this invocation showing server, operation, amount and payment method. |
| `Call.nap .cvm "registry.list" {query?}` | `CvmRegistryQuery` | `json {entries}` or `json {error}` | NAP-CVM §Registry; CEP-15 hashes computed and verified by the host. |
| `Call.nap .cvm "registry.has" {selector, server?}` | | `json {has: bool}` | Permitted, verified, recently reachable provider satisfies the selector and pin. |
| `Call.nap .cvm "registry.describe" {selector, server?}` | | `json {entry}` or `json {error}` | `entry` = `CvmRegistryEntry` with verified `tools[].schemaHash`; no match: `schema mismatch` (hash) / `family not found` (label). |
| `Call.nap .cvm "registry.call" a` | `a` = `{client, selector, tool, args?, server?, initialize?, payment, cache?}` | `json {result}`, `json {payment: offer}` or `json {error}` | MCP `tools/call` of `tool` on a provider of the verified hash (the pinned `server` only, if given); no substitution after dispatch; remote JSON-RPC errors become `error`; result cache keyed per NAP-CVM. |
| `Effect.nap .cvm "close" {client, server}` | | — | Release this client's session with `server` (subscriptions, initialisation, correlations, authorisations); keep shared transport only if another client uses it. No remote cancellation or refund is promised. |
| `HostEvent.nap .cvm "event" {client, server, message}` | | — | An MCP notification or server request from `server` (pubkey verified) for `client`, or a notification correlated to one of its requests. Payment control messages are not reported. |
| `Effect.cancel ⟨.cvm, n⟩` | | — | Core contract (deadline reached, close, teardown). |

### DISPLAY (`Napplet/Run/Display.lean`)

* **Configuration** (`Cfg`, not a call): `devices`, the displays the host has
  discovered at start-up, each `{id, width, height, type}` with positive
  geometry. The host MUST keep each `id` stable for the same physical display
  across listings and restarts and MUST NOT reuse it for another display; it
  SHOULD be opaque (not a hardware serial). `permitted identity displayId`, the
  per-napplet policy (default: deny everything, as upstream recommends explicit
  per-napplet permission). `maxBatch`, the largest accepted batch (default 4096
  pixels).
* `HostEvent.nap .display "devices" {displays: [{id, width, height, type, available?}]}`:
  the host's current device list after a connection change. It replaces the
  runtime's list. Entries that are not well formed (missing field, unknown
  `type`, zero width or height) are skipped. `available: false` keeps the
  display listed but makes pushes to it fail with `unavailable`.
* `Effect.nap .display "push" {displayId, pixels: [{x, y, bytes: [r, g, b]}]}`:
  an accepted batch, already validated (display exists, permitted, non-empty, at
  most `maxBatch` pixels, every coordinate in range and distinct, every byte in
  `0..255`). The host maps logical sRGB to the device (it MAY rotate, reorder scan
  lines, quantize, dither, adjust brightness or coalesce refreshes) and MUST apply
  batches for the same display in the order the effects are emitted. It never
  receives driver commands from a napplet.

### INC (`Napplet/Run/Inc.lean`)

* `HostEvent.nap .inc "revoke" {"endpoint": <endpoint id>}`: the shell's INC
  policy for that live endpoint was revoked (NAP-INC §Channel management, "ACL
  revocation"). The runtime closes every channel the endpoint is a member of,
  sending `inc.channel.closed {channelId}` to both members, and drops the
  endpoint's topic subscriptions. An unknown or non-live endpoint id has no effect.
  The endpoint id is `Ctx.endpointId` (`"endpoint-<window id>"`).

No calls or effects: INC is answered entirely inside the runtime. Policy that is not
asynchronous is in `Cfg` (`subscribeAllowed`, `openAllowed`, `maxChannels`).

### INTENT (`Napplet/Run/Intent.lean`)

* `HostEvent.nap .intent "catalog" {"entries": [Entry]}` where
  `Entry = {"id": text, "title"?: text, "z": [text], "i": [[text, ...]]}`. The complete
  installed catalog, replacing the previous one. Contract: one entry per verified
  installed NIP-5D napplet manifest (kinds 5129, 15129, 35129; signature and artifact
  verified per NIP-5D); `id` is that manifest's catalog id exactly as
  `Identity.catalogId` computes it (`nip5d:35129:<pubkey>:<d>`, `nip5d:15129:<pubkey>`,
  `nip5d:5129:<event id>`), so it equals `Ctx.catalogId` of the running napplet;
  `title` is the manifest's title, if any; `z` lists the values of its `z` tags and `i`
  the full value lists (after the tag name) of its `i` tags, in tag order. The host
  sends it at start-up and whenever the installed set changes. A malformed payload is
  ignored. The runtime pushes `intent.changed` for every role whose availability changed.
* `HostEvent.nap .intent "default" {"archetype": text, "handler": text | null}`: the user
  set (or, with `null` / absent `handler`, cleared) the default handler for an
  archetype. Contract: only the user (shell UI or settings) causes it; the value is
  persistent user preference (`Host.lean` §Persistence) and is re-sent at start-up.
  The runtime pushes `intent.changed` for that archetype if its availability changed.
* `HostEvent.nap .intent "launchFailed" {"handler": text}`: the host could not start a
  napplet for that catalog id (not installed, refused by policy, load rejected, or the
  loaded napplet does not have `intent` exposed). Terminal failure: the runtime discards
  the retained deliveries for that handler. Nothing is reported to the source.
* `Effect.nap .intent "launch" {"handler": text, "behavior"?: {"focus"?: bool, "reuse"?: bool}}`:
  start the napplet whose verified catalog id is `handler`, through the ordinary NIP-5D
  load (`Input.create` … `Input.hello`), honouring `behavior` as hints. Emitted once per
  handler while deliveries for it are retained. Once the napplet is bound with `intent`
  exposed, the runtime delivers. If it cannot be started, the host sends `launchFailed`.
* `Effect.nap .intent "focus" {"window": number}`: `behavior.focus` was `true` and the
  delivery went to the already running napplet in that window; bring its surface
  forward if workspace policy allows. A hint; ignoring it is valid.
* `Call.prompt .intent "choose" {"sender": text, "archetype": text, "action": text,
  "convention": text, "candidates": [IntentCandidate]}` → `Reply.decision allowed choice`.
  Ask the user to pick a handler among `candidates` (NAP-INTENT `IntentCandidate`
  JSON). `allowed = true` with `choice = some <candidate id>` selects it; `allowed =
  false` or no choice means cancelled (`"user cancelled"`). A choice that is no longer a
  compatible candidate when the reply arrives yields `"invoke rejected"`.
* `Call.prompt .intent "authorize" {"sender": text, "handler": text, "archetype": text,
  "action": text, "convention": text}` → `Reply.decision allowed _`. Ask the user whether
  the source (`sender`, its catalog id) may address the installed handler `handler`
  explicitly (NAP-INTENT: "MUST NOT let a caller address a handler instance unless the
  user explicitly authorized that handler"). The host may answer from a rule the user
  configured. `allowed = false` yields `"invoke rejected"`.

A prompt reply other than `decision` counts as a refusal / cancellation. Prompts of a
torn-down source are cancelled with `Effect.cancel`.

### KEYS (`Napplet/Run/Keys.lean`)

All host-facing arguments name the endpoint by `port` (the `PortId` of the bound
port, which the host learned from `Output.bound`).

* `Effect.nap .keys "input" {port, key, code, ctrl, alt, shift, meta}`: a keystroke
  the napplet forwarded. The host processes it as if it occurred in the shell's own
  context (global hotkeys, command palette, workspace switching). It MUST NOT
  deliver it to any napplet. Fields are those of the wire message
  (`KeyboardEvent.key`, `KeyboardEvent.code`, modifier flags).
* `Effect.nap .keys "bindings" {port, actions: [{actionId, label, key?}]}`: the
  complete list of actions this endpoint has registered, with the current canonical
  combo for bound ones. Emitted whenever it changes and on teardown (then empty).
  The host shows labels in its own UI (keymap editor, command palette) and listens
  for the bound combos in its own context.
* `HostEvent.nap .keys "combo" {key}`: the user pressed combo `key` in the shell's own
  context (or a global hotkey fired). The runtime sends `keys.action` to the owner
  of the binding for that combo, if any.
* `HostEvent.nap .keys "trigger" {port, actionId}`: the user invoked an action from
  shell UI (for example a command palette). Sent as `keys.action` if that endpoint
  has registered the action.
* `HostEvent.nap .keys "rebind" {port, actionId, key}`: the user changed the binding of
  a registered action; `key` is a combo string, or `null` to unbind. A combo that is
  unparseable, reserved, or bound by any action is refused (nothing changes);
  otherwise the binding changes and the owner gets the new `keys.bindings`.

### LINK (`Napplet/Run/Link.lean`)

* `Call.prompt .link "open" {url, host?, label?, napplet}` → `Reply.decision allowed choice`.
  Ask the user whether to open `url`. The prompt MUST show the napplet
  (`napplet` is its catalog identifier `Ctx.catalogId`; show its name and author
  when known), the destination `url` and hostname `host` (treat IDN, punycode and
  lookalike hostnames as phishing risks), and MAY show `label`, marked as text
  supplied by the napplet. Choices: `choice` `"once"` (or absent) applies to this
  request only; `"napplet"` persists the answer for every link from this napplet;
  `"host"` (allow only) persists allow for links to this hostname from this
  napplet; `"url"` persists the answer for this exact URL from this napplet.
  Any other reply is treated as a refusal by policy (`blocked-by-policy`).
* `Effect.nap .link "open" {url}`: open `url` for the user outside the napplet
  sandbox (new tab, external browser, in-shell browser or native handler, the
  host's choice) with `noopener` (HTML `rel=noopener` / `window.open(url, "_blank",
  "noopener")`) or an equivalent: the opened context MUST NOT get `window.opener`
  or any other reference back to the napplet. The model only emits it for URLs
  that passed steps 1–2 and either a persisted allow rule or the user's approval.
* `Effect.cancel tag`: withdraw an outstanding prompt (endpoint torn down).

### MEDIA (`Napplet/Run/Media.lean`)

All are in domain `media`. `sessionId` is always the canonical id; `window` is the
endpoint's `WindowId` (JSON number). Numbers are JSON numbers. A `MediaState` object is
`{status, position?, duration?, volume?, reason?}` as in NAP-MEDIA.

Effects (`Effect.nap .media op args`, fire-and-forget):

* `open {sessionId, window, source, metadata?, context?, autoplay?, live?}`: start a
  **shell-owned** session. The host resolves `source` (`MediaSourceRef`: `url`,
  `blossomHash` per BUD-10 from servers it chooses, `nostr` event/address one NIP-19 hop)
  and fetches the bytes under the NAP-RESOURCE policy (private-address block at DNS
  resolution, MIME byte sniffing); it never gives the bytes to the napplet. It shows the
  session on its media surface with `metadata`; artwork is fetched only through that same
  policy. It starts output only if `autoplay` is `true` and its autoplay and audio-focus
  policy allow it. It then reports through the `state` and `capabilities` events below;
  if the source cannot be played it stops and sends `retire` with reason `error`.
* `register {sessionId, window, metadata?, context?, capabilities}`: show a
  **napplet-owned** session on the media surface (metadata, media keys, OS integration).
  No source is passed; the host MUST NOT fetch or play anything for it.
* `update {sessionId, metadata}`: merge `metadata` (a partial `MediaMetadata`) into the
  displayed metadata; only the given fields change.
* `state {sessionId, status, position?, duration?, volume?, reason?}`: a napplet-owned
  session's reported state, for display (out-of-range numbers already removed).
* `capabilities {sessionId, actions}`: a napplet-owned session's supported actions; the
  host enables only these controls for it.
* `command {sessionId, action, value?, reason}`: perform `action` on a **shell-owned**
  session's backend (`value`: seek position in seconds, or volume 0–1). The runtime has
  checked that the action was exposed and its value is in range; the backend still
  applies its policy (it MAY ignore `seek` on live sources and `next`/`prev` without a
  queue) and reports the outcome through the `state` event. With reason `focus-lost` or
  `focus-gained` it is the runtime's audio-focus decision; the runtime has already sent
  the corresponding `media.state`, so the host need not report that transition again.
* `close {sessionId, reason}`: stop the session's output and remove it from the media
  surface, before the runtime sends `media.session.ended` (shell-owned: stop and release
  the backend; napplet-owned: revoke the frame's output authority, for example by muting
  it, when `reason` is `policy`). Sent on destroy (`destroyed`), on focus loss of a
  napplet-owned session that cannot pause (`policy`) and on endpoint teardown
  (`destroyed`, with no `ended`). This model does not promote sessions to persistent
  playback; teardown always stops shell-owned output.

Events (`HostEvent.nap .media ev args`):

* `state {sessionId, status, position?, duration?, volume?, reason?}`: a **shell-owned**
  backend's state change (buffering, position, natural end as `stopped`/`ended`, user
  action in the shell's own player as reason `user`, failure as `error`). Forwarded as
  `media.state`. Ignored for napplet-owned sessions.
* `capabilities {sessionId, actions}`: a shell-owned backend's supported actions;
  forwarded as `media.capabilities`.
* `controls {sessionId, controls}`: the shell's control list for a session; forwarded as
  `media.controls`.
* `command {sessionId, action, value?, reason?}`: the user used a shell control on a
  **napplet-owned** session. Forwarded as `media.command` only if the action is in the
  session's current capabilities and `seek`/`volume` carry a valid `value`.
* `focusLost {sessionId}`, `focusGained {sessionId}`: the host's audio-focus decision for
  one session (NAP-MEDIA §Temporary audio-focus loss). The runtime decides what is sent.
* `retire {sessionId, reason}`: the host has already stopped the session's output and
  retires it (`preempted`, `ended`, `error`, `backend-exited`, `user`, `policy`; an
  unknown reason is treated as `policy`). The runtime sends the one `media.session.ended`.

Events naming an unknown or retired `sessionId` are ignored.

### NOTIFY (`Napplet/Run/Notify.lean`)

`port` is the endpoint's `PortId` (from `Output.bound`); `napplet` is its catalog id
(`Ctx.catalogId`), for attribution.

* `Effect.nap .notify "show" {notificationId, port, napplet, title, body?, icon?,
  actions: [{id, label}], channel?, priority}`: render a notification in shell UI
  (toast, system notification, notification centre). The host MUST render `title`,
  `body` and labels as plain text, never markup, MUST visibly attribute it to the
  napplet, SHOULD honour `priority` (`low`, `normal`, `high`, `urgent`) and its
  per-channel user settings, and fetches `icon` only under its own resource policy.
* `Effect.nap .notify "hide" {notificationId}`: remove that notification from shell UI.
* `Effect.nap .notify "badge" {port, count}`: show `count` on the napplet's tile, tab
  or icon; `0` clears it.
* `Effect.nap .notify "channel.register" {port, napplet, channelId, label,
  description?, defaultPriority?}`: record a channel the user can configure
  (mute, priority) for this napplet; the host MAY ignore channels.
* `Call.prompt .notify "permission" {port, napplet, channel?}`, reply `decision allowed _`:
  ask the user whether this napplet may show notifications (for `channel`, when
  given). Any other reply counts as a refusal. The prompt MUST NOT block other inputs.
* `HostEvent.nap .notify "clicked" {notificationId}`: the user clicked the body.
* `HostEvent.nap .notify "action" {notificationId, actionId}`: the user clicked an
  action button (ignored unless `actionId` is one of that notification's actions).
* `HostEvent.nap .notify "dismissed" {notificationId, reason?}`: the notification left
  the screen (`reason` one of `user`, `timeout`, `replaced`; anything else is
  dropped). The runtime forgets it.

Events for ids the runtime does not hold are ignored.

### OUTBOX (`Napplet/Run/Outbox.lean`)

Only core host calls; no `Call.nap`, `Effect.nap`, `HostEvent.nap` or `Call.prompt`.

* `Call.relayList pubkey` → `relayList (some entries)` / `relayList none` (NIP-65 kind
  10002, from cache or relays).
* `Call.subscribe filters relays` → stream `event ev relay`, `eose`, `closed reason?`;
  stopped with `Effect.unsubscribe`.
* `Call.sign unsigned` → `signed (some ev)` / `signed none` (refused: `"publish denied"`).
* `Call.publish ev (some relays)` → `published acks` (one `(relay, accepted)` per relay;
  becomes the `relays` map; `ok` iff some relay accepted, else `"publish failed"`).
* `Effect.unsubscribe`, `Effect.cancel` on EOSE, close, replacement and teardown.

### POW (`Napplet/Run/Pow.lean`)

| Operation | Args (JSON) | Reply | Contract |
|---|---|---|---|
| `Call.nap .pow "mine" a` | `a` = `{pubkey, created_at, kind, content, tags, target, workers, timeoutMs?, commitCreatedAt}`; `tags` are the template's tags (any `nonce` tag is replaced by the miner) | `json {nonce: tstr, hashes: uint, elapsedMs: uint, created_at?: uint}` or `json {error: tstr}` | NIP-13: find a nonce `n` such that the NIP-01 id of `{pubkey, created_at, kind, content, tags'}` with `tags' = tags` minus `nonce` tags `++ [["nonce", n, toString target]]` has at least `target` leading zero bits, using at most `workers` workers. With `commitCreatedAt = false` the miner MAY advance `created_at` and then reports the value it used in `created_at`; otherwise `created_at` is fixed. `timeoutMs` bounds mining time only; on expiry reply `{error: "timeout"}`. Progress is reported with the `progress` event below, throttled to a few per second. |
| `Effect.nap .pow "pause" {call}` | `call` = the tag number `n` of the `mine` call | — | Suspend that search, keeping its best nonce and hash counters. |
| `Effect.nap .pow "resume" {call}` | as above | — | Continue a suspended search. |
| `HostEvent.nap .pow "progress" a` | `a` = `{call, bestPow, bestNonce?, hashes, hashRate, workers: [{workerId, bestPow, hashes, hashRate}], elapsedMs}` | — | Progress of the `mine` call `call` (numbers as NAP-POW `PowProgress`; `hashRate` any JSON number). |
| `Call.nap .pow "wake" {}` | `{}` | `json {}` | Reply promptly; lets the queue advance after a teardown freed a mining slot. |
| `Call.prompt .pow "publish" d` | `d` = `{jobId, event}` (the committed unsigned event with its id) | `decision` | Same publish consent as NAP-OUTBOX `publish`. Anything but `decision true _` refuses (`"publish denied"`). |
| `Call.sign ev` | the committed event | `signed` | Core contract. The shell rejects (`"publish denied"`) a signed event whose committed fields differ. |
| `Call.publish ev none` | the signed event | `published acks` | Core contract; the host selects relays outbox-aware (user's NIP-65 write relays plus the inbox relays of tagged recipients), as NAP-OUTBOX `publish`. |
| `Effect.cancel ⟨.pow, n⟩` | — | — | Core contract; on `pow.cancel` and on teardown. |

`Host.crypto.sha256` (FIPS 180-4) is applied to the UTF-8 bytes of the NIP-01
serialisation `[0, pubkey, created_at, kind, tags, content]` printed by
`Json.render` (`JSON.stringify` escaping, as NIP-01 prescribes).

### RELAY (`Napplet/Run/Relay.lean`)

This component uses only core host calls; it adds no `Call.nap`, `Effect.nap`,
`HostEvent.nap` or `Call.prompt`.

* `Call.subscribe filters relays` (subscribe: `relays = some [relay]` when the napplet
  scoped it, else `none` = the shell's pool; query: `none`). Stream replies under one tag:
  `event ev relay` (signature already verified, NIP-01), one `eose`, `closed reason?`.
  Stopped with `Effect.unsubscribe`.
* `Call.sign unsigned` → `signed (some ev)` / `signed none`.
* `Call.encrypt scheme recipient plaintext` → `text (some ciphertext)` / `text none`
  (NIP-44 v2 or NIP-04; never another scheme).
* `Call.decrypt scheme ev` → `text (some plaintext)` / `text none`.
* `Call.publish ev none` → `published acks`; the result is `ok: true` iff some relay
  accepted, else `ok: false, error: "publish failed"`.
* `Effect.unsubscribe tag`, `Effect.cancel tag` on close, replacement and teardown.

### RESOURCE (`Napplet/Run/Resource.lean`)

* `Call.fetch url` → `Reply.fetched o` (`NapResource.FetchOutcome`), or
  `Reply.json {error, message?}` for failures `FetchOutcome` cannot express.
  `url` is a napplet URL after the `nhash` alias rewrite; `data:` is never sent.
  Contract (in addition to `Call.fetch` in `Napplet.Host`): resolve `https:` with
  DNS; `blossom:` per BUD-10 from servers the host chooses, treating `xs`/`as`/`sz`
  hints as advisory and fetching upstream hosts under `https:` policy; `nostr:` by
  one NIP-19 hop, never following URLs or `nostr:` references in the result;
  `hashtree:`/`htree:` per HTS-01 (§6.2–6.3 `nhash` TLV fields, §9 `htree` URL
  profile, URL-ENCODING segment rules), verifying the root, nodes, chunks and CHK
  decryption, and never sending `#k=` secrets or keys to relays, storage servers,
  FIPS peers or HTTP bodies. Report every address connected to in `o.hops`, in
  order (private-address checks happen after DNS and before connecting, so the
  host MUST refuse to connect to an address `NapResource.isPrivate` classifies as
  private and report it as a hop); stop after `Cfg.pol.maxRedirects` redirects;
  set `o.timedOut` after `Cfg.timeoutSecs` (recommended 30 s) per URL; `o.body`
  is the complete response body or `none` when the resource does not exist.
  `o.upstreamType` is never used. `Reply.json` `error` is one of the NAP-RESOURCE
  codes: `network-error` (DNS, TCP, TLS or upstream failure), `invalid-request`
  (an `nhash` whose TLV fields are invalid, an unresolvable `self`/petname, or a
  Hashtree directory), `decode-failed` (Hashtree hash or key mismatch),
  `blocked-by-policy`, `not-found`, `timeout`, `too-large`; `message` is
  diagnostic text passed to the napplet. Any other reply is `network-error`.
* `Effect.cancel tag`: abandon a fetch whose request was cancelled or whose
  endpoint was torn down.
* Pure host functions used: `Host.crypto.sha256` (Blossom hash check),
  `Host.sniff` (MIME, WHATWG MIME Sniffing over the bytes only), `Host.rasterize`
  (SVG to PNG/WebP in an isolated, network-less context within 5 MiB input,
  4096 × 4096 output and 2 s).

### UPLOAD (`Napplet/Run/Upload.lean`)

* `Call.prompt .upload "upload" {napplet, rail, server, size, mimeType, filename?,
  data}` → `Reply.decision allowed _`. First-upload consent for this napplet. The
  prompt MUST show the requesting napplet (`napplet` = `Ctx.catalogId`), the file
  type, size and target server, SHOULD let the user inspect `data` (byte array) and
  SHOULD say the upload will be public and durable. Any non-`decision` reply is a
  refusal.
* `Call.sign ev` (core): the rail authorisation. `ev` is the template built by
  `authTemplate`; the reply must satisfy `Call.sign`'s contract.
* `Call.nap .upload "put" {call, server, rail, auth, data, sha256, size, mimeType,
  filename?, caption?, noTransform, metadata?}` → `Reply.json`. Send `data` (byte
  array) to `server` over `rail`: for `nip96` a NIP-96 upload (`POST` to `server`,
  the configured NIP-96 `api_url`, with the NIP-98 `Authorization: Nostr <base64
  of auth>` header, `no_transform` form field from `noTransform`, `caption`,
  `content_type`); for `blossom` a BUD-02 `PUT <server>/upload` with the kind 24242
  `auth` in `Authorization: Nostr …`; for other rails the host's own protocol
  (`auth` is `null`). `sha256` is the shell's hash of `data`; `call` is the call
  tag number, used by `progress` events. Reply: on success `{ok: true, url,
  sha256, originalSha256?, size?, mimeType?, dimensions?: {width, height},
  blurhash?, fallbackUrls?}` where `sha256` is the server-reported hash of the
  stored file (Blossom descriptor `sha256`, NIP-96 `x`) and `originalSha256` the
  server-reported hash of the received bytes when it transformed them (NIP-96 `ox`);
  `url`/`fallbackUrls` are where the server says it stored the file (the host MAY
  upload to mirrors and list them). On failure `{ok: false, error?}` with `error`
  one of upstream's strings (`"server rejected"`, `"upload failed"`,
  `"quota exceeded"`, …). The host MUST NOT report `ok: true` unless the server
  confirmed storage.
* `HostEvent.nap .upload "progress" {call, bytesSent, bytesTotal}`: progress of the
  `put` with tag number `call`; pushed to the napplet as `upload.status.changed` once
  the initial result went out.
* `Effect.cancel tag`: abandon an outstanding prompt, signature or `put` when the
  endpoint is torn down.
* Pure host functions used: `Host.crypto.sha256` (FIPS 180-4), `Host.sniff`,
  `Host.transform`, `Host.verifyEvent`.

### VALUE (`Napplet/Run/Value.lean`)

| Operation | Args (JSON) | Reply | Contract |
|---|---|---|---|
| `Call.prompt .value "send" d` | `d` = the `ValueRequest` JSON (`rail`, `amountMsat`, `target`, `comment?`, `metadata?`) plus `transferId` | `decision allowed _` | NAP-VALUE consent: the host shows amount, rail, target and recipient identity, comment, metadata and the requesting napplet's verified identity. Any reply other than `decision true _` is a refusal. |
| `Call.sign ev` | kind 9734 `UnsignedEvent` built by `zapRequest` | `signed` | Core `Call.sign` contract (NIP-01 / BIP-340). |
| `Call.nap .value "quote" a` | `a` = `ValueRequest` JSON | `json {feesMsat?: uint, expiresAt?: uint, error?: tstr}` | Best-effort, MUST NOT move money or sign anything. MAY resolve LNURL-pay (LUD-06/LUD-16) to validate payability and estimate fees. `error` uses the NAP-VALUE error strings. |
| `Call.nap .value "pay" a` | `a` = `{transferId, rail, amountMsat, target, comment?, metadata?, zapRequest?}`; `zapRequest` is the signed kind 9734 event (zap rail only) | `json {status: "pending"\|"settled"\|"failed", preimage?: tstr, event?: NostrEvent, error?: tstr}` | Pay exactly `amountMsat` once. `zap`: NIP-57 (resolve the recipient's LNURL-pay endpoint from their kind 0 `lud16`/`lud06`, request an invoice with `nostr=<zapRequest>` and `amount`, check the invoice amount, pay). `lnurl`: LNURL-pay (LUD-06/LUD-16) to `target.lnurl`. Payment through NWC (NIP-47) or an internal wallet. `settled` only on backend confirmation, with the `preimage`; `event` is a NIP-57 zap receipt (kind 9735) when observed. Credentials never leave the host. Cancelling the call (`Effect.cancel`) does not promise a refund. |
| `HostEvent.nap .value "status" a` | `a` = `{transferId, status, preimage?, event?, error?}` | — | Later settlement news for a transfer the host was asked to pay (for example a zap receipt observed on relays). Same meaning as the `pay` reply. |
| `Effect.cancel ⟨.value, n⟩` | — | — | Core contract; issued on endpoint teardown for every outstanding call. |


-/

end Napplet
