# Audit: Hypergolic against the Lean model

- **Audited:** [nostrocket/hypergolic](https://github.com/nostrocket/hypergolic) at commit
  `0b00b23e9c4c385f16d62833f9743eafb98ef744` (`main`, "Merge pull request #96").
- **Model:** this repository's `lean/` at the commit that adds this file.
- **Date:** 2026-11-22.
- **Checkout:** cloned to `/Users/gareth/git/napplets/hypergolic`. Nothing there was committed or
  pushed, and no issue or PR was opened. One test file was added to `runtime/tests/` for a single
  run and then deleted.
- **Evidence:** every script and probe used is in [`hypergolic/`](hypergolic/), next to this file.

## Summary

Hypergolic is a careful shell, but it does not implement the NIP-5D transport:

- There is no `napplet.hello` and no `MessageChannel` port.
- Every NAP message in both directions travels over `window.postMessage`.
- The binding is to the iframe's `WindowProxy`.

That single design choice breaks NIP-5D rows 2, 4, 5, 9, 21, 23 and 28 (finding NIP5D-1). Every
trace in `lean/traces/` therefore differs from step 3 onward.

Below the transport, the most serious confirmed breaks are:

- **RELAY-1 / OUTBOX-1.** Napplet-supplied NIP-04 and NIP-44 ciphertext is signed and published
  once the user approves it.
- **RELAY-2.** Incoming encrypted events are delivered raw, or they kill the subscription.
- **INC-1.** The INC `sender` is the bare `d` tag, so two publishers cannot be told apart.
- **CONFIG-1 / CONFIG-2.** CONFIG schemas are held per window, and defaults are persisted as if
  the user had chosen them.
- **IDENTITY-1.** `identity.getPublicKey` can go unanswered, or return `""` while a user is signed
  in.
- **RESOURCE-1.** The RESOURCE `blob` field carries a host `Blob` instead of base64.
- **INTENT-1.** `intent.launch` gets no reply.

Many lower findings share one cause. Hypergolic validates strictly and drops a request it cannot
parse without replying, where decision 31 requires an error result for any known type that has a
string `id`.

What holds up:

- **Address blocking:** private addresses are blocked on every redirect hop and after DNS, on both
  platforms.
- **MIME:** types are sniffed from the bytes.
- **Notifications:** only the creating napplet can dismiss a notification.
- **Links:** only `https:` opens, and only after a prompt.
- **Late replies:** they are dropped after teardown.
- **Document building:** the CSP comes first and the bootstrap runs before any napplet script, on
  every document Hypergolic accepts.

Findings by severity:

| Severity | Count | IDs |
|---|---|---|
| Critical | 1 | RELAY-1 (with OUTBOX-1 as its twin) |
| High | 10 | NIP5D-1, OUTBOX-1, RELAY-2, CONFIG-1, CONFIG-2, IDENTITY-1, INC-1, INTENT-1, INTENT-2, RESOURCE-1 |
| Medium | 28 | see below |
| Low | 29 | see below |

## Architecture map

| Concern | Where in Hypergolic | Notes against the web projection the model assumes |
|---|---|---|
| WebView | Android `WebView` and iOS `WKWebView` load the packaged trusted document `runtime/dist/index.html` (built from `runtime/src/main.ts`). Android serves it from the app-assets HTTPS origin; iOS uses an isolated WebKit content world. | The model's "shell page" is this packaged document, not a browser tab. Native code talks to it through `HypergolicHost.postMessage` (`runtime/src/native-client.ts`). |
| Napplet frame | `createGuestFrame`, `runtime/src/main.ts:200-213`: `sandbox="allow-scripts"`, `referrerpolicy=no-referrer` and an `allow` list that denies camera, microphone and similar. | Meets NIP-5D rows 7 and 8: no `allow-same-origin`. |
| Manifest and artifact verification | `src/napplets/verified-artifact.ts`. `authenticateManifestEvent` (`:140-170`) recomputes the event id, checks the Schnorr signature and binds kind, pubkey and `d`. `verifyManifest` (`:173-223`) and `verifyArtifact` (`:323-353`) check SHA-256 of the HTML and a strict HTML envelope. Native staging rechecks the bytes in `runtime/src/published-artifact.ts:66-112`. | Accepts kinds 35129 and 5129 only; root kind 15129 is unsupported. Also accepts a NIP-5A "legacy-path" format (finding NIP5D-2). |
| Identity | `{dTag: appId, aggregateHash}` is registered with Kehto's `originRegistry` against `frame.contentWindow` (`main.ts:227,240`). `aggregateHash = sha256("<htmlHash> /index.html\n")`. | Model: `Identity` = (`dTag`, `artifactHash`, publisher, kind, event id), bound to a port. Hypergolic binds to a `WindowProxy`, and its Kehto identity has no publisher (see INC-1). |
| Document building | `renderGuest`, `main.ts:366-389`: `publishedCspParts` (`published-artifact.ts:126-129`, using `src/napplets/html-envelope.ts`) puts the CSP after the `<head>` start tag. Shell scripts, then Kehto's `injectNappletNamespacePrelude` (which installs `window.napplet`), are inserted right after the CSP meta. | Model: `Bootstrap.srcdoc` / `Srcdoc.buildSrcdoc`. Hypergolic refuses documents without `<!doctype html><html><head>` (SRCDOC-1). |
| Bootstrap and binding | Kehto's `nappletNamespacePrelude` (`@kehto/shell` 0.20.0 `dist/index.js:1313ff`) uses `window.parent.postMessage` and listens on `window`. Handshake: guest sends `shell.ready`, shell answers `shell.init` (`dist/index.js:1176-1183,1232`). | No `MessageChannel`, no `napplet.hello` (NIP5D-1). |
| Ingress and routing | `window` `message` listener → `guestMessageReceiver` (`runtime/src/guest-message-receiver.ts`: source check, 64 messages/s rate limit, `keys.*` / `media.*` / `cvm.*` side lanes) → `validEnvelope` / `rejectEnvelope` (`runtime/src/guest-envelope.ts`) → Kehto `bridge.handleMessage` (session, ACL and domain gate) → `operationOverrides` (`main.ts:181-197`) → `native-client.ts` → native module (`modules/napplet-host/{android,ios}`) → React Native brokers in `src/` (`src/runtime/capability-broker.ts`, `src/network`, `src/outbox`, `src/resources`, `src/uploads`, `src/routing`, `src/presentation`, `src/cvm`, `src/links`). | Every reply is posted with `source.postMessage(msg, '*')`. |
| Storage and persistence | SQLite (`src/storage/schema.ts`): `saved_strings` is keyed by (user, publisher, app, version, scope, instance). Also `access_grants` (domain consent), `workspaces` and `app_versions`. Configuration lives in a native encrypted record per (identity, publisher, app, aggregate hash), `src/presentation/config-store.ts`. Intent catalog and defaults are per identity (`docs/intent-inc.md`). Notify permissions are in `hypergolic-notify-v1.db`. | Compared with `Persist.Persisted` in Check 5. |
| Signer | `src/security/approval-service.ts` → `event-snapshot.ts` → native signer core (`modules/signer-core`): a local key, NIP-46 or NIP-55. The user reviews each event. | No ciphertext test before signing (RELAY-1). |
| Relays | `relay.*` and `outbox.*` → `native-client.ts` streams → native relay pool → `src/network/relay-*.ts` and `src/outbox/*`. | Scoped relay URLs: `wss://` only, no IP literals and no local names. |
| Wallet | None. NAP-VALUE is absent, and CVM is a free-only profile with no payments. | |
| Mobile-specific | A `WebView` reload, backgrounding or app restart tears the session down (`pagehide` → `stop()`, `main.ts:76`). Native leases are tied to a per-generation `sessionId`. | Each case is in Check 6. |

## Coverage

"Partial" means implemented with divergences or missing message types; each is listed under
Findings. Domains outside the model (`lists`, `common`, `mesh`) are not audited.

| NAP | Status | Notes |
|---|---|---|
| NIP-5D core | Partial | Manifest, hash and sandbox checks are present. The port transport is absent (NIP5D-1). Kind 15129 is absent. |
| SHELL | Partial | `shell.init` is pushed by Kehto in reply to `shell.ready`, not to `napplet.hello`. `shell.check` and `shell.domains` (PR #142) are absent. |
| THEME | Implemented | `theme.get`, `theme.changed` |
| IDENTITY | Partial | All 9 queries are present. `identity.changed` is absent: `publishIdentityChanged` is never called. |
| STORAGE | Implemented | Limits and error strings differ. |
| RELAY | Partial | `publishEncrypted` is absent but still advertised. No decryption. `close` sends no reply. |
| OUTBOX | Partial | `close` sends no reply. Error results from `resolveRelays` carry no `plan`. |
| RESOURCE | Partial | The `blob` wire form is wrong. `hashtree:`, `htree:`, `nhash` and `http:` are absent. |
| UPLOAD | Partial | Blossom only. Uses a `pending` result plus push instead of `complete`. |
| INTENT | Partial | `launch` and `handlerHint` are absent. Selected-instance replay is absent (no host hook). |
| INC | Implemented | All 8 requests and 7 pushes, with identifier divergences. |
| NOTIFY | Implemented | |
| CONFIG | Implemented | Several schema and persistence divergences. |
| LINK | Implemented | `https:` only. Every link prompts; no rules are saved. |
| KEYS | Partial | `keys.forward` is a no-op and `keys.action` is never sent. |
| MEDIA | Partial | Shell-owned `http(s)` sessions only. `session.update`, napplet-owned sessions and `media.controls` are absent. |
| CVM | Partial | `request` and `close` work. `discover` and the registry answer "unsupported method". There are no payments. |
| VALUE | Absent | grep: 0 hits for `value.*` wire types |
| POW | Absent | grep: 0 hits |
| DISPLAY | Absent | grep: 0 hits |

## Findings

Each finding has:
- an id and severity;
- the spec text (an upstream quote, or the row in `lean/conformance/`);
- the Lean reference;
- the Hypergolic `file:line`, relative to the Hypergolic root;
- how to reproduce it, and the expected and actual behaviour;
- a suggested fix;
- a class: **Bug** (a Hypergolic bug), **Silent (decision N)** (the spec is silent and the model
  chose otherwise) or **N/A mobile** (the mobile projection makes the rule inapplicable).

"Probe" names a script under [`hypergolic/`](hypergolic/). How to run each one is in the
Reproduction section.

### Critical

**RELAY-1: Napplet-supplied ciphertext is signed and published.**
- **Spec:** NIP-5D Security 7, "Shells MUST NOT sign or broadcast events containing ciphertext
  received from a napplet" (NIP-5D row 75).
- **Lean:** `Run/Relay.lean:316,323` (`looksCiphertext` → `"blocked: ciphertext from napplet"`);
  `handle_sign` `:546`; decision 11; trace `relay-ciphertext` step 4.
- **Hypergolic:** no content check on the path `runtime/src/guest-envelope.ts:69-80` →
  `src/security/approval-service.ts` (`enqueue`) → `src/security/event-snapshot.ts:52-76` → signer.
- **Reproduction:** probe `relay/cipher.test.mts`. It sends `relay.publish` with kind 4 and content
  `aGVsbG8gd29ybGQ=?iv=AAAA…==` (NIP-04 form), and also a NIP-44 v2-shaped payload, then approves.
- **Expected:** `relay.publish.result {ok:false, error:"blocked: ciphertext from napplet"}`, with no
  signing.
- **Actual:** `nip04 kind4 SIGNED … published= 1 reply.ok= true`, and the same for NIP-44. Rerun
  and confirmed for this report.
- **Fix:** test the napplet-supplied content (NIP-04 `?iv=` form; NIP-44 version byte plus base64)
  at admission, before `enqueue` and before any approval UI.
- **Class:** Bug. The approval prompt does not mitigate it: the MUST NOT does not depend on the
  user's consent.

### High

**NIP5D-1: No MessageChannel transport. NAP messages travel over `window.postMessage`, and the
binding is to a `WindowProxy`.**
- **Spec:** NIP-5D row 2: the bootstrap "MUST … create a `MessageChannel` … and transfer the other
  port to the shell exactly once". Row 4: "All NAP messages in both directions MUST be carried over
  the port". Row 5: "Shells MUST NOT send NAP messages via `iframeWindow.postMessage`". Rows 9, 21
  and 23 (one `napplet.hello` with exactly one port) and row 28 (NAP messages only from the bound
  port).
- **Lean:** `Shell.lean:131-160` (`hello` with `[p]` only); `nap_dispatch_requires_binding`;
  `Runtime.lean:157` (`Output.send p` is the only reply channel); `message_unbound_silent`;
  `Binding.boot_once`; `Bootstrap.bootstrapJs`.
- **Hypergolic:**
  - `runtime/src/main.ts:240` binds the identity to `frame.contentWindow`.
  - `runtime/src/guest-message-receiver.ts:22` accepts by `event.source`.
  - Replies are posted to the frame window at `runtime/src/guest-envelope.ts:92,99,108,112,120`,
    `runtime/src/main.ts:294-295`, and `@kehto/shell` 0.20.0 `dist/index.js:1182` (`shell.init`)
    and `:1213` (theme and identity broadcasts).
  - The guest prelude posts to `window.parent` (`dist/index.js:1329-1330`).
- **Reproduction:**
  - `grep -rn "napplet.hello" src runtime/src modules docs runtime/node_modules/@kehto runtime/node_modules/@napplet`
    gives 0 hits.
  - The ingress adapter (`core/ingress.ts`) finds 51 `hello` and 5 `portClosed` trace inputs with
    no Hypergolic counterpart.
  - Every trace's step 2 (`bound`) has no Hypergolic equivalent.
- **Expected:** the shell binds `(dTag, artifactHash)` to the one port in the first `napplet.hello`
  and talks only over that port.
- **Actual:** it binds to the window and talks over window messages.
- **Mitigations present:**
  - A second frame `load`, nested frames, or a message from another source tears the session down
    (`main.ts:253-285`).
  - Probe `core/zz-audit-navigation.spec.ts` navigated the napplet to a `data:` document. The
    session was revoked (`frame-navigation`), and the new document's `theme.get` was not
    answered.
  - So the property port binding protects was not shown to fail. The wire contract is still
    broken.
- **Fix:** adopt the NIP-5D bootstrap. Kehto itself already transfers a `MessageChannel` port for
  intent delivery (`dist/index.js:2399-2413`), so the WebViews support it.
- **Class:** Bug. Not N/A mobile: Android `WebView` and `WKWebView` both support `MessageChannel`
  and transferable ports between frames inside the document.

**OUTBOX-1: Same ciphertext gap on `outbox.publish`.**
- **Spec:** as RELAY-1.
- **Lean:** `Run/Outbox.lean:469,554`, `handle_sign` `:931`.
- **Hypergolic:** `src/outbox/publication-contract.ts:20-33` → `src/outbox/approval-preparation.ts`
  → the same signer path.
- **Reproduction:** probe `relay/stream.test.mts` (bundled; see Reproduction) prints
  `outbox.publish cipher ACCEPTED content= aGVsbG8=?iv=…`.
- **Expected:** `ok:false`, `"blocked: ciphertext from napplet"`.
- **Actual:** the request enters the signing pipeline.
- **Fix:** as RELAY-1.
- **Class:** Bug. (Severity is High rather than Critical only because it was traced to admission,
  not to a published event.)

**RELAY-2: Incoming encrypted events are not decrypted.**
- **Spec:** "The shell MUST decrypt incoming encrypted events (NIP-04/NIP-44) before delivering
  them" (NAP-RELAY row 27).
- **Lean:** `onReply_delivers_plaintext` (`Run/Relay.lean:672`); `undecryptable_not_delivered`.
- **Hypergolic, three paths:**
  - (a) `relay.query` accepts `kinds:[4]` (`src/network/relay-query-contract.ts:83-89`) and returns
    events unchanged (`src/runtime/capability-broker.ts:63`).
  - (b) A subscription that receives a kind 4 or 1059 event throws at `runtime/src/native-client.ts:57`
    and is closed.
  - (c) `outbox.query` uses the same query path (`src/outbox/query-contract.ts:52-73`,
    `read-service.ts:100`). This one was traced in the code only.
- **Reproduction:**
  - (a) Probe `relay/query.test.mts` prints
    `relay.query kinds:[4] accepted; delivered 1 event(s); kind 4 content= aGVsbG8gd29ybGQ=?iv=…`.
  - (b) Probe `relay/stream.test.mts` prints
    `kind4 event on authors sub -> [{"type":"relay.closed",…,"reason":"relay subscription unavailable"}]`;
    the plaintext event sent next is lost.
- **Expected:** plaintext delivered, or the one undecryptable event dropped.
- **Actual:** raw ciphertext is delivered, or the stream dies.
- **Fix:** decrypt with the user's key, or drop encrypted events one at a time without closing the
  stream.
- **Class:** Bug.

**CONFIG-1: Schemas are held per window, not per scope.**
- **Spec:** NAP-CONFIG: schemas and values are per napplet scope.
- **Lean:** `Run/Config.lean:581` (`St.schemas : Scope → …`, persisted, decision 55).
- **Hypergolic:** `src/presentation/config-broker.ts:228,261`. A new endpoint starts with
  `schema: null`.
- **Reproduction:** probe `storage/config.test.ts`. Open a second window of the same scope and
  send `config.get`.
- **Expected:** `config.values {"theme":"dark"}`. Registering `$version` 1 after 6 should give
  `version-conflict`, and other subscribers of the scope should be pushed new values.
- **Actual:** `schemaError no-schema`, `ok:true`, and only the registering window is pushed.
- **Fix:** key the schema by scope.
- **Class:** Bug.

**CONFIG-2: Resolved defaults are persisted as user values.**
- **Spec:** "The shell is the sole writer". Values change only through user edits.
- **Lean:** `Run/Config.lean:631-640,660-676`; `default_resolution`.
- **Hypergolic:** `src/presentation/config-broker.ts:41`, where `cleaned` persists `resolved(...)`.
- **Reproduction:** probe `storage/config.test.ts`. Register a schema with default `dark`, then
  re-register it with default `light`, with no edit in between.
- **Expected:** `{"theme":"light"}`.
- **Actual:** `{"theme":"dark"}`; the stored record holds `"ordinary":{"theme":"dark"}`.
- **Fix:** persist only values the user edited.
- **Class:** Bug.

**IDENTITY-1: `getPublicKey` can go unanswered, or return `""` while signed in.**
- **Spec:** NAP-IDENTITY: `getPublicKey` always answers with the user's key.
- **Lean:** `getPublicKey_no_error` (`Run/Identity.lean:175`).
- **Hypergolic:** the parse is strict (`src/runtime/capability-protocol.ts:84`). `main.ts:143`
  re-parses and throws, so nothing is sent. `main.ts:144` falls back to `pubkey:""`.
- **Reproduction:** probe `storage/identity.test.ts`.
  - `{type:"identity.getPublicKey",id:"p1",extra:1}` gets no reply.
  - A reused `id` gets `pubkey:""`.
- **Expected:** `pubkey:"ab12cd"`.
- **Fix:** ignore extra members, and never answer with an empty key while signed in.
- **Class:** Bug.

**INC-1: `sender`/`peer` is the bare `d` tag, and channel targets are addressed by `d` tag.**
- **Spec:** NAP-INC row 4, "MUST NOT be interpreted as a manifest `d` tag". Row 5, "MUST
  distinguish different publishers, manifests, and simultaneous instances".
- **Lean:** `Run/Inc.lean:246-249` (`cx.endpointId`), `:230` (`byEndpointId?`); decision 33.
- **Hypergolic:** `src/routing/routing-broker.ts:188,193`; `src/routing/routing-channels.ts:27,28,33,58`;
  `src/napplets/published-identity.ts:59-62`.
- **Reproduction:** probe `routing/audit.test.ts`. Two publishers, both with `d=caller`, emit.
  - It prints `INC senders: [{…"sender":"caller","payload":1},{…"sender":"caller","payload":2}]`
    (rerun and confirmed).
  - Opening a channel to a `d` tag shared by two live views gives `"peer unavailable"`.
- **Expected:** distinct, opaque per-endpoint ids.
- **Fix:** use the runtime's endpoint id.
- **Class:** Bug.

**INTENT-1: `intent.launch` is not implemented and gets no reply.**
- **Spec:** NAP-INTENT rows 81-98 (PR #148).
- **Lean:** `Run/Intent.lean:447` (`decode`, launch branch), `launchErr`/`launchOk`,
  `launch_outputs`; decision 50; traces `intent` step 11 and `intent-launch*` step 8.
- **Hypergolic:** `src/routing/routing-contract.ts:100-107` has no schema for it, so parsing
  throws. `runtime/src/guest-envelope.ts:88-124` has no routing branch, so nothing is sent.
- **Reproduction:**
  - Probe `routing/audit.test.ts` prints `intent.launch: THROWS Invalid routing request`.
  - The ingress adapter reports `intent#11 … DIFF: oracle replies, Hypergolic drops at ingress`.
- **Expected:** `intent.launch.result`.
- **Actual:** silence, and the napplet waits for its own timeout.
- **Fix:** implement it, or answer `{ok:false, error:"launch rejected"}`.
- **Class:** Bug (missing message type).

**INTENT-2: A malformed or extended `intent.invoke` gets no result, and `handlerHint` is
rejected.**
- **Spec:** NAP-INTENT row 51 ("MUST respond to `intent.invoke` with the same request `id`") and
  row 110 (an extra `sender` is ignored). Rows 4 and 63-73 cover `handlerHint`.
- **Lean:** `Run/Intent.lean:447ff` (`invokeErr id "invalid convention"`); `requestOf?` ignores
  unknown members; decision 39.
- **Hypergolic:** `src/routing/routing-contract.ts:9,77` rejects unknown keys, then the request is
  dropped as in INTENT-1.
- **Reproduction:** probe `routing/audit.test.ts` prints `extra sender member: THROWS` and
  `handlerHint: THROWS`.
- **Expected:** an `intent.invoke.result`.
- **Fix:** reply whenever `id` is a string, ignore unknown members, and accept `handlerHint`.
- **Class:** Bug.

**RESOURCE-1: The `blob` field carries a host `Blob` object instead of canonical base64.**
- **Spec:** "Every wire `blob` field MUST use [canonical padded base64]" and "Host byte objects …
  MUST NOT appear in these wire fields" (NAP-RESOURCE rows 13 and 15).
- **Lean:** `Run/Resource.lean` `itemJson`/`finishMsg` (~685-709); trace `resource-data` expects
  `"blob":"AAEC/w=="`.
- **Hypergolic:** `runtime/src/resource-adapter.ts:49,67`. Hypergolic's own test asserts the Blob:
  `tests/network/resource-transfer.test.ts:35`.
- **Reproduction:** probe `resource/res.test.ts` prints `"blob":"Blob(5)"`.
- **Fix:** send base64 on the wire, and let the binding build the `Blob`.
- **Class:** Bug. Hypergolic pins an older revision of NAP-RESOURCE.

### Medium

| ID | Statement and Lean reference | Hypergolic | Reproduction: expected → actual | Fix | Class |
|---|---|---|---|---|---|
| NIP5D-2 | Row 18, "a manifest that does not carry exactly one `x` tag MUST be rejected"; row 32, `content` "MUST contain a non-empty … description". `Manifest.lean` `xValue?`, `checkManifest_single_x`, `emptyContent`. | `src/napplets/verified-artifact.ts:179-182` (the legacy-path branch only rejects `x` tags when there are more than 1, and skips the content check) | Probe `core/manifest-x.test.ts`: a signed kind 35129 event with `d` and `path`, no `x`, empty content. Expected: rejected. Actual: `ACCEPTED format= legacy-path x tags= 0 content= ""`. | Accept NIP-5D manifests only, or require exactly one `x` and non-empty content in both formats. | Bug |
| RELAY-3 | Row 26, "MUST encrypt content and sign … and respond"; row 29 (every request gets a result). `Run/Relay.lean:235-242`. | Missing from `runtime/src/guest-envelope.ts:43-86` and from `runtime/src/main.ts:190`; still advertised at `src/runtime/nap-catalogue.ts:41`. | Probe `relay/envelope.test.ts`: `publishEncrypted valid= false replies= []`. Ingress adapter: `relay-ciphertext#5`. Expected: a result. Actual: silence. | Implement it, or reply `ok:false` and stop advertising it. | Bug |
| RELAY-4 / OUTBOX-2 | Decision 9; the OUTBOX docstring, "`outbox.close` is answered with `outbox.closed`". `Run/Relay.lean:310-312`, `Run/Outbox.lean:545-547`; trace `relay-subscribe` step 7. | `runtime/src/main.ts:128`; `runtime/src/native-client.ts:401` | Probe `relay/stream.test.mts`: `guest messages after close = 0`. Expected `relay.closed {subId}` → nothing. | Send `<domain>.closed`. | Silent (decision 9) |
| RELAY-5 / OUTBOX-3 | Decision 10: reusing a `subId` replaces the old subscription. `stopSub` in `Run/Relay.lean`. | `runtime/src/native-client.ts:296` (a permanent `claim`); `runtime/src/main.ts:126` | Probe `relay/stream.test.mts`: reusing a live `subId` gets `relay.closed`, while the old stream `still delivering after "closed"`. | Replace the old subscription, or never send `closed` for a `subId` that is still live. | Silent (decision 10), plus a Bug for the inconsistent `closed` |
| CONFIG-3 | Decision 47: `x-napplet-secret` with `default` is `secret-with-default` for every type. `Run/Config.lean:457`. | `src/presentation/config-schema.ts:103` | Probe `storage/config.test.ts`: number, boolean and object secrets with a default give `invalid-schema` instead of `secret-with-default`. | Check secret-with-default before the type check. | Bug |
| CONFIG-4 | Decision 26: an invalid default is skipped. `Schema.resolve` `:289`. | `config-schema.ts:132` | `{t:{type:string,enum:["a"],default:"b"}}`: expected `ok`, then `values {}`; actual `invalid-schema`. | Skip the default instead of rejecting the schema. | Bug |
| CONFIG-5 | Decision 47 (Core Subset). `Run/Config.lean:465,475`; `leafOf`. | `config-schema.ts:106,107,120-121` | An `object` with no `properties`, a schema-valued `additionalProperties`, or `minimum` on a string: expected `ok`; actual `invalid-schema`. | Accept these. | Bug (the 3 cases above). Duplicate `required` entries and `minimum > maximum` are also rejected: Silent. |
| CONFIG-6 | Decision 31 and the CONFIG paragraph: unknown or non-core keywords give `invalid-schema`. `Run/Config.lean:354`. | `config-schema.ts:92,93,98,100` | `$version:"x"` gives `version-conflict`; nested `$schema` gives `unsupported-draft`; `patternProperties` gives `pattern-not-allowed`; `$dynamicRef` gives `ref-not-allowed`; `x-foo` is accepted. Expected: `invalid-schema` in every case. | Align the codes; allow only `x-napplet-*` extensions. | Bug |
| CONFIG-7 | `Run/Config.lean:563`: the request `version` wins over `$version`. | `src/presentation/config-broker.ts:226` | `version:12` with `$version:11`: expected `ok`; actual `version-conflict`. | Use the request version. | Bug |
| CONFIG-8 | `Schema.resolve` `:289-305`: own default, then every ancestor's. | `config-schema.ts:145` | Root `default {a:{x:1}}` with `a.default {}`: expected `{"a":{"x":1}}`; actual `{"a":{}}`. | Walk all ancestors. | Bug |
| CONFIG-9 | Decision 31. `Run/Config.lean:129-148`. | `runtime/src/guest-envelope.ts:65` (no branch in `rejectEnvelope`) | `registerSchema` with no `schema`, or `version:-1`: expected `ok:false invalid-schema`; actual dropped. `config.get` with an extra member, and `config.subscribe {id}`: expected accepted; actual dropped. | Reply when `id` is a string; ignore extra members. | Bug |
| IDENTITY-2 | Decision 31. `Run/Identity.lean:91`. | `src/runtime/capability-broker.ts:98-103` (no identity branch) | `identity.getList` with no `listType`: expected `error:"invalid request"`; actual no reply. | Add an identity branch. | Bug |
| IDENTITY-3 | Same wire types only; `getPublicKey_no_error`. | `runtime/src/guest-envelope.ts:44` with `guest-message-receiver.ts:24-27` | A burst of more than 64 messages per second gets `{type:"identity.getPublicKey.error",error:"quota-exceeded"}`, a type the spec does not define. | Answer rate-limited requests in the NAP's own result shape. | Bug |
| STORAGE-1 | `Nap/Storage.lean:98-103`: one per-scope quota (`quota_preserved`). | `src/storage/ports.ts:12`; `src/runtime/capability-protocol.ts:96-97`; `src/storage/database.ts:239` | A 300 KB value or a 2000-byte key: expected success; actual `"invalid storage request"`. The 257th key gets `"storage quota exceeded"`. | Document the limits or align. | Silent (the spec only recommends 512 KB) |
| STORAGE-3 | Decision 31. `Run/Storage.lean:53-70`. | `capability-protocol.ts:93`; `guest-envelope.ts:79` | Extra member: expected a `value`; actual an error. `id:""`, or an `id` of 200 characters: expected a reply; actual none. | Ignore extra members. | Bug (extra members); Silent (id length) |
| STORAGE-4 | `handle_same_id` (every request is answered). | `capability-broker.ts:170`; `src/runtime/request-history.ts:22-26` | Reused id: `"request already used or session limit reached"`. After about 1022 non-SDK ids, every request fails. | Track only pending ids. | Silent |
| STORAGE-5 | No rate limit in the model. | `runtime/src/guest-message-receiver.ts:24-27` | The 65th message within a second gets `quota-exceeded`. | — | Silent |
| RESOURCE-2 | Decision 13: a duplicate in-flight id is ignored. `Run/Resource.lean:775-781`. | `runtime/src/resource-adapter.ts:93` | Probe `resource/res.test.ts`: expected nothing; actual `resource.bytes.error … quota-exceeded`. | Drop it silently. | Bug |
| RESOURCE-3 | Only in-flight ids are blocked (`inUse`). | `src/resources/resource-service.ts:32-33`; `src/runtime/request-history.ts:11-28` | Reusing an id after completion gives `invalid-request`; after 1024 ids, everything fails. | Track only pending ids. | Silent |
| RESOURCE-4 | README RESOURCE paragraph: at most 10 in flight, the rest queue. `pump`/`launch`. | `resource-adapter.ts:93` (`pending.size >= 4`) | The 5th concurrent request: expected queued; actual `quota-exceeded`. | Queue it. | Bug |
| RESOURCE-5 | `nostrOk` `Run/Resource.lean:469`: checksummed `npub`/`nprofile`/`note`/`nevent`/`naddr`; otherwise `invalid-request`. | `src/resources/resource-contract.ts:146`; `resource-service.ts:66` | A valid `npub`, a `note` with a bad checksum, or an `nsec`: expected fetch / `invalid-request` / `invalid-request`; actual `decode-failed` for all three. | Verify the bech32 checksum and use the model's codes. | Bug (codes); Silent (refusing `npub`) |
| RESOURCE-7 | `bytes_mime_sniffed_not_svg` (`Nap/Resource.lean:271`); decision 43's allowlist has no archives. | `src/resources/resource-mime.ts:132` | Probe `resource/res2.test.ts`: gzip-wrapped `<svg><script>…` is delivered as `application/gzip`, and the napplet can gunzip it. | Refuse gzip, or sniff the decompressed payload. | Silent (decision 43: the allowlist is configurable), but it defeats the raw-SVG rule |
| UPLOAD-1 | README UPLOAD paragraph: up to 1 MiB answers `complete`; a declined consent is a `cancelled` result (trace `upload` step 7). | `modules/napplet-host/android/…/UploadTransport.kt:139-151,278`; iOS `UploadTransport.swift:139` | Always `status:"pending"`; the outcome, including a decline, arrives only as an `upload.status.changed` push. | Return the terminal state in the result when it is known. | Silent (README UPLOAD) |
| INTENT-3 | Rows 8 and 20 (archetype, action and convention required; the convention must be queryless). `convOk` `Run/Intent.lean:508`, `:577`. | `src/routing/routing-contract.ts:78,81-85` | A missing `action` defaults to `open`; a missing `convention` is accepted; a `?query` is moved into `payload`; a convention that does not match the action gives `no handler`. Expected: `invalid convention`. | Require all three fields and check them first. | Bug |
| INTENT-4 | Row 31, "Legacy combined `archetype` tags MUST NOT substitute for `z` and `i`"; row 13 (delivery is `intent.deliver`). | `src/routing/routing-broker.ts:37-38,121-133`; `tests/routing/broker.test.ts:12-22` asserts `inc.event` | A legacy candidate has no `id`/`contracts`, and delivery arrives as `inc.event`. | Remove legacy routing from the NAP path. | Bug |
| INC-2 | Row 27, "MUST NOT parse, decode, normalize". `Run/Inc.lean:248` (exact match); decision 38. | `src/routing/routing-contract.ts:116-119` | `inc.emit` to `napplet:note/open?a=1` is rewritten and delivered; `napplet:foo` and `""` are dropped, while `inc.subscribe napplet:foo` is accepted. | Treat topics as opaque. | Bug |
| INC-3 | Decision 31. `Run/Inc.lean:143`. | Same drop path as INTENT-2 | `inc.subscribe` with no `topic`, or `inc.channel.open` with no `target`: expected `error:"invalid request"`; actual no reply. | Reply. | Bug |
| KEYS-1 | "MUST accept `keys.forward` and process the keystroke as if it occurred in the shell's own context"; README KEYS paragraph: a bound forwarded combo fires `keys.action`. `Run/Keys.lean` `handle .forward` → `fire`; trace `keys` step 4. | `runtime/src/keys-adapter.ts:79-83`; `keys.action` is never sent | Probe `ui/keys.test.ts`: register `defaultKey:'a'` (bound as `A`), forward `a`. Expected `keys.action {actionId:"go"}`; actual `[]`. | Fire the bound action. | Bug |

### Low

| ID | Statement and Lean reference | Hypergolic | Reproduction: expected → actual | Class |
|---|---|---|---|---|
| SRCDOC-1 | Decision 61; `Srcdoc.buildSrcdoc` adds `<head>` when it is absent and follows the tokenizer. | `src/napplets/html-envelope.ts:30-36`; `src/napplets/verified-artifact.ts:246-300` | Probe `core/srcdoc-harness.ts` ran 31 vectors. 28 are refused, including `<!doctype HTML>\n<HTML LANG=en>\n <HEAD>` (unquoted attribute), `<title>x</title>…` (no `<head>`) and `<meta charset=utf-8><head>`. The model builds a safe srcdoc for each. A leading BOM is removed by `TextDecoder` before the check, so the BOM vector is refused here only in isolation. | Silent (decision 61; this is a fail-closed choice) |
| CSP-1 | NAPPLETS-SPEC §16.1 baseline; `Srcdoc.baselineCsp` has `worker-src 'none'` and `media-src 'none'`. | `runtime/src/main.ts:92-98,238` | The shipped policy has `worker-src blob:` and adds `webrtc 'block'`. It has `media-src blob:` when `resource` is granted. The legacy profile adds `script-src blob:`. | Silent (the baseline is a SHOULD); weaker than the baseline for workers |
| RELAY-6 / OUTBOX-5 | Decision 30. `EventTemplate.ofJson?` (`Napplet/Event.lean:95`). | `runtime/src/guest-envelope.ts:73-74`; `src/security/event-snapshot.ts:53` | The template must have exactly 4 keys. Trace `outbox` request `p2` (`{kind,content,tags}`): expected `ok:true`; actual `invalid publication`. | Silent (decision 30) |
| RELAY-7 | Decisions 31, 40 and 41. `Run/Relay.lean:213-249,223`. | `guest-envelope.ts:94`; `capability-broker.ts:100` | Error strings `"Invalid event template."`, `"invalid relay query"` and `"invalid or unsupported relay subscription"`, where the model has `"invalid request"`, `"invalid relay subscription"`, `"invalid relay destination"` and `"policy denied"`. A subscribe with a non-string `id` gets no reply, where the model sends `relay.closed`. | Silent (strings); Bug (no reply) |
| RELAY-8 | Row 34 (SHOULD include relay hints). `hintsOf` `:288`. | `capability-broker.ts:63` | `sidecar` is undefined. | Silent (SHOULD) |
| OUTBOX-4 | Row 9 (`OutboxRelayPlan` is required). `planMsg` `Run/Outbox.lean:292`. | `src/outbox/query-contract.ts:103-109` | An error result has no `plan`. | Bug |
| STORAGE-2 | Decision 31. `Run/Storage.lean:57`; `Nap/Storage.lean:103`. | `capability-broker.ts:35,101` | `"invalid storage request"` and `"storage quota exceeded"`, where the model has `"invalid request"` and `"quota exceeded"` (trace `storage` request `b9`). | Silent (strings) |
| CONFIG-10 | Trace `config` step 4: result first, then push. | `config-broker.ts:233,239` | The push comes before the result, and the error text is generic. | Silent |
| THEME-1 | Decision 31. `Run/Theme.lean:79`. | `guest-envelope.ts:97-99` | `theme.get` with an extra member, or with `id:""`, is dropped. | Bug |
| THEME-2 | The wire types are fixed. | `guest-envelope.ts:44` | A burst gets `theme.get.error`, a type the spec does not define. | Bug |
| RESOURCE-6 | RFC 2397; `dataBytes?` `Run/Resource.lean:434`. | `src/resources/resource-service.ts:84-101` | `data:;base64,aGk%3D`: expected `"hi"`; actual `decode-failed`. `data:nocomma`: expected `invalid-request`; actual `decode-failed`. | Bug |
| RESOURCE-8 | `gateMime` gives `blocked-by-policy`; `application/octet-stream` is allowed. | `src/resources/resource-mime.ts:138-142` | HTML, SVG and unknown binary give `decode-failed`. | Bug (code) |
| RESOURCE-9 | `decode` ignores extra members; one bad URL in `bytesMany` is a per-item error (row 7). | `resource-contract.ts:34,41,46,155` | Extra `opts` gives `invalid-request`. An empty item fails the whole envelope. An `id` over 128 bytes gets no reply. | Bug (row 7) |
| RESOURCE-10 | `infoJson` lists 7 schemes. | `resource-contract.ts:160` | `hashtree` and `http` are omitted. | Silent (scheme policy) |
| UPLOAD-2 | `Run/Upload.lean:521` (`"unknown upload"`). | `UploadTransport.kt:118,165`; iOS `:112,151` | `upload.status` for an unknown id gives `"policy denied"`. | Bug |
| UPLOAD-3 | `noTransform` keeps the bytes. | `UploadWire.kt:38`; `NativeUploadAuthority.java:149`; `UploadFileProfile.java:15-19` | `noTransform` is ignored; PNG metadata is always stripped. | Silent |
| UPLOAD-4 | Decision 44: `upload.info` reports the effective policy. | `UploadTransport.kt:110`; `UploadFileProfile.attachmentType` | JPEG cannot be uploaded, and `mimeTypes` is not disclosed. | Silent (decision 44) |
| INTENT-5 | Row 38/65. `Run/Intent.lean:582-585` (`"invoke rejected"`, no prompt); decision 7. | `src/routing/routing-broker.ts:146-165` | An unknown explicit handler gives `"no handler"`. An incompatible one is shown to the user first, then fails with `"unsupported action"`. It never falls back, which is correct. | Bug |
| INTENT-6 | INTENT paragraph strings; `invokeErr {ok:false,error}`. | `routing-broker.ts:138-175` | Uses `"ambiguous handler"`, `"invoke failed"`, `"handler requires focus"` and others, plus extra `archetype`, `action` and `handled` fields. | Bug (strings); Silent (fields) |
| INC-4 | INC paragraph strings. `Run/Inc.lean:270-275`. | `routing-broker.ts:194-208`; `routing-channels.ts:22` | `"peer unavailable"` is used for self, for a missing target and for the channel limit; `"user denied"`; a `reason:"closed"` on member close. | Bug (strings) |
| CVM-1 | Decision 27 / CVM paragraph: payments off gives `"payment required"`. `gate` `Run/Cvm.lean:505`. | `src/cvm/cvm-session.ts:174-176` | Gives `"payment denied"`. It never pays, which is correct. | Silent |
| NOTIFY-1 | Decision 24. `Run/Notify.lean` `core .dismiss` emits only the `hide` effect. | `src/presentation/notify-broker.ts:88,115` | Probe `ui/notify.test.ts`: a napplet's own `notify.dismiss` pushes `notify.dismissed {reason:"user"}` back to it. | Bug |
| NOTIFY-2 | README NOTIFY paragraph: more than 3 actions are truncated (`Nap/Notify.lean:76`). | `src/presentation/notify-contract.ts:22,43` | Rejected with `"invalid notification"`. | Silent (MAY limit) |
| NOTIFY-3 | Decision 31. `Run/Notify.lean` `decode` ~209. | `guest-envelope.ts:52,110-112`; `notify-contract.ts:41` | A missing title gives `"invalid notification"`. An extra member gets no reply at all, for both `send` and `permission.request`. An empty title is rejected. | Bug |
| NOTIFY-4 | `channel` is unconstrained; permission lasts for the endpoint's lifetime. | `notify-broker.ts:127,131` | An unregistered channel gives `"invalid channel"`; `badge` requires permission; permission persists across sessions. | Silent |
| LINK-1 | Decision 31. `Run/Link.lean:177` (`labelOf` ignores bad labels). | `src/links/link-contract.ts:23,27`; `runtime/src/link-adapter.ts:9`; Android `LinkTransport.kt`; iOS `LinkTransport.swift:44` | A non-string `label`, non-object `options`, or extra members give `invalid-url`. | Bug |
| KEYS-2 | Decision 31. `Run/Keys.lean` `decode` ~127-142. | `runtime/src/keys-adapter.ts:22-26,58,59` | An id outside `[A-Za-z0-9_.:/-]{1,96}` gets no reply. An extra member gives `actionId:""`. `Ctrl+Ctrl` is accepted but left unbound, where the model gives `"invalid action"`. | Bug (no reply); Silent (rest) |
| MEDIA-1 | Conformance row 57 strings; `Run/Media.lean:292`. | `runtime/src/guest-message-receiver.ts:41`; Android `NativeFiniteVideo.kt:98,101` | Every failed create gives `"Unsupported media request."`. | Silent (strings) |
| MEDIA-2 | `NapMedia.focusLost` acts only on `playing`. | `NativeFiniteVideo.kt:334,357-365`; iOS `NativeFiniteVideo.swift:291-294` | Pause (reason `user`), then lose focus: a second `paused`/`focus-lost` overwrites the reason. Found by code path only. | Bug |

Informational only, not counted:
- MEDIA-3: sessions start `paused` (decision 22 chose `stopped`).
- KEYS-3: the space key binding is reported as `" "`.

## Results by check

### 1. Identity and transport

- **Hello and port:** absent (NIP5D-1).
- **Binding from verified bytes:** yes. `verified-artifact.ts` checks the signature, event id,
  coordinate and SHA-256. The WebView rechecks the HTML hash and aggregate before rendering
  (`published-artifact.ts:104-106`). The exception is NIP5D-2.
- **Sandbox:** `allow-scripts` only, with no same-origin access.
- **Messages only from the bound endpoint:** by `event.source` plus `isTrusted`
  (`guest-message-receiver.ts:22`), not by port.
- **Teardown:** every path found (`pagehide`, a second `load`, nested frames, failure, account or
  epoch change) runs `cleanup` → `destroyFrame`. That path unregisters the Kehto session and origin
  registry, destroys the native client and removes the frame (`main.ts:242-250,349-362`). There is
  no port to close.

### 2. Wire formats

See the per-NAP findings.

- **Unknown types:** ignored silently, as required. The ingress adapter confirmed that
  `nosuch.thing` and unknown `relay.*` and `keys.*` types produce no reply.
- **Malformed known types:** frequently dropped with no reply, against decision 31. This affects
  CONFIG-9, IDENTITY-1/2, THEME-1, INTENT-2, INC-3, NOTIFY-3, KEYS-2 and RELAY-7.

### 3. Security rules

| Rule | Result |
|---|---|
| Napplet ciphertext is never signed | **Fails:** RELAY-1, OUTBOX-1. |
| Private IPs are blocked on every redirect | **Holds.** Every hop is revalidated, DNS answers are pinned and checked, and decimal, octal and hex IP forms, `localhost`, CGNAT, `0/8`, `::`, mapped IPv6 and NAT64 are all refused. Android: `PublishedHttpsTransport.java:136-157,186-193` (compiled and probed). iOS: `PublishedPinnedHTTPS.swift:132,448-462` (read only). Stricter than decision 12. |
| MIME types are sniffed | **Holds:** `src/resources/resource-mime.ts`, with a recheck at `runtime/src/resource-adapter.ts:36`; uploads are sniffed natively (decision 16). Gzip-wrapped SVG still gets through (RESOURCE-7). |
| Consent before upload, value and link | **Holds.** Every upload and every link prompts, which is stricter than decisions 17 and 25. VALUE is absent. |
| Allowance debited before payment | **N/A:** there are no payments (VALUE is absent; CVM is free-only). |
| Notifications dismissed only by their owner | **Holds:** a dismiss from another napplet is ignored (`ui/notify.test.ts`). NOTIFY-1 is about the owner's own dismiss. |
| Config secrets never taken from defaults | **Holds:** secrets come only from saved values, and a secret with a default is rejected, though with the wrong code for non-string types (CONFIG-3). |

### 4. Document injection

- Probe `core/srcdoc-harness.ts` runs Hypergolic's own published-path builder, with the injectors
  in the order `renderGuest` uses. It runs on all 26 adversarial inputs from `Srcdoc.lean`, plus 5
  of them placed behind a doctype.
- Every output was parsed with parse5 (the WHATWG HTML parser).
- On all 3 documents Hypergolic accepts, the CSP meta is the first element of `<head>`, and
  Kehto's `window.napplet` prelude comes before every napplet script. That matches the
  requirements of `csp_first` and `bootstrap_first`.
- Shell-owned helper scripts sit between the CSP and the prelude. They are host code, so napplet
  scripts still run after the bootstrap.
- The other 28 inputs are refused (SRCDOC-1).
- The CSP differs from `baselineCsp` (CSP-1).

### 5. Persistence

| `Persist.Persisted` field | Hypergolic | Result |
|---|---|---|
| STORAGE values | SQLite `saved_strings`, scoped to (user, publisher, app, aggregate version, scope, instance) | Survives. The scope adds the account to the model's key, which is stricter. |
| CONFIG schemas | Not persisted per scope (CONFIG-1) | **Diverges** |
| CONFIG values | Native encrypted record per (identity, publisher, app, aggregate hash), but resolved defaults are written as values (CONFIG-2) | Survives; contents diverge |
| INTENT defaults | Per-identity catalog and defaults, kept across restart (`docs/intent-inc.md:7`) | Survives |
| LINK rules | None exist: every link prompts | Nothing to persist |
| UPLOAD consent | One-use, never remembered | Nothing to persist |
| VALUE and CVM allowance balances | No allowance feature exists | N/A |

- Restore brings back no port, window, binding or grant. A restart creates new frames and native
  generations.
- The persisted `access_grants` record domain consent. That corresponds to the model's exposure
  policy (`Config`), not to runtime grants, and "a persisted grant alone does not authorize a live
  generation" (`docs/workspace-storage.md:69`).
- One extra: the instance-scope UUID is persisted, so instance-scoped storage comes back for a
  restored pin. The model issues instance ids per runtime session (decision 54). The spec is
  silent here; this is not counted as a finding.

### 6. Mobile lifecycle

- **Late replies after teardown are dropped.** Every adapter captures `live()` or
  `captureRecipient()` and checks it before `send` (`main.ts:104-147,288-296`).
- **Native replies are bound to the generation.** They are matched on `sessionId === generation`
  (`native-client.ts:128-154`).
- **CVM** drops late and duplicate responses (`cvm-native.ts:17-18`) and aborts in-flight work on
  close (`cvm-session.ts:179-185`).
- **Resource cancel** drops late results.
- **WebView reload or document replacement:** `pagehide` → `stop()`, and a second `load` →
  `fail('frame-navigation')`. The browser test confirmed the second case.
- **Backgrounding:** closes INC channels (`docs/intent-inc.md:65`) and pauses media. Not run on a
  device.
- **OS kill:** native generations die with the process, and the next launch starts fresh
  generations. Seen in the code only.
- No violation was found. See also "Not checked".

### 7. Trace replay

- `core/ingress.ts` replays every `message` input on a bound port from all 43 `lean/traces/*.in.ndjson`
  files (97 steps). It runs them through Hypergolic's real WebView ingress:
  - the side-lane routing in `guestMessageReceiver`;
  - `validEnvelope`;
  - `rejectEnvelope`;
  - the `media-wire` projection.
- It then compares the first reply with `*.out.ndjson`. Output is in `core/ingress.out`:
  - 75 steps are forwarded to NAP handlers.
  - 3 steps match at ingress.
  - 19 steps differ:
    - absent NAPs: `display` ×3, `pow` ×2, `value` ×2, `shell.check` ×3, `intent.launch` ×3,
      `relay.publishEncrypted`;
    - MEDIA: napplet-owned sessions are unsupported;
    - `relay-ciphertext#4` is refused for its template shape, with `"Invalid event template."`;
    - `upload`: the trace configures a `nip96` rail, which Hypergolic refuses.
  - 56 transport inputs (`hello` ×51, `portClosed` ×5) have no counterpart.
- A full replay past ingress is not feasible. NAP behaviour runs across the React Native app,
  Kotlin and Swift, and the transport differs from step 3 of every trace.
- The forwarded steps were compared per NAP instead. The agents' probes drive Hypergolic's real
  brokers with the trace requests, and each finding above cites the trace step it diverges on.

## Possible model errors

These are recorded only, and the model was not changed. Each needs a decision before the model is
edited.

1. **IDENTITY error results leave out the primary field.**
   - Decision 52 says any identity result carrying `error` holds the primary field's default.
   - The decode-failure path uses `Component.errorReply` (`Napplet/Component.lean:108`), which
     sends `{type,id,error}` only.
   - Evidence: the oracle on `hypergolic/storage/id.in.ndjson`, step 4, gives
     `{"type":"identity.getList.result","id":"l1","error":"invalid request"}` with no `entries`.
2. **A secret on array `items` is filled from a default.**
   - `Run/Config.lean`'s leaf case drops `x-napplet-secret` on array `items`.
   - So an array whose items are secret, with `default:["public-default"]`, is accepted, and the
     default is delivered.
   - Evidence: the oracle on `hypergolic/storage/cfg3.in.ndjson` gives
     `config.values {"list":["public-default"]}`.
   - That contradicts the intent of `secret_never_defaulted` and decision 47. Hypergolic rejects
     this schema.
3. **KEYS space key (unconfirmed).** `Run/Keys.lean` `normKey` does not treat `"Space"` and `" "`
   (the browser's `KeyboardEvent.key`) as the same key. Read only; not evaluated.

## Reproduction

The commands below assume Hypergolic is cloned at `../hypergolic` (relative to the napplets root),
with both dependency trees installed. They use pnpm 10.34.5, run with `--ignore-scripts`; the
engine check is relaxed because Node 26 was used here instead of the pinned 24.20.0.

```bash
cd ../hypergolic && git checkout 0b00b23e9c4c385f16d62833f9743eafb98ef744
npx -y pnpm@10.34.5 install --frozen-lockfile --ignore-scripts --config.engine-strict=false
npx -y pnpm@10.34.5 --dir runtime install --frozen-lockfile --ignore-scripts
```

Trace replay through Hypergolic's ingress. The output should match `core/ingress.out`. Bundling
needs esbuild, and parse5 is needed for the next step:

```bash
cd lean/audits/hypergolic/core && npm i --no-save esbuild@0.25.0 parse5@7.3.0
npx esbuild ingress.ts --bundle --format=esm --platform=node --outfile=/tmp/ingress.mjs
node /tmp/ingress.mjs ../../../traces
```

Document builder on the `Srcdoc.lean` vectors:

```bash
cd lean/audits/hypergolic/core
npx esbuild srcdoc-harness.ts --bundle --format=esm --platform=node --outfile=/tmp/srcdoc.mjs
node srcdoc-run.mjs /tmp/srcdoc.mjs
```

Manifest without an `x` tag (NIP5D-2):

```bash
cd ../hypergolic && node --experimental-strip-types --test ../napplets/lean/audits/hypergolic/core/manifest-x.test.ts
```

Navigation revocation in Chromium. Copy the spec in temporarily, then delete it:

```bash
cd ../hypergolic/runtime && npx -y pnpm@10.34.5 exec playwright install chromium
cp ../../napplets/lean/audits/hypergolic/core/zz-audit-navigation.spec.ts tests/
npx -y pnpm@10.34.5 exec playwright test tests/zz-audit-navigation.spec.ts --project=chromium
rm tests/zz-audit-navigation.spec.ts
```

Per-NAP probes. Run each from `../hypergolic`; adjust any absolute paths inside a probe to your
checkout. Probes whose name ends in `.test.ts` use `--test`. Of the `.test.mts` probes:
- `cipher.test.mts` takes `--test`;
- `query.test.mts` runs as a plain script under `--experimental-strip-types`;
- `stream.test.mts` and `outbox.test.mts` are bundled with esbuild and then run with `node`.

`relay/envelope.test.ts` and `storage/envelope.test.ts` need
`--import ../napplets/lean/audits/hypergolic/<dir>/register.mjs` to resolve imports without
extensions.

```bash
node --experimental-strip-types --test ../napplets/lean/audits/hypergolic/relay/cipher.test.mts
node --experimental-strip-types --test --test-timeout=25000 ../napplets/lean/audits/hypergolic/routing/audit.test.ts
node --experimental-strip-types --test ../napplets/lean/audits/hypergolic/storage/config.test.ts
node --experimental-strip-types --test ../napplets/lean/audits/hypergolic/resource/res.test.ts
node --experimental-strip-types --test ../napplets/lean/audits/hypergolic/ui/keys.test.ts
```

Model-side comparison (the oracle):

```bash
cd lean && lake build && .lake/build/bin/napplet-oracle < audits/hypergolic/storage/cfg3.in.ndjson
```

## Not checked

- **The native relay pool, Android or iOS.** Whether a scoped subscription emits its own
  `closed`/`eose`, and the `outbox.publish` fan-out and NIP-65 resolution end to end. Both need a
  device or emulator with live relays.
- **The approval UI.** Whether the review sheet shows ciphertext to the user. This affects how
  RELAY-1 plays out in practice, not whether it is a break.
- **On a device:** backgrounding, WebView process loss and the OS killing the app. Covered by
  reading the code only; Hypergolic's own native harnesses need physical devices.
- **The iOS address classifier and redirect logic.** Read, not executed (no Xcode run).
- **Live DNS rebinding,** native timeouts and body caps.
- **End-to-end flows:** the upload flow (consent UI, signing, the Blossom PUT) and the native media
  runtime (MEDIA-2 is from the code path only). Notification rendering and attribution UI, and the
  Android link dialog.
- **`identity.changed` across an account switch.** Sessions appear to be torn down on a switch, so
  the push may never be needed. Not verified end to end.
- **What Kehto does with an unknown `upload.*` or `resource.*` type.** It falls to a domain handler
  that throws `Capability unavailable` (`runtime/src/main.ts:114,175-176`); whether patched Kehto
  then sends an error envelope was not traced.
- **Self-target INC `channel.open`.** The probe got no reply, possibly an artifact of the review
  harness.
- **Full replay of the traces past ingress.** Explained in Check 7.
- **NAP-VALUE, NAP-POW and NAP-DISPLAY behaviour, `shell.check`, `intent.launch` and kind 15129
  manifests.** These are absent from Hypergolic, so only their absence is recorded.
