# Napplets and the Runtime/Shell: Specification

Status: **draft, in active development** (compiled 2026-11-21).
Authors: dskvr (NIP-5D), Sandwich/sandwichfarm (napplet SDK, NAP registry), contributors.

> **Provenance.** Compiled from the NIP-5D draft (`dskvr/nips`, branch `nip/5d`, head `f60550c`),
> the `napplet/naps` registry (branch `master`) and every NAP spec on its PR head branch, the
> registry's web projection, templates and SOUL.md, the `napplet/web` SDK docs and maturity page,
> the `kehto/web` runtime docs and `napplet.run`. Fetching tools capped verbatim quoting, so this
> is a close structured paraphrase, **not** a character-exact copy. Normative keywords (MUST,
> SHOULD, MAY) are carried over from the sources. For authoritative wording read the sources in
> section 18. Every spec is a draft; only 5 NAPs are merged to `master`, the other 16 (plus two
> CLASS sub-tracks) live on open PR branches and may change. Upstream inconsistencies and open
> review questions are recorded under each NAP as **Open issues**.

---

## 1. Overview

A **napplet** is a small sandboxed web application that runs inside a host called the **shell**
(also **runtime**). It has no direct access to keys, network or storage. Everything it can do
is mediated by the shell over a message protocol.

```
Manifest   what a napplet IS / how it is described      artifact, identity   (NIP-5D)
  NAP      what a runtime OFFERS a napplet              the capability seam  (napplet/naps)
   └─ projection: web (only one in use), native, WASM   same contracts, different host
```

| Layer | Spec | Home |
|---|---|---|
| Manifest, transport, identity, sandbox | NIP-5D "Nostr Web Applets" (draft, optional) | PR nostr-protocol/nips#2303 |
| Capability contracts | NAPs (Nostr Applet Protocol) | github.com/napplet/naps |
| Web mapping | `projections/web.md` | napplet/naps |
| Napplet-side SDK | `@napplet/*` | github.com/napplet/web |
| Runtime toolkit | `@kehto/*` | github.com/kehto/web |

NIP-5D is deliberately thin. Relay access, storage, signing, theming and the rest are NAPs.
References: NIP-01, NIP-19, NIP-89, proposed NIP-91 (PR #2252), NIP-92, NIP-94, NIP-34, CSP Level 3.

## 2. Philosophy

- Napplets are untrusted. The shell is trusted. The browser enforces iframe boundaries.
- Napplets SHOULD be single-purpose. The shell composes napplets; napplets do not compose themselves.
- Keys never enter the sandbox. Napplets produce cleartext only.
- Capabilities are per-domain and opt-in. A shell MAY support any subset of NAPs.
- Identity comes from verified bytes, never from a host or gateway claim.

## 3. Terminology

| Term | Meaning |
|---|---|
| Seam | Boundary between napplet and runtime |
| Runtime / Shell | Host that verifies, loads and serves napplets |
| NAP | One capability contract; owns one message domain |
| Domain | Short bare NAP name (`relay`, `intent`). Not `NAP-RELAY` |
| Projection | Mapping of NAP contracts onto a host (web today) |
| NAP-WORD | A NAP interface spec, e.g. NAP-RELAY |
| Convention | Message shape with identity `napplet:<archetype>/<intent>`. Not a NAP |
| Archetype | Ad-hoc label for what a napplet does (`feed`, `profile`). Not a granted role |
| Gateway | Optional untrusted byte server |
| Snapshot | Kind 5129 manifest pinning one immutable version |

## 4. Event kinds

| Kind | Meaning | Type |
|---|---|---|
| 5129 | Snapshot: one immutable napplet version | regular |
| 15129 | Root napplet | replaceable |
| 35129 | Named napplet (has `d`) | addressable |
| 31990 | Shell handler advertisement (NIP-89) | addressable |
| 31989 | Handler recommendation (NIP-89) | addressable |

## 5. Manifest

### 5.1 Tags

| Tag | Cardinality | Meaning |
|---|---|---|
| `d` | exactly 1 on 35129; absent otherwise | napplet identifier (dTag) |
| `x` | exactly 1 | lowercase-hex sha256 of the single `/index.html` artifact (artifactHash) |
| `z` | 0+ | archetype (`feed`, `profile`) |
| `i` | 0+ | accepted intent, then its advertised parameter names |
| `R` | 0+ | NAP domain required for full functionality (bare name) |
| `O` | 0+ | optional NAP domain integration |
| `icon` | 0-1 | icon blob sha256, then MIME type |
| `screenshot` | 0+ | screenshot blob metadata |
| `preview` | 0-1 | preview video blob metadata |
| `server` | 0+ | Blossom server origin hint for artifact, icon, presentation blobs |
| `title` | 0-1 | short display label |
| `source` | 0-1 | source repo or archive location |
| `source-commit` | 0-1 | full Git commit ID in `source` |
| `source-archive` | 0-1 | archive URL, sha256, MIME |
| `a` / `A` | 0-1 each, kind 5129 only | parent / root napplet address |

Rules:

- The manifest MUST carry exactly one `x` tag. A manifest without exactly one MUST be rejected.
- `server` SHOULD hint the Blossom servers holding the blob.
- `content` MUST be non-empty human-readable plain text. Clients MUST treat it as plain text,
  not HTML or Markdown. There is no separate `description` tag.
- `a` (immediate antecedent) and `A` (root) use `35129:<pubkey>:<d-tag>`; the antecedent MAY
  belong to another author. Lineage MUST NOT affect verification. A runtime MUST NOT resolve
  or trust a referenced napplet on a snapshot's behalf.
- `z` and `i` are untrusted routing hints, never grants. They MUST NOT widen what a shell exposes.
- `i` trailing values are parameter names, not kind restrictions. A napplet with no `z` or `i`
  is valid but cannot be addressed by archetype.

### 5.2 Example (kind 35129; id, pubkey, created_at, sig omitted)

```json
{
  "kind": 35129,
  "content": "A feed viewer and editor hosted on Nostr",
  "tags": [
    ["d", "my-napplet"],
    ["x", "186ea5fd14e88fd1ac49351759e7ab906fa94892002b60bf7f5a428f28ca1c99"],
    ["z", "feed"],
    ["i", "napplet:feed/open"],
    ["i", "napplet:feed/edit", "filters", "relays"],
    ["R", "relay"],
    ["O", "theme"],
    ["icon", "ae7a3bd1a3fa9d824d0e64a6f57fe6cb4dd80c423786b6a2ecb94d587c94c75a", "image/png"],
    ["server", "https://blossom.example.com"],
    ["title", "My Napplet"],
    ["source", "https://github.com/example/my-napplet"]
  ]
}
```

### 5.3 Source metadata

- MAY include one `source` tag with exactly two elements. Location MUST be an absolute URL using
  http, https, ssh, git or nostr, or scp-like SSH `[user@]host:path`. Local paths and `file` URLs
  are unsupported. Examples: HTTPS, `ssh://`, `git@host:owner/repo.git`, `git://`, `nostr://<naddr>`.
- A `nostr` location MUST identify a kind 30617 repository announcement (NIP-34 clone URL format).
- MUST NOT contain more than one `source` tag, even with mirrors.
- Informational only. Does not replace `x` or verification, and does not attest the source
  reproduces the artifact.
- `source-commit`: MAY pin a revision for a Git `source`. Exactly two elements, full lowercase
  hex commit ID (40 chars SHA-1 or 64 chars SHA-256). Clients resolving this version's source
  MUST use the pinned commit. Ignored without a Git `source`.
- `source-archive`: exactly four elements: tag name, absolute HTTPS URL (no credentials, no
  fragment), 64-char lowercase hex sha256 of the archive bytes before decompression, MIME type.
  Clients MUST verify the digest before use.
- Clients MUST ignore a source field if its tag is malformed or repeated. Missing or unusable
  source metadata MUST NOT prevent playback.

### 5.4 Presentation media

- Any number of `screenshot` tags, at most one `preview` tag.

```json
["screenshot", "x <sha256>", "m image/png", "dim 1200x750", "size 184320", "alt The puzzle board"]
["preview",    "x <sha256>", "m video/webm", "dim 960x600", "duration 8.5", "alt Building a bridge"]
```

- Encoding is NIP-92 `key value`, split at the first ASCII space. Field order does not matter.
- `x` is REQUIRED, exactly one, 64-char lowercase hex sha256 of the full media bytes. No `url`
  field is required.
- Optional: `m`, `dim`, `size`, `alt` (NIP-94 meanings). Publishers SHOULD include `m` and `dim`.
  `duration` is seconds (NIP-71).
- Clients MUST ignore tags with a missing, malformed or repeated `x`, and MUST ignore unknown,
  malformed or repeated optional fields.
- Clients resolve blobs by hash via `server` hints and MUST verify sha256 before rendering.
  Screenshots MUST decode as PNG, JPEG or WebP. Previews MUST be a supported video format. If a
  valid `m` is present, clients MUST verify it matches the decoded format.
- Clients SHOULD preserve screenshot order and MAY show a subset. Unusable entries MUST NOT
  suppress usable ones or block discovery or playback.
- If multiple `preview` tags exist, clients MUST ignore the preview.

### 5.5 Icon

- MAY include one: `["icon", "<sha256>", "<mime-type>"]`. MIME MUST be `image/png`,
  `image/jpeg` or `image/webp`. SVG and others are unsupported.
- Clients MUST fetch by hash from declared Blossom `server` origins, verify `sha256(blob)`
  equals the hash, and verify the bytes decode as the declared format. MIME or server response
  alone is insufficient. Clients MUST render the verified bytes, not an unverified remote URL.
- An absent, malformed, unsupported, unavailable, mismatched or undecodable icon MUST fall back
  to generic artwork and MUST NOT prevent loading.
- The icon hash is separate from `x` and not part of `(dTag, artifactHash)` identity.

### 5.6 HTML metadata for publishing

Publishing tools SHOULD preserve manifest metadata in the artifact `<head>`:

| Manifest | HTML |
|---|---|
| `title` | `<title>My Napplet</title>` |
| `content` | `<meta name="description" content="...">` |
| `d` (35129) | `<meta name="napplet-id" content="my-napplet">` |
| `z` | `<meta name="napplet-archetype" content="feed">` |
| `i` | `<meta name="napplet-intent" content="napplet:feed/edit filters relays">` |
| `R` | `<meta name="napplet-requires" content="relay storage">` |
| `O` | `<meta name="napplet-optional" content="theme">` |
| `icon` | `<link rel="icon" href="data:image/png;base64,..." type="image/png">` |
| `source` | `<meta name="napplet-source" content="...">` |
| `server` | `<meta name="napplet-server" content="...">` |
| `a` (5129) | `<meta name="napplet-parent" content="35129:PUBKEY:PARENT_D">` |
| `A` (5129) | `<meta name="napplet-root" content="35129:PUBKEY:ROOT_D">` |

- Repeat `napplet-archetype`, `napplet-intent`, `napplet-server` for multiple tags.
- Each intent is its queryless identity then parameter names, ASCII-whitespace separated.
  `napplet-requires` / `napplet-optional` are whitespace-separated bare domains, one `R`/`O` each.
- Icon links SHOULD use data URLs. The icon hash derives from decoded image bytes, not the URL.
  Publish the same bytes to the declared Blossom servers.
- `x` and signing fields are not embedded. Publishers MUST finalize embedded metadata **before**
  computing `x` (embedded metadata is part of the digest).
- Embedding is optional. Runtimes MUST NOT require it, and MUST NOT let it override the signed
  manifest or runtime domain availability.

## 6. Identity and load sequence

Identity is `(dTag, artifactHash)`. A `d` tag alone is not publisher-scoped. The hash covers
artifact bytes only.

NIP-5D's tuple is not enough for the NAP scopes. NAP-STORAGE, NAP-RESOURCE and NAP-CONFIG scope
by a **manifest key** (named: publisher, kind, `d`; root: publisher, kind; snapshot: signed event
id) plus `artifactHash`, and NAP-INTENT catalog identifiers use the same key. Neither spec states
the reconciliation, but both say the runtime derives these from "the authenticated endpoint's
verified manifest and artifact". The kehto runtime binds a permission principal
`(manifestKey, artifactHash)` with `manifestKey` = `nip5d:35129:<pubkey>:<d>`,
`nip5d:15129:<pubkey>` or `nip5d:5129:<event id>` (`@kehto/nip` `getNappletCatalogId`).

1. The runtime MUST compute identity from the napplet's own bytes and MUST NOT accept it from a host.
2. Before creating the iframe, the runtime MUST:
   a. resolve the manifest (5129, 15129 or 35129) from relays and verify its signature;
   b. read the single `x` tag, rejecting a manifest without exactly one;
   c. fetch the artifact from Blossom by that sha256 and verify `sha256(blob) == x` (gives `artifactHash`);
   d. inject the verified bytes via `srcdoc`, never a navigated `src`, together with the bootstrap;
   e. bind `(dTag, artifactHash)` to the port in the first valid `napplet.hello` from that iframe's `Window`.
3. A gateway MAY serve bytes. The runtime MUST verify its output against the signed manifest.
   Gateways are never trusted.
4. The shell MUST accept at most one `napplet.hello` per iframe.
5. The shell MUST treat the verified document as replaced on: a second `napplet.hello` or any
   other window-level message from that iframe after handoff; a second `load` event; the port
   closing or erroring.
6. On any of those the shell MUST close the port, revoke the identity binding and every grant
   and session attached to it, and remove the iframe.
7. `close()` MUST be explicit on every teardown path, including paths that also remove the iframe.
8. The shell MAY create a fresh iframe from the verified bytes afterward.
9. The shell MUST NOT process NAP messages from any source other than the bound port.
10. The shell MUST NOT re-bind a napplet identity to an existing iframe.

Changing hash scheme changes identity keys even for identical bytes. SDKs do not silently
migrate saved data or grants. Legacy path/aggregate (NIP-5A style) manifests are accepted only
through an isolated adapter.

## 7. Sandbox and transport

### 7.1 Sandbox

- Napplet iframes MUST use `sandbox="allow-scripts"`, loaded via `srcdoc`.
- `allow-same-origin` MUST NOT be present (load-bearing precondition for isolation). The shell
  MAY add other tokens (`allow-forms`, `allow-popups`) per policy.
- The napplet cannot reach shell DOM, cookies, `localStorage`, `sessionStorage`, IndexedDB,
  service workers, or arbitrary `fetch`/`WebSocket` targets.
- Shells MUST NOT provide `window.nostr` (NIP-07) or any signing or encryption primitive.
- Shells MUST inject `window.napplet` before any napplet script runs (classic, module and dev
  wrappers included). The namespace MUST contain only the NAP domain objects exposed to that napplet.

### 7.2 Transport

1. Before any napplet script runs, the bootstrap MUST create a `MessageChannel`, retain one port
   privately (it MUST NOT be reachable from napplet code), and transfer the other to the shell
   exactly once: `window.parent.postMessage({ "type": "napplet.hello" }, '*', [port])`.
   The `'*'` target origin is required (opaque origin).
2. All NAP messages in both directions MUST travel over the port.
3. Shells MUST NOT send NAP messages via `iframeWindow.postMessage`, and MUST NOT transfer a
   port into the iframe themselves.
4. The shell accepts `napplet.hello` only when `MessageEvent.source` is the `contentWindow` of an
   iframe it created and exactly one port is attached. Sender identity is `MessageEvent.source`,
   NOT `event.origin`. Messages from unknown sources MUST be silently dropped.
5. Shells SHOULD verify the bootstrap's port unreachability in CI (scan `window` and the
   injected namespace).

## 8. Wire format

- Each message is one JSON object with a `type` of the form `domain.action`.
- Request/response pairs share an `id`; the result type is the request type plus `.result`.
  Fire-and-forget and pushed messages omit `id`.
- The runtime MAY push unsolicited messages.
- Messages with an unrecognised `type` MUST be silently ignored (prevents capability probing and
  lets napplets run on smaller shells).
- NIP-5D does not enumerate type strings; each NAP does.
- Base TypeScript type: `NappletMessage` in `@napplet/core`.

```json
{ "type": "relay.publish", "id": "a1", "event": { } }
{ "type": "relay.publish.result", "id": "a1", "ok": true }
```

### 8.1 Convention URI binding (web projection)

For operations taking a convention URI (`napplet:<archetype>/<intent>[?params][#<naddr>]`) the
binding, before sending: extracts any NAP-INTENT handler fragment into `handlerHint`; removes
the query from the stable identity; percent-decodes each unique `name=value` pair as text into
the payload. It MUST NOT coerce scalar types or form-decode (`+` stays literal). It MUST reject
malformed percent-encoding, repeated names, and a query combined with an explicit payload. The
`#<naddr>` fragment is accepted only by `intent.invoke`; other operations (including NAP-INC)
reject fragments.

For `intent.invoke`, the binding decodes the bare `naddr1…` (kind 35129 only) into
`request.handlerHint.address` and optional `request.handlerHint.relays`. The raw fragment MUST NOT
appear in the wire convention or payload. A queryless invocation MAY combine the fragment with an
explicit structured payload. The fragment is a recommendation, not an explicit handler selection.
The shell receives normalised identity and payload fields; routing uses exact equality over the
queryless, fragment-free identity.

The web projection defines no generic promise, timeout or subscription-handle semantics; each NAP
defines its own (see section 15).

## 9. Capabilities and domain availability

- `["R", "<domain>"]` required, `["O", "<domain>"]` optional. Bare domain names.
- At load the shell checks the complete `R` set against domains it can expose to that napplet.
  If one is absent the shell SHOULD reject the napplet or warn that full functionality is
  unavailable. Missing `O` domains MUST NOT by themselves block loading. No `R` means none required.
- `R` and `O` are declarations, never grants; they MUST NOT widen exposure. Actual availability
  is the injected namespace, i.e. shell policy.
- If `window.napplet.<domain>` is present the domain is exposed. If absent the napplet MUST
  degrade gracefully or stop using it. Presence is only an availability signal; operations,
  payloads, errors and versioning belong to the NAP. A domain needing version negotiation or
  diagnostics MUST define it in its own NAP.
- Indexing: `#R`, `#O` (NIP-01); proposed NIP-91 `&R`, `&O`. Compatibility is
  `R ⊆ runtime capabilities`, but `&R` tests `filter values ⊆ event R`, so `&R` can miss
  compatible napplets and return incompatible ones. Clients MUST inspect the complete `R` set
  locally; `&R` is only a discovery optimisation. `O` does not constrain compatibility.

## 10. Archetypes and intents

- Manifest declares `["z", "<archetype>"]` and `["i", "<intent>", "<param>", ...]`.
- An intent is a stable queryless convention identity for one action (`napplet:feed/open`,
  `napplet:feed/edit`). Vocabulary, identities and payload semantics live outside NIP-5D (archetype
  registry and NAP-INTENT). The NAAT registry is deprecated.
- Example conventions: `napplet:profile/open`, `napplet:note/open`, `napplet:dm/open`,
  `napplet:feed/open`, `napplet:stream/switch`.

## 11. Shell handlers (kind 31990)

A shell MAY advertise itself via NIP-89 kind 31990. `k` = manifest kinds it handles, `N` = domains
it can expose.

```
["k", "<manifest-kind>"]                    5129 | 15129 | 35129
["N", "<nap-name>"]                         bare domain, same vocabulary as R/O
["web", "<url-template>", "<nip-19-entity>"]
```

- `web`: shell SHOULD provide at least one. Clients replace `<bech32>` with an `naddr` (root or
  named) or `nevent` (snapshot). `content` and `d` keep NIP-89 meanings.
- Compatibility: full functionality when manifest `R` ⊆ shell `N`.
- Discovery filter: `{"kinds":[31990],"#k":["35129"],"&N":["relay","storage"]}`. Clients served
  by the `#N` fallback MUST still check the complete `R` set against `N` locally.
- Recommendations: NIP-89 kind 31989, `d` = a manifest kind, `a` tags to handler events.
- `N` tags are advertisements, not grants. A handler event MUST NOT widen what a shell exposes or
  replace the load-time `R` check, and plays no part in identity verification. A missing or
  malformed handler event MUST NOT prevent playback in a shell the user already opened.

```json
{
  "kind": 31990,
  "content": "{\"name\":\"Example Shell\",\"picture\":\"https://shell.example.com/icon.png\"}",
  "tags": [
    ["d", "7d8a1f"],
    ["k", "35129"], ["k", "5129"],
    ["N", "relay"], ["N", "storage"], ["N", "theme"],
    ["web", "https://shell.example.com/open/<bech32>", "naddr"],
    ["web", "https://shell.example.com/open/<bech32>", "nevent"]
  ]
}
```

## 12. NAP extension framework

- Each NAP owns one message domain (`foo` owns `foo.*`, e.g. `foo.bar`, `foo.bar.result`) and
  defines its type strings, payload shapes, injected-object behaviour and semantics.
- A NAP is self-contained; it references NIP-5D only for namespace injection, envelope and transport.
- NAPs MUST define all valid `type` strings, the payload shape per type, expected shell behaviour
  per message, and be independently implementable. A shell MAY support any subset.
- **Boundary rule**: "Only runtime-provided API surfaces are NAPs." A NAP is runtime-provided and
  defines an API surface. A convention is napplet-agreed and defines message semantics.
- Every NAP-WORD is optional. NAP-SHELL is not a prerequisite for domain discovery. A NAP's
  `Depends:` block always names domains, never spec ids.
- Licence CC0-1.0.

### 12.1 Governance

- Fork, add `naps/NAP-<WORD>.md` from the interface template, open a PR. Discussion in PR comments.
- Maintainers merge when the spec has been implemented, defended and has stabilised. No formal
  stages, committees or voting. NAP-WORD names are first-come-first-served, subject to maintainer
  approval. PR labels seen: DRAFT, IMPLEMENTED, STABLE, NEEDS WORK, MAY RENAME, MAY DEFER,
  DEFERRED, EXPERIMENTAL, TOO VERBOSE.
- An authoring skill exists at `skills/nap-authoring/SKILL.md` (`npx skills add napplet/naps`).

### 12.2 NAP-WORD template (required section order)

1. Header: `NAP-{NAME}`, title, status `draft`; **NAP ID**; **Domain** `` `{name}` ``; **Depends**
   (omit if none; otherwise bullets `<domain>` — wire|capability|layering · required|optional —
   the concrete field or method relied on); **Web binding** `window.napplet.{name}`.
2. **Description**: one paragraph; what the shell provides and the napplet consumes.
3. **API Surface**: language-neutral table `Operation | Parameters | Result | Wire`, then
   **Schemas** tables `Field | Required | Type | Notes`, then per-method notes.
4. **Wire Protocol**: `{name}.*` messages in NIP-5D format; table `Type | Direction | Payload
   fields`; request/result correlate by `id`; fire-and-forget has no `id`; shell pushes use
   domain-specific routing fields. **Examples** and **Error Handling** (typically an `error` field).
5. **Shell Behavior**: MUST/MAY bullets. Baseline: "The shell MUST respond to every request with a
   result message carrying the same id." The shell MAY enforce ACL checks.
6. **Security Considerations**: the shell is the subject of crypto/trust MUSTs; napplets do not
   sign or verify.
7. **Implementations**.

Dependency kinds: **wire** (a type crosses the seam), **capability** (a result may be used with
another domain), **layering** (the shell may implement it using another domain internally).

### 12.3 Convention template

Header `napplet:{archetype}/{intent}`, **Convention**, **Invocation** `napplet:{archetype}/{intent}[...?params]`,
optional **Depends** (semantic dependencies only; `inc` and `intent` are carriers, not
dependencies). Sections: Description; Payload (identity is queryless and fragment-free; the
convention MUST name every supported query field; structured or non-text data uses the explicit
payload; `#<naddr>` MUST NOT appear in payload schemas, advertised identities or subscriptions);
Schemas; Behavior (producer and consumer requirements); Discovery (`z`/`i` tags or
`intent.available()` candidate contracts; trailing `i` values name parameters, not types);
Implementations. Producer = napplet invoking; consumer = napplet receiving, directly or via the
runtime by archetype. No registry edit is needed before two napplets can try a compatible payload.

### 12.4 Implementation maturity (non-normative, `@napplet/*` packages)

Two independent signals, neither encoded in manifests, HTML, the namespace or the wire:

- **Proposal status** (as of `proposal.checkedAt`): `merged`, `in-review`, `draft`, `unknown`.
- **Implementation maturity**: `supported` (maintained and tested, API not frozen),
  `experimental` (deliberate evaluation, likely to change), `exploratory` (early, explores a draft).
  Deferred or rejected proposals are retired, not offered as a tier. Unclassified domains are
  excluded. Experimental status never waives conformance requirements.

Selection and injection:

```js
import { selectNapDomains } from '@napplet/core';
const { domains, excluded } = selectNapDomains({ candidates: [...], optIn: ['llm'] });
// excluded reasons: 'unknown-domain' | 'unclassified' | 'maturity-not-allowed'
// allowedMaturities defaults to ['supported']; [] allows only named opt-ins
import { renderNappletRuntimePreludeCall } from '@napplet/shim/prelude';
// inline @napplet/shim/prelude.global, then the activate call, before any napplet script
```

- The legacy root `@napplet/shim` entry installs every bundled domain on import; do not use it for
  policy-controlled injection. The prelude has no install-on-import side effect.
- **Shim filtering is not a security boundary**: a napplet can `postMessage` directly. Hosts must
  apply `selection.domains` to the endpoint's dispatch allowlist as well as to namespace
  injection, and keep source identity checks and per-operation authorisation.
- Classifications live in `packages/core/src/nap-catalog.ts`; a daily workflow refreshes proposal
  status on a draft PR. The catalog includes domains (e.g. `llm`, `ble`) absent from the registry.

### 12.5 Principles (SOUL.md)

- The user composes: workspace, preferences and handler defaults belong to the user; a napplet's
  recommendation stays a recommendation.
- Authority has an owner: the napplet designs, the shell mediates, the runtime executes, the user
  composes.
- Small tools deserve complete contracts: operation, result, error, dependency and trust boundary.
- Trust comes from evidence: distinguish a proposal from supported behaviour, and an accepted
  request from its eventual effect.
- Keep user identity distinct from napplet identity. Declarations, advertisements and supplied
  identities never grant authority. Keep contracts language-neutral and transport-independent
  ("transport-agnostic, not Nostr-agnostic"); browser details belong in the web projection.

## 13. Shell (runtime) responsibilities

MUST: verify manifest signature and artifact hash before execution; create sandboxed iframes as
specified; accept the single hello and bind identity to the port; tear down on revocation triggers;
inject only supported domains; enforce capability, consent and storage policy by verified identity;
never expose keys, wallet credentials or raw network; never sign or broadcast events containing
ciphertext received from a napplet.

MAY: expose any subset of domains; broker signing via NIP-46 remote signer, NIP-07 extension or
own key management; scope storage per napplet; gate signing, payments, uploads and relays by
per-napplet policy; implement the `shell` domain; set its own intent-resolution, startup, reuse
and retry policy.

### 13.1 Kehto runtime toolkit

- `@kehto/runtime`: browser-agnostic; handles protocol messages after the host identified the
  source window/session. Owns no DOM, iframe creation, `localStorage` or listeners.
- `@kehto/shell`: browser adapter; owns the `message` listener, source lookup, gateway loading,
  hosted `shell.ready`/`shell.init`, registries.
- Dispatch, ACL gates, service routing and state belong in runtime code; service behaviour behind
  `@kehto/services` factories or host callbacks.
- Alpha: the implementer still owns envelope security, process isolation and performance.

## 14. Napplet-side API

```js
if (window.napplet?.relay) { /* feature gate */ }

const result = await window.napplet.intent?.open('napplet:profile/open', {
  payload: { pubkey: 'abc123' },
  behavior: { focus: true, reuse: false },
});
if (!result?.ok) throw new Error(result?.error ?? 'intent not accepted');

window.napplet.intent?.onDelivery(({ sender, convention, payload }) => { /* ... */ });
```

Domain objects named in SDK docs: `relay`, `outbox` (query/subscribe/publish), `inc`
(topics/channels), `storage` (get/set/remove), `resource` (bytes/bytesMany), `identity`,
`intent`, `theme`, `keys`, `services`. Names have shifted between releases.

## 15. NAP registry and specs

All Draft except NAP-CLASS and NAP-CONNECT (Deferred). Implementations: none listed yet.

| NAP | Domain | Depends on | Summary |
|---|---|---|---|
| SHELL | `shell` | none | Environment and readiness |
| INTENT | `intent` | none | Convention delivery from manifest advertisements |
| INC | `inc` | none | Inter-napplet communication, authenticated endpoints |
| THEME | `theme` | none | Shell-provided themes |
| RELAY | `relay` | resource | Relay proxy: subscribe, publish, query, publishEncrypted |
| IDENTITY | `identity` | resource | Read-only identity queries |
| STORAGE | `storage` | none | Scoped key-value storage |
| KEYS | `keys` | none | Keyboard forwarding, action keybindings |
| MEDIA | `media` | resource | Media session control |
| NOTIFY | `notify` | none | Shell-rendered notifications |
| RESOURCE | `resource` | none | Sandboxed fetch (https, blossom, nostr, data) |
| CONFIG | `config` | none | Per-napplet declarative config (JSON Schema) |
| UPLOAD | `upload` | relay | Upload (NIP-96, Blossom) |
| VALUE | `value` | relay | Value transfer, zaps |
| OUTBOX | `outbox` | relay | Outbox-aware routing and queries |
| CVM | `cvm` | value | ContextVM / MCP-over-Nostr bridge |
| LINK | `link` | none | External link opening |
| POW | `pow` | identity, relay, outbox | NIP-13 miner |
| DISPLAY | `display` | none | Runtime-controlled pixel displays |
| CLASS | `class` | none | Deferred |
| CONNECT | `connect` | none | Deferred; user-gated direct network |

Extra domains named in SDK README, status unknown: `navigation`, `gamepad`, `llm`, `blossom`,
`catalog`, `torrent`, `soulseek`.

### 15.0 Where each spec lives

| NAP | Location | PR state / labels |
|---|---|---|
| SHELL, INTENT, INC, THEME, IDENTITY | `master` (`naps/`) | merged (PRs #101, #91, #104, #8, #12) |
| RELAY | PR #2, branch `nub-relay` | open; DRAFT, IMPLEMENTED, MAY RENAME |
| STORAGE | PR #3, branch `nub-storage` | open; DRAFT, IMPLEMENTED |
| KEYS | PR #9, branch `nub-keys` | open; DRAFT, STABLE, IMPLEMENTED |
| MEDIA | PR #10, branch `nub-media` | open; DRAFT, STABLE, IMPLEMENTED |
| NOTIFY | PR #11, branch `nub-notify` | open; DRAFT |
| CONFIG | PR #14, branch `nub-config` | GitHub draft; DRAFT, MAY DEFER |
| CLASS | PR #16, branch `nub-class` | draft; DEFERRED |
| CLASS-1 / CLASS-2 | PRs #17 / #18 | draft; DEFERRED |
| CONNECT | PR #19, branch `nub-connect` | draft; DEFERRED |
| VALUE | PR #30, branch `nap-value` | draft; DRAFT, NEEDS WORK |
| CVM | PR #31, branch `nap-cvm` | open; DRAFT, IMPLEMENTED, NEEDS WORK, TOO VERBOSE |
| OUTBOX | PR #32, branch `nap-outbox` | open; DRAFT, IMPLEMENTED |
| UPLOAD | PR #33, branch `nap-upload` | open; DRAFT, IMPLEMENTED |
| POW | PR #39, branch `nap-pow` | open; DRAFT |
| LINK | PR #53, branch `nap-link` | open; DRAFT; changes requested |
| RESOURCE | PR #80, branch `nub-resource` | open; DRAFT, IMPLEMENTED, STABLE (earlier merge #13 reverted by #79) |
| DISPLAY | PR #97, branch `nap-display` | draft; DRAFT, EXPERIMENTAL |

Raw spec URL pattern: `https://raw.githubusercontent.com/napplet/naps/<branch>/naps/NAP-<WORD>.md`.

### 15.1 NAP-SHELL (`shell`, optional)

- `supports(domain)`: boolean, local, works before `shell.init`, no wire message.
- `services()`: list of text; empty until `shell.init`.
- `ready()`: resolves a `ShellEnvironment` after `shell.ready`/`shell.init`.
- `onReady(handler)`: one-shot; late handlers receive the retained environment.
- Wire: `shell.ready` (napplet to runtime, no fields); `shell.init` (runtime to napplet:
  `capabilities`, `services`). Neither carries `id`.
- Schemas: `ShellCapabilities{domains[] R}`; `ShellEnvironment{capabilities R, services R}`.
- No errors defined; a napplet MAY stop waiting under its own timeout.
- MUST: when exposed, the binding installs its receiver before sending `shell.ready`. Runtime
  sends `shell.init` exactly once per endpoint, in response to the first `shell.ready`;
  duplicates create no new session. Environment describes only that napplet's domains and
  services. Runtime MUST NOT gate other domains on this exchange. The signal is untrusted, not a grant.

### 15.2 NAP-INTENT (`intent`)

Operations and wire:

- `invoke(uri, options?)`: `intent.invoke` {id, request} / `intent.invoke.result` {id, result}.
- `open(uri, options?)`: sugar over invoke; URI intent MUST be `open`.
- `available(archetype)`: `intent.available` {id, archetype} / `.result` {id, availability, error?}.
- `handlers()`: `intent.handlers` {id} / `.result` {id, handlers, error?}.
- `onChanged(handler)`: push `intent.changed` {availability}.
- `onDelivery(handler)`: push `intent.deliver` {delivery}, no id.

Schemas (R = required):

- `IntentRequest`: archetype R, action R, convention R; payload, handler, handlerHint, behavior optional.
- `IntentInvokeOptions`: payload, handler, handlerHint, behavior (all optional).
- `IntentHandlerHint`: address R (`35129:<pubkey>:<d>`), relays optional. Kind 35129 only; `d`
  is case-sensitive and MUST NOT be normalised.
- `IntentBehavior`: `focus`, `reuse` (optional bool hints).
- `IntentResult`: ok R; archetype, action, convention, handler required when ok; error required when not ok.
- `IntentCandidate`: id R, actions R, conventions R, contracts R; title, isDefault optional.
- `IntentContract`: convention R, params R (may be empty).
- `IntentAvailability`: archetype R, available R, candidates R, hasDefault R.
- `IntentDelivery`: sender R, archetype R, action R, convention R; payload optional.

Handler resolution, "The shell MUST apply this precedence":

1. An explicit authorised `handler` catalog identifier, or a `handler: "choose"` selection.
2. The user's applicable default handler.
3. The recommended handler, if policy permits and it supports the archetype, action and convention.
4. Normal installed-handler resolution or user choice.

Absent `handler` or `"default"` uses steps 2-4. An explicit selection MUST NOT silently fall back
to the recommendation. An unavailable, unsupported, declined or policy-denied recommendation MUST
fall back to step 4. A hint MUST NOT alter the user's default.

Convention rules: binding MUST reject malformed percent-encoding, duplicate decoded query names,
invalid fragments, query plus `options.payload`, fragment plus `options.handlerHint`. The runtime
MUST reject unless the convention is exactly queryless, fragment-free `napplet:<archetype>/<action>`.
Manifest advertisements are `["z","<slug>"]` and `["i","napplet:<slug>/<action>",params...]`;
matching is exact string equality; advertisements are hints, not grants.

Errors: `"invalid convention"`, `"no handler"`, `"unsupported convention"`, `"user cancelled"`,
`"invoke rejected"`.

Security/MUST: runtime derives `sender` from the authenticated endpoint; a napplet cannot set or
change the default; a caller MUST NOT address a handler instance unless the user authorised it;
`ok:true` means delivery responsibility accepted; `intent.invoke.result` MUST precede closing the
source; binding buffers deliveries until `onDelivery` is registered; delivery MUST NOT leak payload
or sender to non-target napplets; the target MUST validate payload. Target startup, reuse, retry
and persistence are runtime policy.

### 15.3 NAP-INC (`inc`)

Topics (pub/sub):

- `emit(topic, payload?)`: `inc.emit` {topic, payload?}; no id, no response.
- `on(topic, cb)`: `inc.subscribe` {id, topic} / `inc.subscribe.result` {id, error?};
  `inc.unsubscribe` {topic}; delivery `inc.event` {topic, sender, payload?}.

Channels (point-to-point):

- `channel.open(target)`: `inc.channel.open` {id, target} / `.result` {id, channelId?, peer?, error?};
  target receives `inc.channel.opened` {channelId, peer}.
- `channel.onOpened(cb)`, `channel.list()` (`inc.channel.list` {id} / `.result` {id, channels}),
  `channel.broadcast(payload)` (`inc.channel.broadcast`, no id).
- `ChannelHandle`: `emit` (`inc.channel.emit` {channelId, payload?}), `on` (`inc.channel.event`
  {channelId, sender, payload?}), `onClosed` (`inc.channel.closed` {channelId, reason?}),
  `close` (`inc.channel.close` {channelId}).

Schemas: `IncEvent{topic R, sender R, payload}`, `ChannelHandle{id R, peer R}`,
`ChannelEvent{channelId R, sender R, payload}`, `ChannelClosed{channelId R, reason}`,
`ChannelInfo{id R, peer R}`. Errors e.g. `"topic rejected by ACL"`, `"target not found"` (no
channel created on error).

Transposition on emit: remove query, percent-decode pairs into a text-to-text payload map; no
coercion; reject fragment, malformed encoding, repeated names, or explicit payload with query.
Structured data MUST use an explicit payload with a queryless topic.

MUST/security: exact string match on the full topic (shell MAY intercept `shell:*`); shell copies
topic unchanged; no delivery back to the emitter; `sender` derived from the authenticated endpoint;
target must exist and be live before open; `inc.channel.opened` MUST be enqueued before a successful
open result; auth checked once at open, not per message; shell MUST send `inc.channel.closed` to
both sides on close, iframe removal or ACL revocation (reason `"peer destroyed"` on endpoint
destruction); binding retains buffered events and the terminal closed record until a handler
registers, and on overflow MUST close the channel and notify both sides; broadcast excludes the
sender and SHOULD NOT carry sensitive data; topic namespaces are not enforced, receivers SHOULD
check `sender`. A compromised extension forging channel messages is an accepted trust boundary.

### 15.4 NAP-THEME (`theme`)

- `get()`: `theme.get` {id} / `theme.get.result` {id, theme, error?}.
- `onChanged(handler)`: push `theme.changed` {theme}. No wire subscribe; closing a handle only
  removes the local handler.
- Schemas: `ThemeColors{background R, text R, primary R}` (hex text); `ThemeFont{name R, url R}`;
  `ThemeFonts{body, title}`; `ThemeBackground{url R, mode R (CSS background-size), mime R}`;
  `Theme{colors R, fonts, background, title}`.
- Errors: any result MAY carry `error` (e.g. `"no active theme"`); other fields undefined then.
- MUST: answer `theme.get` with the same id; include all three colour fields in every payload;
  broadcast `theme.changed` only to napplets with `theme` exposed; MUST NOT infer grants from
  manifest R/O. Napplets MUST NOT assume external font/background URLs load, SHOULD fall back to
  colours and SHOULD validate hex. Read-only. Kind 16767 mapping is informational.

### 15.5 NAP-IDENTITY (`identity`, optional dep on `resource`)

| Operation | Wire | Returns |
|---|---|---|
| `getPublicKey()` | `identity.getPublicKey` {id} / `.result` {id, pubkey} | text, `""` if no signer |
| `onChanged(h)` | push `identity.changed` {pubkey} | |
| `getRelays()` | `identity.getRelays` / `.result` {id, relays, error?} | RelayMap |
| `getProfile()` | `identity.getProfile` / `.result` {id, profile?, error?} | ProfileData or null |
| `getFollows()` | `identity.getFollows` / `.result` {id, pubkeys, error?} | kind 3 |
| `getList(type)` | `identity.getList` {id, listType} / `.result` {id, entries, error?} | entries |
| `getZaps()` | `identity.getZaps` / `.result` {id, zaps, error?} | kind 9735 receipts |
| `getMutes()` | `identity.getMutes` / `.result` {id, pubkeys, error?} | kind 10000 |
| `getBlocked()` | `identity.getBlocked` / `.result` {id, pubkeys, error?} | pubkeys |
| `getBadges()` | `identity.getBadges` / `.result` {id, badges, error?} | NIP-58 |

Schemas: `RelayPermissions{read R, write R}`; `ProfileData{name, displayName, about, picture,
banner, nip05, lud16, website}` all optional; `ZapReceipt{eventId R, sender R, amount R (msats),
content}`; `Badge{id R, awardedBy R, name, description, image, thumbs}`.

Errors: `"relay timeout"`, `"not found"`, `"unsupported list type"`. `getPublicKey.result` MUST NOT
include `error`. A null profile is not an error.

MUST/security: same id in replies; every shell MUST support `getPublicKey`; shell MUST emit
`identity.changed` on change including `""` on sign-out; napplets MUST NOT depend on an initial
push and SHOULD NOT poll `getPublicKey`; shell MUST NOT expose the private key, signing,
encryption or decryption (signing goes via NAP-RELAY); shell MAY ACL-restrict lists and MAY redact
mutes, blocks and zaps. Read-only.

### 15.6 NAP-RELAY (`relay`; depends: `resource` wire optional)

Operations (all async, correlated):

| Operation | Wire | Result |
|---|---|---|
| `subscribe(filters, options?)` | `relay.subscribe` + pushes `relay.event`, `relay.eose`, `relay.closed` | Subscription handle streaming `RelayEventResult`, with `close()` |
| `publish(template)` | `relay.publish` / `.result` | signed `NostrEvent` (shell signs) |
| `publishEncrypted(template, recipient, encryption?)` | `relay.publishEncrypted` / `.result` | signed `NostrEvent`; default NIP-44, NIP-04 fallback |
| `query(filters)` | `relay.query` / `.result` | list of `RelayEventResult` (collect until EOSE, then close) |
| `Subscription.close()` | `relay.close` | none |

Schemas: `NostrFilter`, `NostrEvent`, `EventTemplate` = open maps; `RelayEncryption` = `"nip44" | "nip04"`;
`RelayEventResult{event R, sidecar?}`; `RelayEventSidecar{resources? [ResourceSidecarEntry], relayHints? [tstr]}`;
`RelaySubscribeOptions{relay?}`. `ResourceSidecarEntry` is imported from NAP-RESOURCE and MUST NOT be redefined.

Wire (R = required, O = optional):

| Type | Dir | Fields |
|---|---|---|
| `relay.subscribe` | → | id R, subId R, filters R (array), relay O |
| `relay.close` | → | id R, subId R |
| `relay.publish` | → | id R, event R (template) |
| `relay.publishEncrypted` | → | id R, event R, recipient R (hex pubkey), encryption O |
| `relay.query` | → | id R, filters R |
| `relay.event` | ← | subId R, result R |
| `relay.eose` | ← | subId R |
| `relay.closed` | ← | subId R, reason O |
| `relay.publish.result` / `relay.publishEncrypted.result` | ← | id R, ok R, event O, eventId O, error O |
| `relay.query.result` | ← | id R, events R (MAY carry `error` instead) |

No error code list; example `"blocked: content policy violation"`.

Shell MUST: forward subscriptions to its pool and deliver `relay.event`; send `relay.eose` when
stored events are exhausted; honour `relay.close`; sign `publish` templates and return the signed
event; encrypt and sign `publishEncrypted`; **decrypt incoming NIP-04/NIP-44 events before
delivery** ("napplets receive plaintext content"); answer `query` after EOSE; reply to every
request with the same `id`/`subId`. MAY send `relay.closed`, enforce read/write ACLs, support
scoped `relay` connections, manage its pool. SHOULD include `relayHints` when disclosable.

Sidecar pre-resolution: shells MAY attach sidecar metadata; it is not part of the event and MUST
NOT be written back into it. Pre-resolution is optional and **MUST NOT be enabled by default**;
SHOULD honour per-napplet, per-kind and per-host opt-out, and an opt-out MUST prevent the fetch.
`relayHints` are advisory and MUST NOT bypass relay policy. When `sidecar.resources` is non-empty
the shim MUST hydrate its `resource.bytes` cache before delivering the event; an existing cache
entry is authoritative. Sidecar MIME MUST be shell-sniffed; SVG MUST be rasterised; all NAP-RESOURCE
safety properties apply. Pre-fetching arbitrary URLs from kinds 1, 4, 1059 is discouraged; SHOULD
use allowlists.

Security: napplet never sees ciphertext or keys; shell MAY inspect content before signing; scoped
relay URLs SHOULD be validated against SSRF; filters SHOULD be bounded.

Open issues (PR review): decrypted delivery conflicts with "raw event" (replacing `content` breaks
the signature; a `view` form `{form:"decrypted", ref, view:{pubkey,kind,content}}` was proposed);
`relay.close` and refused `subscribe` have no defined reply; NIP-59 gift-wrap decryption depth
undefined; a `stream: true` option for paged `query` proposed but absent; NIP-04 fallback
downgrade (implementation fails closed).

### 15.7 NAP-STORAGE (`storage`; no deps)

| Operation | Wire | Result |
|---|---|---|
| `getItem(key)` | `storage.get` / `.result` {id, value: string or null} | string or null |
| `setItem(key, value)` | `storage.set` / `.result` {id} | none; throws on quota |
| `removeItem(key)` | `storage.remove` / `.result` {id} | none; no-op if absent |
| `keys()` | `storage.keys` / `.result` {id, keys[]} | list |
| `instance.getItem/setItem/removeItem/keys` | same, with `scope: "instance"` | |

Requests carry `id` R, `key` R (where applicable), `value` R (set), `scope` O (`"shared"` default
or `"instance"`). Results carry no `scope`. Any result MAY carry `error`; other fields are then
undefined, e.g. `{"type":"storage.set.result","id":"b2","error":"quota exceeded"}`. Values are
strings only.

Identity scope: the runtime MUST derive scope from the verified manifest and artifact: named =
(publisher, kind, d); root = (publisher, kind); snapshot = signed event id; plus `artifactHash`.
A bare `d` MUST NOT identify a scope. A napplet MUST NOT supply or override identity fields.
Different publishers, keys and hashes MUST stay isolated.

Instance scope: instances MUST NOT share or read each other's instance keys; the same instance
MUST resolve to the same namespace across reloads; instance identification is unspecified and
never visible to the napplet; the shell MAY reclaim it on destroy.

Shell MUST: scope by verified identity; isolate per instance for `"instance"`; treat absent or
`"shared"` as napplet-wide; enforce a per-napplet quota (recommended **512 KB**, UTF-8 bytes);
persist across reloads; reply with the same `id`; return `error` for quota and invalid requests.
MAY enforce `storage:read`/`storage:write` ACLs. SHOULD NOT parse or execute stored content.
Keys and values are visible to the shell; confidential data SHOULD be encrypted by the napplet.

Open issue: a maintainer comment says per-call scope was replaced by a declarative "instanceable"
capability with no wire change, but the branch still carries `scope` and `instance.*` (related
PRs #42 closed, #43 merged).

### 15.8 NAP-RESOURCE (`resource`; no deps)

| Operation | Wire | Result |
|---|---|---|
| `info()` | `resource.info` {id} / `.result` {id, info} / `.error` {id, error, message?} | `ResourceInfo`; advisory, MUST NOT be a required preflight |
| `bytes(url)` | `resource.bytes` {id, url} / `.result` {id, blob, mime} / `.error` | one complete byte sequence |
| `bytesMany(urls)` | `resource.bytesMany` {id, urls} / `.result` {id, items} / `.error` | ordered per-URL results; `urls` non-empty |
| cancel | `resource.cancel` {id} | late terminal envelopes for cancelled ids MUST be dropped |

Every request gets exactly one terminal result or error envelope unless cancelled. `message` is
diagnostic only; programmatic handling uses `error`.

Schemas: `ResourceSchemeInfo{scheme R, enabled R}`; `ResourceInfo{schemes R, maxBytes?, maxUrls?}`;
`ResourceBytesItem{url R, ok R, blob?, mime?, error?, message?}` (ok:true MUST include blob and
mime; ok:false MUST include error and MUST NOT include blob); `ResourceSidecarEntry{url R, blob R, mime R}`;
`ResourceBytes` = canonical padded base64 (RFC 4648 §4, standard alphabet, `=` padding, no
whitespace, no data-URL prefix; empty bytes = `""`; non-canonical MUST be rejected; e.g. bytes
`00 01 02 ff` = `"AAEC/w=="`). Host byte objects MUST NOT appear on the wire.

Rules: `items` MUST preserve input order and length; each URL is processed as an independent
`bytes` and one failure MUST NOT discard siblings; MUST NOT grant raw network or expose upstream
`Content-Type`; a projection MUST enforce direct-network denial before exposing this domain; MIME
MUST be runtime-sniffed; complete bytes only (no streaming, ranges, progress); cache keys are
byte-equal URL strings; cache is scoped to verified identity (same rules as STORAGE).

Schemes:

| Scheme | Rule |
|---|---|
| `data:` | MAY decode in shim; still size-limited, sniffed, SVG-rasterised, quota- and policy-checked |
| `https:` | runtime fetch under full default policy |
| `blossom:` | BUD-10 `blossom:<sha256>.<ext>`; runtime MUST verify SHA-256; `xs`/`as`/`sz` hints advisory |
| `hashtree:` / `htree:` | `hashtree:<nhash>` (immutable, HTS-01 §6.2–6.3; bare nhash alias) and `htree://<npub-or-hex>/<tree>[/<path>][#k=<64-hex>]` (mutable, HTS-01 §9); verify root, nodes, chunks, CHK decryption; MUST NOT leak keys; `#private` subject to authorisation; `#link-visible` MUST be rejected; queries, bad escapes, unknown fragments, colon paths, directories = `invalid-request`; advertise both scheme names |
| `nostr:` | NIP-19; one hop; MUST NOT follow URLs or nostr refs in the result |
| `http:` | not canonical; MUST NOT be enabled by default |
| other | MUST return `unsupported-scheme` |

`info.schemes` reports disclosure only and grants nothing.

Default resource policy:

| Rule | Level | Detail |
|---|---|---|
| Private IP block | MUST | after DNS, before connect, every redirect; RFC1918, loopback, link-local, ULA, 169.254.169.254 |
| MIME sniffing | MUST | per-scheme allowlists; never upstream type |
| SVG | MUST | never deliver raw `image/svg+xml`; rasterise to PNG/WebP in an isolated, network-less context |
| Blossom / hashtree verification | MUST | mismatch = `decode-failed` |
| Size cap | SHOULD | 10 MiB → `too-large` |
| Timeout | SHOULD | 30 s per URL → `timeout` |
| Concurrency / rate | SHOULD | 10 in flight, 60 req/min per napplet; bulk counts per URL |
| Bulk URL cap | SHOULD | 100 → top-level `too-large` |
| Redirects | SHOULD | ≤ 5 hops, private-IP recheck per hop |
| Blob quota | SHOULD | 50 MiB outstanding per napplet → `quota-exceeded` |
| Single-flight | SHOULD | concurrent same-URL MAY share one fetch |
| SVG caps | SHOULD | 5 MiB input, 4096×4096 output, 2 s raster |

Error codes: `invalid-request` (top-level for malformed payload or empty `urls`; per item for a bad
URL), `not-found`, `blocked-by-policy`, `timeout`, `too-large`, `unsupported-scheme`,
`decode-failed`, `network-error`, `quota-exceeded`.

Sidecar: NAP-RESOURCE defines only the `ResourceSidecarEntry` type; carriers (RELAY, OUTBOX)
declare their own wire dependency. Sidecars MUST be hydrated before the event handler runs and SVG
already rasterised. IDENTITY picture/banner and MEDIA artwork are fetched through `resource`.

Open issues (automated review): direct-network denial as projection prerequisite; SSRF global
address validation; bytes/Blob mapping; terminal envelopes scoped to cancellable ops; shim-side
decoding policy; htree grammar; `opts?` in API table has no wire field.

### 15.9 NAP-OUTBOX (`outbox`; depends: `relay` wire required, `resource` wire optional)

| Operation | Wire |
|---|---|
| `getEvent(eventId, options?)` → `OutboxEventResult` | `outbox.getEvent` {id, eventId, options?} / `.result` {id, result?, incomplete?, error?} |
| `query(filters, options?)` → `OutboxResult` | `outbox.query` {id, filters, options?} / `.result` {id, events, incomplete?, error?} |
| `subscribe(filters, options?)` → `OutboxSubscription` | `outbox.subscribe` {id, subId, filters, options?}; pushes `outbox.event` {subId, result}, `outbox.closed` {subId, reason?}; `outbox.close` {id, subId} |
| `publish(template, options?)` → `OutboxPublishResult` | `outbox.publish` {id, event, options?} / `.result` {id, ok, event?, eventId?, relays?, error?} |
| `resolveRelays(target)` → `OutboxRelayPlan` (diagnostic) | `outbox.resolveRelays` {id, target} / `.result` {id, plan, error?} |

There is no `outbox.eose`; relay EOSE stays internal.

Schemas: `OutboxEventOptions{author?, relays?, timeoutMs?}`; `OutboxQueryOptions{authors?, relays?, limit?, timeoutMs?}`;
`OutboxSubscribeOptions{authors?, relays?, limit? (backfill), timeoutMs?}`;
`OutboxPublishOptions{relays? (candidates, validated), toOutbox? (default true), toInboxes? (pubkeys whose NIP-65 read relays are required targets)}`;
`OutboxTarget{authors?, pubkey?, direction? "read"|"write"}`;
`OutboxRelayPlan{relays R, source R "nip65"|"cache"|"policy"|"fallback", missingAuthors?}`;
`OutboxEventResult{result?, incomplete?, error?}`; `OutboxResult{events R, incomplete?, error?}`;
`OutboxSubscription{on("event"), on("closed"), close()}`;
`OutboxPublishResult{ok R, event?, eventId?, relays? (url→bool), error?}`.

Errors: `"not found"`, `"no authors"`, `"relay list unavailable"`, `"relay timeout"`,
`"policy denied"`, `"publish denied"`, `"invalid filter"`.

Shell MUST: resolve plans per NIP-65 when available; verify `getEvent` results match the id;
deduplicate by event id; validate signatures before delivery; sign templates; publish at most one
signed event per request; include the user's NIP-65 write relays unless `toOutbox: false`; resolve
read relays for every `toInboxes` author and include each allowed relay or report failure;
deduplicate relay URLs; reply with matching `id`/`subId`; deliver `outbox.event` until close.
SHOULD merge observed relays into `sidecar.relayHints`, cache relay lists, fall back to configured
relays when NIP-65 is unavailable (never substituting for a `toInboxes` read relay), return
`incomplete: true` for partial results. MAY use NIP-66, attach sidecar resources (default-off),
enforce ACLs.

Security: `options.relays` MUST be validated and never bypass ACLs or reach private hosts; bound
broad queries and author sets; id lookups without author SHOULD be limited; publishing SHOULD show
consent or require prior approval; relay plans MAY be redacted.

### 15.10 NAP-UPLOAD (`upload`; depends: `relay` capability optional)

| Operation | Wire |
|---|---|
| `info()` → `UploadInfo` (advisory) | `upload.info` {id} / `.result` {id, info, error?} |
| `upload(request)` → `UploadResult` | `upload.upload` {id, request} / `.result` {id, result, error?} |
| `status(uploadId)` → `UploadStatus` | `upload.status` {id, uploadId} / `.result` {id, status, error?} |
| `onStatus(handler)` | push `upload.status.changed` {status} |

Schemas: `UploadRail` = `"nip96" | "blossom" | string`; `UploadState` = `pending | uploading |
complete | failed | cancelled`; `UploadRailInfo{rail R, enabled R, returns?}`;
`UploadInfo{rails R, maxBytes?, mimeTypes?}`;
`UploadRequest{rail?, data R (Blob/ArrayBuffer on web), mimeType?, filename?, caption?, noTransform?, metadata?}`;
`UploadResult{ok R, uploadId R, status R, rail R, url?, fallbackUrls?, sha256? (NIP-94 x), originalSha256? (ox), size?, mimeType?, dimensions? {width, height}, blurhash?, nip94? [tag], error?}`;
`UploadStatus` = `UploadResult` + `bytesSent?`, `bytesTotal?`, `updatedAt R`.

Errors: `"unsupported rail"`, `"policy denied"`, `"no server configured"`, `"file too large"`,
`"unsupported media type"`, `"user cancelled"`, `"server rejected"`, `"upload failed"`,
`"quota exceeded"`.

Shell MUST: keep `info` advisory (napplet MAY skip it); select a rail by policy when omitted
(SHOULD honour a supplied rail or fail with `unsupported rail`/`policy denied`); build and sign
authorisation (NIP-98 for NIP-96, kind 24242 for Blossom) without exposing keys; choose servers
(never napplet input); enforce per-napplet rail, size and MIME policy; reply with same `id`; report
`sha256` and `originalSha256` when transformed; report success only for bytes the server
confirmed. SHOULD push progress, get consent before a napplet's first upload, return `ok: false`
results for created-then-failed uploads and a top-level `error` when nothing was created. MAY
mirror to `fallbackUrls`, strip EXIF (reflected in hashes).

Security: uploads are egress and identity-linking; consent UI SHOULD show type, size, server,
napplet and preview; uploads are public and durable unless the rail encrypts; rate-limit.

Open issue: wire table marks `info`/`result`/`status` required while error paths omit them.

### 15.11 NAP-KEYS (`keys`; no deps)

| Operation | Wire |
|---|---|
| `registerAction(action)` → `RegisterResult` | `keys.registerAction` {id, action} / `.result` {id, actionId, binding?, error?} |
| `unregisterAction(actionId)` | `keys.unregisterAction` {actionId} (fire-and-forget) |
| `forward(event)` (shim-internal) | `keys.forward` {key, code, ctrl, alt, shift, meta} (no id) |
| `onAction(actionId, cb)` | local; driven by `keys.action` {actionId} |
| (push) | `keys.bindings` {bindings: [{actionId, key}]} — complete list on every change |

Schemas: `Action{id R (e.g. "editor.save"), label R, defaultKey?}` (hint only);
`RegisterResult{actionId R, binding?}`. Errors: `"duplicate action ID"`, `"invalid action"`.

Combo format: `Modifier+Key`, modifiers `Ctrl`, `Alt`, `Shift`, `Meta`, key = `KeyboardEvent.key`
(`Ctrl+S`, `Alt+Shift+P`, `F5`, `Escape`). Shells MUST normalise to the order
`Alt+Ctrl+Shift+Meta+Key`; napplets SHOULD use it.

Shim smart-forwarding: (1) skip text inputs, textareas, contenteditable; (2) skip bare modifiers;
(3) skip while `isComposing`; (4) normalise; (5) if in suppress list, `preventDefault()`, run the
local handler, do not forward; (6) otherwise send `keys.forward`.

Reserved keys (Tab, Shift+Tab, Escape, browser shortcuts like Ctrl+W/T/L) MUST never be suppressed
or bound; napplets MUST NOT hint them.

Shell MUST process `keys.forward` as shell input, reply to registrations with same `id`, push
`keys.bindings` on every change, ignore forwards from unmapped sources, and MUST NOT rely on napplet
suppression for security-critical bindings. SHOULD NOT forward keys to other napplets; SHOULD show
labels in shell UI. MAY bind immediately or leave unbound, send `keys.action` without focus, ACL,
cap actions. Napplets SHOULD validate incoming `actionId`.

Security: forwarding excludes text inputs to avoid credential leakage; a compromised napplet can
ignore suppression.

Open issues: "alphabetical" order is not alphabetical; case and exact-match rule for key segment;
action-id scope and lifetime; `error` missing from schema; reply to reserved `defaultKey`;
`actionId` echo on failure. Rename to KEYBOARD/KEYSTROKE discussed.

### 15.12 NAP-MEDIA (`media`; depends: `resource` optional for artwork)

Ownership: `owner: "shell"` = shell fetches, plays, owns the element and emits state;
`owner: "napplet"` = napplet plays in its frame and registers the session for metadata, media
keys, focus and commands.

| Operation | Wire |
|---|---|
| `createSession(options)` → `MediaSessionResult` | `media.session.create` / `.result` {id, sessionId?, owner?, error?} |
| `updateSession(sessionId, metadata)` | `media.session.update` {sessionId, metadata} |
| `destroySession(sessionId)` | `media.session.destroy` {sessionId} (ends with reason `destroyed`) |
| `reportState` / `onState` | `media.state` {sessionId, status, position?, duration?, volume?, reason?} (owner → peer) |
| `reportCapabilities` / `onCapabilities` | `media.capabilities` {sessionId, actions} (owner → peer) |
| `command` / `onCommand` | `media.command` {sessionId, action, value?, reason?} (controller → owner) |
| `onControls` | `media.controls` {sessionId, controls} (shell → napplet) |
| `onEnded` | `media.session.ended` {sessionId, reason} (shell → napplet) |

Napplet-owned: state/capabilities napplet→shell, commands shell→napplet. Shell-owned: the reverse.

Schemas: `MediaAction` = `play | pause | stop | next | prev | seek | volume`;
`MediaSessionCreate{owner R, sessionId? (hint), source? (required for shell-owned), metadata?, context?, capabilities?, autoplay?, live?}`;
`MediaSourceRef{url?, blossomHash?, nostr? {eventId?, address?, relays?}, mimeType?}`;
`MediaMetadata{title?, artist?, album?, artwork? {url?, hash?}, duration?, mediaType? audio|video}`;
`MediaSessionContext{label?, detail?, index?, total?, links? [{rel R lower-case, title?, nostr?}]}`;
`MediaState{status R playing|paused|stopped|buffering, position?, duration?, volume? 0–1, reason?}`;
`MediaCommand{action R, value? (seek seconds or volume 0–1), reason?}`.

Reasons: `user`, `ended`, `error`, `preempted`, `focus-lost`, `focus-gained`, `destroyed`,
`backend-exited`, `policy` (unknown = unspecified; reasons never grant authority).

Errors: `"session limit exceeded"`, `"invalid session ID"`; shell-owned: `"missing source"`,
`"unsupported source"`, `"source blocked"`, `"autoplay denied"`. Unknown session ids MUST be
silently ignored by both sides.

Key rules:
- The shell MUST return a canonical `sessionId`; later messages MUST use it.
- **Retirement** only via `media.session.ended`: on permanent reallocation (`preempted`) or backend
  exit; remove from dispatch and stop output first; exactly one `ended` per session, after any
  queued messages and after the successful create result; no messages after; retired ids MUST NOT
  be reused; messages to retired sessions (including `play`) are ignored and cannot reacquire
  output; late `onEnded` handlers receive the record once; a napplet-owned player MUST stop and
  release on retirement.
- **Focus loss** keeps the session: shell-owned reports `paused` + `focus-lost`; napplet-owned
  receives a pause command with `focus-lost`. Napplets MUST NOT auto-resume on focus alone; only a
  shell `play` with `focus-gained`, if previously playing and not superseded. Focus never revives
  a retired session.
- Natural end = `stopped` + `ended` (session survives) unless the shell retires it with `ended`.
- For napplet-owned sessions `source` is advisory and the shell MUST NOT fetch or play it.
- Context grants no fetch authority and MUST NOT change ownership.
- Shell MUST reject create without `owner`; enforce source, autoplay, audio focus and volume for
  shell-owned playback; run consent checks on every create; never expose raw source bytes; clean
  up on endpoint removal; destroy napplet-owned sessions when the window closes (SHOULD stop
  shell-owned ones unless promoted, and promoted sessions MUST be detachable and stoppable).
  MUST NOT change owner on command. Artwork MUST be fetched through NAP-RESOURCE.
- MAY limit sessions, duck/mute, enforce single output, ignore seek on live, cap volume.

Open issues: out-of-band source binding undefined; initial state/autoplay default after create;
no way to clear metadata fields.

### 15.13 NAP-NOTIFY (`notify`; no deps)

| Operation | Wire |
|---|---|
| `send(notification)` → `NotificationResult` | `notify.send` {id, title, body?, icon?, actions?, channel?, priority?} / `.result` {id, notificationId?, error?} |
| `dismiss(notificationId)` | `notify.dismiss` {notificationId} |
| `badge(count)` | `notify.badge` {count} (0 clears) |
| `registerChannel(channel)` | `notify.channel.register` {channelId, label, description?, defaultPriority?} |
| `requestPermission(channel?)` → `{granted}` | `notify.permission.request` {id, channel?} / `notify.permission.result` {id, granted} |
| `onAction` / `onClicked` / `onDismissed` / `onControls` | pushes `notify.action` {notificationId, actionId}, `notify.clicked` {notificationId}, `notify.dismissed` {notificationId, reason? user|timeout|replaced}, `notify.controls` {controls} |

Schemas: `NotificationPayload{title R, body?, icon?, actions? (≤3 of {id R, label R}), channel?, priority?}`;
`NotificationPriority` = `low` (silent) | `normal` | `high` (prominent) | `urgent` (may bypass DND);
`NotifyControl` = `toasts | badges | actions | channels | system`.

Errors: `"permission denied"`, `"rate limited"`, `"invalid channel"` (then nothing created).
`granted: false` is not an error. Unknown ids MUST be ignored.

Shell MUST reply with same `id`; track notifications per napplet and remove them with the iframe;
not block other messages while prompting. SHOULD render with its own UI, respect priority,
sanitise text, validate icons, attribute to the napplet, rate-limit urgent. MAY delegate to the
browser Notification API, require consent for urgent, cap badges, show fewer actions. Napplets do
not render notifications themselves.

### 15.14 NAP-CONFIG (`config`; depends: `storage` layering optional)

| Operation | Wire |
|---|---|
| `registerSchema(schema, version?)` | `config.registerSchema` {id, schema, version?} / `.result` {id, ok, error?, code?} |
| `get()` → `ConfigValues` | `config.get` {id} / `config.values` {id, values} |
| `subscribe(cb)` | `config.subscribe` {} then `config.values` {values} pushes; `config.unsubscribe` {} on last detach |
| `onSchemaError(handler)` | `config.schemaError` {error, code} |
| `openSettings({section?})` | `config.openSettings` {section?} |
| `schema` | local: last accepted schema or null |

Napplets MUST register a schema before requesting values. The shell is the **sole writer**; there
is no `config.set`.

Schema Core Subset (JSON Schema draft-07+): root `{type: object, properties}`; types string,
number, integer, boolean, homogeneous primitive arrays, nested objects (max depth 4); keywords
`type`, `properties`, `required`, `items`, `additionalProperties` (defaults to **false** at top
level), `default`, `title`, `description`, `enum`, `enumDescriptions`, `minimum`, `maximum`,
`minLength`, `maxLength`, `minItems`, `maxItems`. `format` is a hint and MUST NOT cause rejection.
Excluded: `pattern`, all `$ref`, `definitions`/`$defs`, `oneOf/anyOf/allOf/not`, `if/then/else`,
`patternProperties`, `propertyNames`, `dependencies`, `dependentSchemas`, `unevaluatedProperties`,
tuples, expression defaults.

Annotations (shell MAY act): `x-napplet-secret` (mask, no default, keychain/encrypted store),
`x-napplet-section`, `x-napplet-order`, `deprecationMessage`, `markdownDescription` (never HTML),
top-level `$version` (migration signal).

Default resolution: persisted valid value → property `default` → ancestor default object → undefined.

Error codes: `invalid-schema`, `unsupported-draft`, `ref-not-allowed`, `pattern-not-allowed`,
`secret-with-default`, `schema-too-deep`, `version-conflict` (registerSchema result and
schemaError); `no-schema` (get/subscribe before a schema). Undeclared `openSettings` sections are
ignored with no wire error.

Identity scope as NAP-STORAGE; no cross-napplet reads.

Shell MUST validate before delivery, apply defaults, key values on verified identity, never deliver
an unset secret, reject depth > 4 and forbidden features, wait for the latest schema before the
first `config.values`, deliver an immediate snapshot on subscribe, drop orphaned properties
(secrets immediately). SHOULD group/sort/render annotations, debounce edits (~100 ms), honour
`openSettings` only for a focused napplet, keep secrets out of logs. Anti-features (MUST NOT
appear): napplet writes, napplet-rendered settings, napplet validation code, `ui:widget`,
cross-napplet sharing, two-way binding, keychain as a MUST.

Security: `config.values` is cleartext over postMessage, secrets included.

Open issues: no policy-denial path for `get`; API says `registerSchema` returns none but wire
ACKs; `message` vs `error` naming.

### 15.15 NAP-LINK (`link`; no deps)

`open(url, options?)` → `LinkOpenResult`; wire `link.open` {id, url, options? {label?}} /
`link.open.result` {id, status `"opened"|"denied"`, error?}. Errors: `"invalid-url"`,
`"unsupported-scheme"`, `"blocked-by-policy"`, `"user-denied"`.

URL MUST be absolute. Shell MUST validate, reject relative URLs and `javascript:`, `data:`,
`blob:`, `file:` and other local or code-bearing schemes, reply with same `id`, never expose
`window.opener`, never treat `label` as proof. Grants no network access and returns no bytes.
SHOULD open outside the sandbox with `noopener`, require a gesture or prompt, show napplet identity
and destination, rate-limit, treat IDN/punycode/lookalikes as phishing risks. MAY persist choices
(allow once, allow napplet, allow hostname, deny once, deny napplet) and support `nostr:`/`mailto:`.
The shell chooses the target (tab, external browser, in-shell browser, native handler).

### 15.16 NAP-VALUE (`value`; depends: `relay` layering optional)

| Operation | Wire |
|---|---|
| `quote(request)` → `ValueQuote` (advisory; revalidated at send) | `value.quote` {id, request} / `.result` {id, quote, error?} |
| `send(request)` → `ValueResult` | `value.send` {id, request} / `.result` {id, result, error?} |
| `status(transferId)` → `ValueStatus` | `value.status` {id, transferId} / `.result` {id, status, error?} |
| `onStatus(handler)` | push `value.status.changed` {status} |

Schemas: `ValueRequest{rail R, amountMsat R, comment?, target R, metadata?}`;
targets `ZapTarget{type "zap", pubkey?, eventId?, address?, relays?}`, `LnurlTarget{type "lnurl", lnurl R}`,
`ValueExtensionTarget{type R, ...}`; `ValueQuote{ok R, amountMsat R, rail R, feesMsat?, expiresAt?, error?}`;
`ValueResult{ok R, transferId R, status R, rail R, amountMsat R, event?, preimage? (only when safe), error?}`;
`ValueStatus` = `ValueResult` + `updatedAt R`. `ValueRail` = `zap | lnurl | string`;
`ValueTransferState` = `pending | settled | failed | cancelled`. Other rails MUST state their unit
in `metadata.unit`.

Errors: `"unsupported rail"`, `"invalid target"`, `"amount out of policy"`, `"user cancelled"`,
`"wallet unavailable"`, `"invoice expired"`, `"payment failed"`.

Shell MUST require explicit user consent before spending unless a configured allowance covers it;
enforce per-napplet rail, amount and allowance policy; build and sign rail events (kind 9734 zap
request); never sign or pay opaque requests it cannot present; keep wallet credentials, NWC
strings, LNURL secrets, preimages and keys out of the sandbox; reply with same `id`; never report
failure as success (`settled` needs backend confirmation). Consent UI SHOULD show amount, target,
rail, recipient, comment and napplet. Allowances SHOULD bind napplet, rail, max amount, window and
target. MAY use NWC, LNURL-pay or an internal wallet.

### 15.17 NAP-CVM (`cvm`; depends: `value` layering optional)

ContextVM (MCP over Nostr) bridge, MCP 2025-11-25, CEP-8/15/16/17/35.

| Operation | Wire |
|---|---|
| `discover(query?)` → `CvmServer[]` | `cvm.discover` {id, query?} / `.result` {id, servers?, error?} |
| `request(server, message, options?)` → MCP message or null | `cvm.request` {id, server, message, options?} / `.result` {id, message?, error?} |
| `listTools`, `callTool(server, name, args?)`, `listResources`, `readResource(server, uri)` | wrappers over `request` |
| `close(server)` | `cvm.close` {id, server} / `.result` {id, error?} |
| `onEvent(handler)` | push `cvm.event` {server, message} |
| `registry.list(query?)`, `registry.has(selector)`, `registry.describe(selector)`, `registry.call(selector, tool, args?, options?)` | `cvm.registry.*` {id, ...} / `.result` {id, entries?/has?/entry?/result?, error?} |

Key schemas: `CvmServerRef{pubkey R (64 hex), relays?}`; `CvmDiscoverQuery{search?, kinds?, relays?, limit?}`;
`CvmServer{pubkey R, relays?, name?, description?, capabilities? (MCP capability names), paymentRequired?}`;
`CvmRequestOptions{timeoutMs? (default 30000, 1–300000), initialize?, payment? deny|prompt|allow (default prompt)}`;
`CvmRegistrySelector{schemaHash?, family?}` (one required; hash authoritative);
`CvmRegistryEntry{family?, description?, schemaHashes R, selected?, providers?, tools R}`;
`CvmRegistryTool{name R, description?, inputSchema R, outputSchema?, schemaHash R (CEP-15)}`;
`McpMessage{jsonrpc "2.0", id?, method?, params?, result?, error?}`; `cache` = `default | reload | no-store`.

Errors: `"invalid message"`, `"invalid request"`, `"invalid timeout"`, `"timeout out of policy"`,
`"unsupported method"`, `"unsupported kind"`, `"server not found"`, `"relay timeout"`,
`"initialization failed"`, `"session closed"`, `"payment required"`, `"payment denied"`,
`"policy denied"`, `"family not found"`, `"schema mismatch"`, `"provider unavailable"`,
`"cache policy denied"`.

Rules (summary):
- Exactly one `.result` per recognised request; failures use top-level `error`; unimplemented ops
  return `unsupported method` (except `registry.has` → `false`); wrappers MUST surface remote MCP
  errors as failures.
- Preserve MCP message form; never add an id to a notification; correlation includes endpoint,
  server, session and direction so ids never collide across napplets.
- Sessions are per endpoint and server; `close` completes pending ops with `session closed` and
  never affects other napplets; `cvm.event` goes only to the owning endpoint.
- Shell picks the ContextVM client key (ephemeral per endpoint RECOMMENDED); it is not the user's
  identity.
- Timeouts: invalid → `invalid timeout`; above shell max → `timeout out of policy` (never silently
  clamp); deadline covers queue, init, consent and payment; late responses produce nothing.
- Payments: enforcement mandatory, processing optional; `deny` / `prompt` (per-invocation consent) /
  `allow` (only with a standing allowance); intercept `-32042` and `notifications/payment_required`;
  reserve budget atomically; never borrow another napplet's paid authorisation; never blindly retry
  uncertain execution.
- Registry: families are sets of CEP-15 hashes; verify hashes before exposing; `registry.call`
  matches the tool to the verified hash; failover only before dispatch and without a pin; cache
  keys include hash, args, server and policy scope.
- Shell signs, encrypts, routes and verifies ContextVM events outside the sandbox; never exposes
  sockets, keys, NWC secrets or relay credentials.

### 15.18 NAP-POW (`pow`; depends: `identity` layering required, `relay` and `outbox` capability optional)

| Operation | Wire |
|---|---|
| `mine(template, target, opts?)` → `PowJob` | `pow.mine` {id, jobId, template, target, options?} / `.result` {id, jobId, accepted, state, position?, error?} |
| `mineAndPublish(template, target, opts?)` → `PowJob` | `pow.mineAndPublish` (same) |
| pushes | `pow.state` {jobId, state, position?}, `pow.progress` {jobId, progress}, `pow.done` {jobId, result}, `pow.error` {jobId, error} |
| `queue()` | `pow.queue` {id} / `.result` {id, jobs} |
| `job(jobId)` | `pow.job` {id, jobId} / `.result` {id, progress, error?} |
| `hashrate()` | `pow.hashrate` {id} / `.result` {id, hashrate} |
| `cancel(jobId)` | `pow.cancel` {id, jobId} / `.result` {id, jobId, cancelled, error?} |
| `pause(jobId?)` / `resume(jobId?)` | `pow.pause` / `pow.resume` {id, jobId?} / `.result` {id, jobId?, error?} |
| `formatHashRate(hps)` | local helper |

The napplet generates `jobId`. Schemas: `EventTemplate{kind R, content R, tags?, created_at?}`;
`PowOptions{workers? (hint), priority?, timeoutMs? (mining time only), commitCreatedAt? (default true)}`;
`PowState` = `queued | mining | paused | done | cancelled | error`; `PowProgress{jobId, target,
state, bestPow, hashes, hashRate, workers[], elapsedMs, bestNonce?}`; `PowResult{jobId, ok, event,
pow, nonce, hashes, elapsedMs, published? {eventId, relays}, error?}`; `PowJobSummary{..., mode mine|mineAndPublish}`.

Errors: `"duplicate jobId"`, `"invalid target"`, `"invalid template"`, `"timeout"`, `"cancelled"`,
`"unknown jobId"`, `"queue full"`, `"publish denied"`, `"publish failed"`, `"policy denied"`.

Semantics: at mining start the shell stamps the user pubkey and `created_at`, replaces any nonce
tag with `["nonce", "<nonce>", "<target>"]` (NIP-13), and MUST NOT return a result below target.
`mine` returns an unsigned event; the shell MUST later sign it verbatim or reject it.
`mineAndPublish` uses outbox fanout with no napplet relays and the same publish consent. Shell MUST
accept or reject synchronously in `.result`, emit `pow.state` on every transition, key pushes to
`jobId`, treat `workers` as a hint, and cap target, concurrent jobs and workers. `priority` MUST NOT
let one napplet starve another. SHOULD throttle progress. Telemetry MAY be coarsened.

### 15.19 NAP-DISPLAY (`display`; no deps; EXPERIMENTAL)

`list()` → `DisplayDevice[]` via `display.list` {id} / `.result` {id, displays, error?};
`push(displayId, pixels)` → null via `display.push` {id, displayId, pixels} / `.result` {id, error?}.

`DisplayDevice{id R (opaque, stable, never reused), width R, height R, type R lcd|eink|led-matrix|other}`;
`Pixel{x R, y R, bytes R [r, g, b] 0–255 sRGB}`. Batches MUST be non-empty with unique coordinates;
top-left origin. Errors: `"not-found"`, `"unavailable"`, `"denied"`, `"invalid-pixel"`,
`"too-large"`; a failed push applies nothing.

Runtime MUST discover devices (napplets cannot alter descriptors), map logical RGB to hardware,
process batches in order per display, validate the whole batch first, mediate per-napplet access.
MAY rotate, dither, quantise, coalesce, rate-limit. SHOULD require explicit permission and bound
batch size. Success means accepted, not refreshed.

### 15.20 NAP-CLASS (`class`; DEFERRED) and sub-tracks

Read-only `window.napplet.class` → `{class?: uint}`, set once by `class.assigned` {id, class}
(no response). The shell MUST send it after shim bootstrap and before any other envelope, at most
once per lifecycle; re-classification requires a new frame; it MUST NOT carry configuration.
Napplets MUST NOT infer class from the environment and MUST assume the most restrictive defaults
when `shell.supports('nap:class')` is false. Class numbers ascend and are never reused.

- **NAP-CLASS-1 (Strict Baseline)**: CSP `connect-src 'none'`; no prompt, no grants; shell MUST
  deliver `{class: 1}` explicitly.
- **NAP-CLASS-2 (User-Approved Explicit-Origin)**: CSP `connect-src <exact approved origins>` (no
  add, remove or normalise; empty set → `'none'`). Shell MUST prompt at first load per
  `(dTag, aggregateHash)` listing origins verbatim; key grants on that exact composite (keying on
  `dTag` alone is a security bug); send `{class: 2}` if approved, `{class: 1}` if denied (a denied
  napplet MUST be indistinguishable from class 1); refuse to serve a class-2 napplet whose HTML has
  its own `<meta http-equiv="Content-Security-Policy">`; offer revocation (moves to DENIED,
  effective by next load). Cleartext origins MUST be marked in prompts.

### 15.21 NAP-CONNECT (`connect`; DEFERRED)

User-gated direct network access. **No wire messages.** Manifest declares `["connect", "<origin>"]`
per origin. Origins: scheme in `https`, `wss`, `http`, `ws`; lowercase; Punycode hosts; no
wildcards; default ports omitted; no path, query, fragment or trailing slash. Example vectors:
`HTTPS://api.example.com` → `https://api.example.com`; `https://café.example.com` →
`https://xn--caf-dma.example.com`; `https://foo.com/`, `:443`, `*.`, paths, queries, `ftp:`,
`data:` rejected.

Origin fold: lowercase, sort ASCII, join with LF (no trailing), UTF-8, SHA-256, hex; pushed as a
synthetic `[<hex>, 'connect:origins']` x-tag into the aggregate hash; shells MUST recompute and
reject mismatches. Fixture: `https://api.example.com`, `https://xn--caf-dma.example.com`,
`wss://events.example.com` → `cc7c1b1903fb23ecb909d2427e1dccd7d398a5c63dd65160edb0bb8b231aa742`.

Runtime surface: `window.napplet.connect = {granted, origins[]}`, never undefined, default
`{granted: false, origins: []}`, read synchronously from injected
`<meta name="napplet-connect-granted" content="<origins>">` (shells MUST inject it, empty on denial),
SHOULD be frozen. Capability strings: `nap:connect`, `connect:scheme:http`, `connect:scheme:ws`.
Any `connect` tag → CLASS-2 consent flow; none → CLASS-1. The prompt MUST state that approval
allows sending and receiving any data with those origins and that the shell cannot see post-grant
traffic, and MUST NOT minimise ("just", "only", "simply"). A grant relaxes only `connect-src`; the
sandbox stays opaque. Weaker than NAP-RESOURCE (no sniffing, private-IP block, limits); authors
SHOULD prefer RESOURCE. Degradation: granted → direct fetch; denied → RESOURCE or degrade;
unsupported → RESOURCE; neither → explanatory UX. Napplets MUST NOT pressure users to switch shells.

Note: CLASS and CONNECT predate the current NIP-5D identity model (they reference NIP-5A
`aggregateHash` and `shell.supports('nap:…')`), which is one reason they are deferred.

## 16. Security considerations

Premise: napplets untrusted, shell trusted, browser enforces sandbox, `MessageEvent.source` gives
unforgeable sender identity.

1. **Sandbox**: `allow-scripts` only. Shells MUST NOT add `allow-same-origin`.
2. **Handoff**: `'*'` target origin is required for opaque-origin iframes; sender identified by
   `MessageEvent.source`, not `event.origin`.
3. **Identity binding**: `(dTag, artifactHash)` bound to the port held in the verified document's
   bootstrap closure, not to the reusable iframe `Window`. No platform mechanism enforces port
   privacy: a sandboxed document can transfer a reachable port cross-origin by transfer-list
   `postMessage`, so the mitigation holds only while bootstrap reachability conformance holds.
   A navigated or reloaded document has no channel, identity or grants; the shell tears it down.
4. **Content-addressed loading**: signature plus `sha256 == x` are mandatory; failure means
   rejection. Gateways are untrusted.
5. **Injection** is outside the signed artifact, limited to the `window.napplet` namespace, and
   MUST NOT change the bytes used for `artifactHash`.
6. **Silent ignore** of unknown types prevents capability probing.
7. **No crypto in sandbox**: napplets produce cleartext only; shells MUST NOT sign or broadcast
   events containing ciphertext received from a napplet; no `window.nostr`.

### 16.1 CSP advisory

An opaque origin does not stop fetch, WebSocket, Worker or subresource requests, and `srcdoc` has
no HTTP response for a CSP header. Shells SHOULD inject a CSP `<meta http-equiv="Content-Security-Policy">`
as the first element of `<head>`, before any napplet-controlled resource is parsed, only after
verifying the artifact bytes, and outside the bytes used for `artifactHash`. Baseline directives:

```
default-src 'none';
script-src 'unsafe-inline' 'wasm-unsafe-eval';
style-src 'unsafe-inline';
img-src data: blob:;
font-src data:;
connect-src 'none';
worker-src 'none';
child-src 'none';
frame-src 'none';
media-src 'none';
object-src 'none';
manifest-src 'none';
base-uri 'none';
form-action 'none'
```

- If host policy permits direct network access, `connect-src` MAY name only exact granted origins;
  wildcard or scheme-wide sources SHOULD NOT be used. This is outside the shell-mediated NAP model.
- `'wasm-unsafe-eval'` permits WebAssembly compilation only, not `eval()`/`Function()`. Shells MUST
  NOT substitute `'unsafe-eval'` for WebAssembly.
- Per CSP3, `report-uri`, `frame-ancestors` and `sandbox` are not enforced via `meta`. A shell that
  must restrict embedders MUST set `frame-ancestors` in its HTTP response.
- CSP is defence in depth, not a replacement for verification, sandbox or port binding.
- A `meta` CSP does not survive navigation and does not stop a document navigating its own frame,
  so a napplet can leak data by encoding it in a navigation URL. Revoking identity stops further
  access but cannot recall sent data. Shells SHOULD treat data released to a napplet as disclosable.
- Storage isolation, relay access control and ACL enforcement are defined by their NAPs.

**Non-guarantees**: no protection against a compromised browser, a malicious shell, side channels
or social engineering.

### 16.2 Known open issues

- Opaque origin breaks ES module CORS, WebSocket `Origin: null` (some relays reject it) and
  `localStorage`. A per-napplet `allow-same-origin` origin was proposed in review and not adopted.
  Multi-file napplets break under srcdoc (Amethyst #3887), so the Vite plugin defaults to
  single-file output.
- No diagnostics spec (e.g. CSP-violation reporting) yet.
- Domain naming churn between SDK docs and the NAP registry.
- Native and WASM projections are only "possible".

## 17. Tooling

| Package | Role |
|---|---|
| `@napplet/core` | Envelope types (`NappletMessage`, `NapDomain`), `registerNap`, `dispatch`, constants |
| `@napplet/shim` | Injects `window.napplet.<domain>` before napplet code runs |
| `@napplet/sdk` | Named TS exports over `window.napplet` |
| `@napplet/nap` | Per-domain subpath exports, tree-shakable |
| `@napplet/vite-plugin` | Hashes final `index.html`, signs kind 35129 manifest, single-file default |
| `@napplet/cli` | `napplet` CLI: create, init, deploy, Paja preview |
| `@napplet/boilerplate` | Generator behind `napplet create` |
| `@napplet/conformance` (+ `-cli`, `-web`) | Mock shell, per-NAP and manifest validators, headless runner |
| `@kehto/acl`, `firewall`, `rate-limit` | Grants, scoped approval, budgets |
| `@kehto/runtime`, `shell`, `services` | Kernel, browser adapter, reference services |
| `@kehto/nip`, `wm`, `mocks`, `conformance` | NIP helpers, window management, mocks, suite |
| `@kehto/paja` | Reference developer runtime (kehto.github.io/web/paja/) |

```bash
napplet create my-napplet && cd my-napplet
napplet init                 # writes .napplet/config.yaml
pnpm install && pnpm verify
napplet deploy --dry-run
napplet deploy               # Blossom + relays; Zapstore event by default
npx napplet-conformance ./dist
```

Conformance v1 checks: signed manifest validity, boots under `sandbox="allow-scripts"`, receives
injected `window.napplet`, well-formed envelopes, graceful degradation when a domain is absent,
no forbidden globals.

## 18. Sources

- NIP-5D PR: https://github.com/nostr-protocol/nips/pull/2303
- NIP-5D text: https://raw.githubusercontent.com/dskvr/nips/nip/5d/5D.md
- NAP registry: https://github.com/napplet/naps (branch `master`, files under `naps/`)
- Web projection: https://github.com/napplet/naps/blob/master/projections/web.md
- SDK: https://github.com/napplet/web
- Kehto: https://github.com/kehto/web
- Site: https://napplet.run/ , https://napplet.run/explainer/ , https://napplet.run/docs/packages/
- Amethyst issue: https://github.com/vitorpamplona/amethyst/issues/3887
