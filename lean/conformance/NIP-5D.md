# NIP-5D conformance

Upstream: `nostr-protocol/nips` PR #2303, `5D.md` at `f60550c3409d6d81a875088ec83e660571e10504`.
Lean: `Napplet/Shell.lean` (transport and identity state machine), `Napplet/Manifest.lean`
(verification and metadata), `Napplet/Capability.lean` (exposure, `R`/`N` checks),
`Napplet/Runtime.lean` (composition), `Napplet/Binding.lean` (bootstrap),
`Napplet/Host.lean` (host contract).

Status `N/A` marks statements that bind NAP spec authors rather than a shell, napplet or host.

Note: `lean/README.md` in the working tree has lost the text between its lines 23 and 24
(the upstream commit list, the "Modelling decisions" heading and decisions 1 and 2). The
`DECISION` rows below that cite decisions 1 and 2 refer to their earlier wording: (1) a `hello`
with zero or several ports before handoff is dropped; (2) window messages other than `hello`
before handoff are ignored.

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | "Napplets SHOULD be single-purpose rather than monolithic" | SHOULD | NAPPLET | Not modelled (design guidance) |
| 2 | Bootstrap "MUST, before any napplet script runs, create a `MessageChannel`, retain one port privately ... and transfer the other port to the shell exactly once" | MUST | NAPPLET | `Binding.lean:118` `boot`; theorems `boot_once` (121), `window_only_hello` (262); retained-port unreachability is a stated assumption (`Shell.lean:19`) |
| 3 | Retained port "MUST NOT be reachable from napplet code" | MUST | NAPPLET | Assumption `Shell.lean:19`; host injects the bootstrap `Host.lean:57-60` |
| 4 | "All NAP messages in both directions MUST be carried over the port" | MUST | OK | `Runtime.lean:157` `Output.send` (port only); `Runtime.lean:426` messages only via `Input.message p`; `Binding.lean:144` `request` |
| 5 | "Shells MUST NOT send NAP messages via `iframeWindow.postMessage` and MUST NOT transfer a port into the iframe" | MUST NOT | OK | No output posts to a window or transfers a port (`Runtime.lean:157-170`); `Host.lean:63-68` |
| 6 | "Shells SHOULD verify the bootstrap ... in CI, with a reachable-port scan" | SHOULD | OPTIONAL (not listed) | Not modelled; README does not list it among optional behaviours |
| 7 | "MUST use this sandbox attribute: `sandbox=\"allow-scripts\"`" | MUST | HOST | `Host.lean:57`; `Runtime.lean:161` `iframeCreated` docstring |
| 8 | "The `allow-same-origin` token MUST NOT be present" (also Security 1) | MUST NOT | HOST | `Host.lean:57` (`sandbox="allow-scripts"` only) |
| 9 | Accept `napplet.hello` only when source is a created iframe's `contentWindow` "and exactly one port is attached" | MUST (implied) | OK | `Shell.lean:131-145` (`[p]` only); zero/several ports dropped: DECISION 1 |
| 10 | "Messages from unknown sources ... MUST be silently dropped" | MUST | OK | `Shell.lean:145,149` (unknown window → `(s, [])`); `Host.lean:68` |
| 11 | "Shells MUST inject `window.napplet` before any napplet script runs" | MUST | HOST | `Host.lean:59-60` |
| 12 | "The namespace MUST contain only the NAP domain objects the shell exposes" | MUST | OK + HOST | `Shell.lean:116-124` `iframeCreated w id ex` with `ex = exposedFor`; theorem `create_exposure` (`Shell.lean:426`); `Host.lean:60` "exposing exactly `exposed`" |
| 13 | "Shells MUST NOT provide `window.nostr` (NIP-07)" (also Security 7) | MUST NOT | HOST | `Host.lean:79` (NIP-07/46 "host side only"); namespace holds only `window.napplet.<domain>` (`Host.lean:60`) |
| 14 | "Signing and encryption ... MUST be mediated by the shell" | MUST | OK | Signing/encryption only via `Call.sign`/`Call.encrypt` (`Host.lean:164-168`), issued by components |
| 15 | "Messages with an unrecognized `type` MUST be silently ignored" (also Security 6) | MUST | OK | `Wire.lean:25` `domain?`; `Component.lean:99` `Decoded.unknown`; `Runtime.lean:225` `lift`; theorem `message_unexposed_silent` (`Runtime.lean:460`) |
| 16 | Identity: runtime "MUST NOT accept it from a host" | MUST NOT | OK | `Manifest.lean:261` identity built from `c.sha256 bytes`; theorems `checkManifest_identity` (313), `dispatch_sender_verified` (`Shell.lean:662`), `ctx_verified` (`Runtime.lean:1240`) |
| 17 | Before the iframe: "Resolve the napplet manifest ... and verify its signature" | MUST | OK + HOST | `Manifest.lean:246` (`verifySig`); resolution `Host.lean:52-54`; `verifySig` contract `Host.lean:124-126` |
| 18 | "a manifest that does not carry exactly one `x` tag MUST be rejected" | MUST | OK | `Manifest.lean:225` `xValue?`; theorem `checkManifest_single_x` (327) |
| 19 | "Fetch the artifact ... and verify `sha256(blob)` equals the `x` value" | MUST | OK + HOST | `Manifest.lean:258`; theorem `checkManifest_rejects_mismatch` (333); fetch `Host.lean:54-56` |
| 20 | "Inject the verified bytes via `srcdoc` (never a navigated `src`)" | MUST | HOST | `Host.lean:57-58` |
| 21 | "Bind `(dTag, artifactHash)` to the port carried by the first valid `napplet.hello`" | MUST | OK | `Shell.lean:133-141`; output `bound` |
| 22 | "A gateway MAY serve the bytes ... the runtime MUST verify its output against the signed manifest" | MAY / MUST | OK | `checkManifest` applies to any bytes (`Manifest.lean:244`); `Host.lean:55-56` |
| 23 | "The shell MUST therefore accept at most one `napplet.hello` per iframe" | MUST | OK | `Shell.lean:144`; theorem `revoke_second_hello` (361) |
| 24 | Evidence of replacement: second hello / window message after handoff / second `load` / port close | MUST | OK | `Shell.lean:129,144,148,152`; theorems `revoke_second_hello` (361), `revoke_window_msg` (369), `revoke_second_load` (377), `revoke_port_closed` (673); window messages before handoff ignored: DECISION 2 |
| 25 | "the shell MUST close the port, revoke the identity binding and every grant and session ..., and remove the iframe" | MUST | OK | `Shell.lean:93` `revoke`; component state: `Runtime.lean:274` `dropAll`, theorems `port_closed_teardown`, `second_hello_teardown`, `teardown_clears` (`Runtime.lean:906`) |
| 26 | "`close()` MUST be explicit on every teardown path" | MUST | OK | `Shell.lean:98`; theorem `step_unbind` (727): a binding disappears only with `closePort`; host applies `MessagePort.close()` (`Host.lean:66-67`) |
| 27 | "The shell MAY then create a fresh iframe from the verified bytes" | MAY | OK | New window via `Input.create` (window ids never reused, decision 4) |
| 28 | "MUST NOT process NAP messages from any source other than the bound port" | MUST NOT | OK | `Shell.lean:154-160`; theorems `nap_dispatch_requires_binding` (236), `message_unbound_silent` (`Runtime.lean:451`) |
| 29 | "MUST NOT re-bind a napplet identity to an existing iframe" | MUST NOT | OK | `Shell.lean:117-118` (create on known window no-op); theorems `removed_stays_removed` (259), `no_rebind_removed` (313); decision 4 |
| 30 | Manifest "MUST carry exactly one `x` tag holding the lowercase-hex sha256" | MUST | OK | `Manifest.lean:225,258` (equality with host `sha256`, lowercase hex per `Host.lean:124`) |
| 31 | "`server` tags SHOULD hint the Blossom servers" | SHOULD | NAPPLET | Publisher guidance; read as `Metadata.servers` (`Manifest.lean:196`) |
| 32 | "The event `content` MUST contain a non-empty ... description" | MUST | OK | `Manifest.lean:256` (`emptyContent`) |
| 33 | "Clients MUST treat it as plain text, not HTML or Markdown" | MUST | RESOLVED (was MISMATCH) (host doc) | `VerifiedManifest.content` (`Manifest.lean:220`) is passed on, but no host contract says to render it as plain text |
| 34 | `d`: "exactly 1 on `35129`, absent otherwise" | table | OK | `Manifest.lean:231` `dValue?`; theorem `checkManifest_dTag` (356) |
| 35 | `a`/`A`: "0-1 each, `5129` only" | table | OK | `Manifest.lean:207-208` (`uniqueTag`, snapshot only); see row 37 for non-snapshots |
| 36 | Snapshot "MAY record lineage with an `A` tag ... and an `a` tag" | MAY | OK | `Manifest.lean:207-208` |
| 37 | "Lineage tags ... MUST NOT affect verification ... a runtime MUST NOT resolve or trust a referenced napplet" | MUST NOT | RESOLVED (was MISMATCH) (minor) | Snapshots: lineage never affects verification and is never resolved. But `lineageOk` (`Manifest.lean:240`, used at 257) rejects a `15129`/`35129` manifest that carries any `a`/`A` tag (`lineageOnNonSnapshot`); no README decision covers that rejection |
| 38 | "A manifest MAY include one `source` tag" | MAY | OK | `Manifest.lean:186` |
| 39 | `source` "tag MUST have exactly two elements" | MUST | OK | `uniqueTag m "source" 1` (`Manifest.lean:180,186`) |
| 40 | `<location>` "MUST be an absolute URL using `http`, `https`, `ssh`, `git`, or `nostr`, or ... scp-like"; no `file` URLs | MUST | OK | `Manifest.lean:171` `sourceOk` |
| 41 | "A `nostr` location MUST identify a kind-30617 repository announcement" (NIP-34 clone URL) | MUST | RESOLVED (was MISMATCH) (minor) | `urlWithScheme` (`Manifest.lean:159`) accepts any non-empty `nostr:` rest; it does not decode the `naddr` or check kind 30617, so a malformed `nostr` source is kept instead of ignored (row 46) |
| 42 | "A manifest MUST NOT contain more than one `source` tag" | MUST NOT | OK | Repeated tag → ignored (`uniqueTag`, `Manifest.lean:180`) |
| 43 | `source-commit` "MUST have exactly two elements, with a full lowercase-hex Git commit ID" | MUST | OK | `Manifest.lean:198-201` |
| 44 | "Clients resolving this version's repository source MUST use the pinned commit" / "A `source-commit` without a Git repository `source` MUST be ignored" | MUST | OK (partial) + RESOLVED (was MISMATCH) (host doc) | Ignored without a valid `source` (`Manifest.lean:198`; whether an `https` source is a Git repository is not decidable from the URL). Nothing in `Host.lean` tells a host that resolves sources to use the pinned commit |
| 45 | `source-archive` "MUST have exactly four elements" (https URL without credentials/fragment, 64-hex sha256, MIME) | MUST | OK | `Manifest.lean:175,202-206` |
| 46 | "Clients MUST verify the digest before using the archive"; "MUST ignore a source field if its tag is malformed or appears more than once"; "MUST NOT prevent playback" | MUST | OK (parse) + RESOLVED (was MISMATCH) (host doc) | Malformed/repeated ignored (`uniqueTag`); metadata never fails `checkManifest`. No host contract for verifying the archive digest before use |
| 47 | Presentation media: "Exactly one `x` field is REQUIRED" | REQUIRED | OK | `Manifest.lean:144-156` `parseMediaBlob` |
| 48 | "publishers SHOULD include `m` and `dim`" | SHOULD | NAPPLET | Publisher guidance |
| 49 | "Clients MUST ignore tags with missing, malformed or repeated `x` fields, and ignore unknown, malformed or repeated optional fields" | MUST | OK | `Manifest.lean:139` `oneField`, 146-156 |
| 50 | "Before rendering those bytes, clients MUST verify SHA-256 and decode ... When a valid `m` field is present, clients MUST also verify that it matches" | MUST | HOST | `Host.lean:69-74` |
| 51 | "Clients SHOULD preserve screenshot tag order and MAY display a subset" | SHOULD / MAY | OK | `Manifest.lean:192` (`filterMap` keeps order) |
| 52 | "Extra or unusable entries MUST NOT suppress other usable screenshots or prevent napplet discovery or playback" | MUST NOT | OK | `Manifest.lean:192` (per-tag), metadata outside `checkManifest` decisions |
| 53 | "If multiple `preview` tags are present, clients MUST ignore the preview" | MUST | OK | `Manifest.lean:193-195` |
| 54 | Icon: "The hash MUST be the 64-character lowercase-hex sha256 ... The MIME type MUST be `image/png`, `image/jpeg`, or `image/webp`" | MUST | OK | `Manifest.lean:82,188-191` |
| 55 | "Clients displaying the icon MUST fetch the blob by its hash from the ... `server` origins and verify ... MUST also verify that the bytes decode ... MUST render the verified bytes" | MUST | HOST | `Host.lean:69-74` |
| 56 | Bad icon "MUST fall back to generic artwork and MUST NOT prevent loading the napplet" | MUST | OK + HOST | Icon outside `checkManifest` (`Manifest.lean:244-268`); fallback `Host.lean:73-74` |
| 57 | "`z` or `i` tag MUST NOT widen what the shell exposes" | MUST NOT | OK | `Capability.lean:38` `exposedFor` (policy only); theorem `exposure_ignores_declarations` (51) |
| 58 | `R` check: "if one is absent it SHOULD reject the napplet or warn" | SHOULD | OK | `Shell.lean:104-112` `admit`, `Capability.lean:30` `strictRequired` (default reject), `missingRequired` (58); unknown names count as missing (decision 5) |
| 59 | "Missing `O` domains MUST NOT by themselves prevent loading" | MUST NOT | OK | `admit` never reads `optional` (`Shell.lean:104-112`) |
| 60 | "`R` and `O` ... MUST NOT widen what the shell exposes" | MUST NOT | OK | `Capability.lean:38,51` |
| 61 | "Clients MUST inspect the complete `R` set locally; `&R` is only a targeted discovery optimization" | MUST | OK | `missingRequired` over all `R` (`Capability.lean:58`); theorems `andFilter_is_not_compatibility` (92), `andFilter_admits_incompatible` (100) |
| 62 | HTML metadata: "Publishing tools SHOULD preserve descriptive metadata"; "Icon links SHOULD use data URLs"; "Publishers MUST finalize embedded metadata before computing `x`" | SHOULD / MUST | NAPPLET | Publisher obligations; not modelled |
| 63 | "runtimes MUST NOT require this metadata or let it override the signed manifest or runtime domain availability" | MUST NOT | OK | The model never reads the artifact's HTML metadata (`checkManifest` reads only the event) |
| 64 | "If it is absent, the napplet MUST gracefully degrade or stop using that domain" | MUST | NAPPLET | Napplet behaviour; shell side: unexposed domains are dropped (`Shell.lean:158`) |
| 65 | "If a domain needs semantic compatibility checks ... that domain MUST define them in its own NAP" | MUST | N/A | Binds NAP authors |
| 66 | "A shell MAY advertise itself with a NIP-89 handler information event"; "the shell SHOULD provide at least one" `web` tag | MAY / SHOULD | OPTIONAL (not listed) | Handler publication is not modelled; only the `R ⊆ N` test is (`Capability.lean:78`). README does not list it |
| 67 | "Clients served by the `#N` fallback MUST still check the complete `R` set against the shell's `N` set locally" | MUST | OK | `Capability.lean:78` `compatible`, theorem `compatible_iff` (81) |
| 68 | "A handler event MUST NOT widen what a shell exposes, nor substitute for the load-time check of a manifest's `R` set" | MUST NOT | OK | `exposedFor`/`admit` never read `N` (`Capability.lean:38`, `Shell.lean:104`) |
| 69 | "a missing or malformed one MUST NOT prevent playback in a shell the user has already opened" | MUST NOT | OK | Handler events play no part in `Runtime.step` |
| 70 | NAP specs MUST define types, payloads, behaviour; "a shell MAY support any subset of NAPs" | MUST / MAY | N/A (MAY: OK) | Subsets: `ShellConfig.supported` (`Capability.lean:26`) |
| 71 | Security 1: "shells MUST NOT add `allow-same-origin`" | MUST NOT | HOST | `Host.lean:57` |
| 72 | Security 3: binding to the verified document's port; "the shell tears the frame down" on navigation/reload | (restates) | OK | Rows 21–26 |
| 73 | Security 4: "a napplet failing either check MUST be rejected" | MUST | OK | `Manifest.lean:246,258`; `Shell.lean:121` (`rejected`) |
| 74 | Security 5: "Runtime injection ... MUST be limited to the `window.napplet` namespace and MUST NOT change the napplet bytes used to compute `artifactHash`" | MUST | OK + HOST | Hash computed from the fetched bytes before injection (`Manifest.lean:258-261`); injection `Host.lean:57-60` |
| 75 | Security 7: "Shells MUST NOT sign or broadcast events containing ciphertext received from a napplet" | MUST NOT | OK | `Host.looksCiphertext` (`Host.lean:136-139`) used by RELAY/OUTBOX before `Call.sign` (decision 11) |
| 76 | Security 7: "MUST NOT provide `window.nostr` (NIP-07) or any signing/encryption primitives" | MUST NOT | OK + HOST | No component exposes a sign/encrypt operation to napplets; row 13 |
| 77 | CSP: "shells SHOULD inject a CSP `meta` element as the first element in `head`" | SHOULD | HOST | `Host.lean:58-59` |
| 78 | "The shell MUST inject the policy only after verifying the signed artifact bytes, and the injected policy MUST remain outside the bytes used to compute `artifactHash`" | MUST | OK + HOST | `iframeCreated` only after `admit` (`Shell.lean:120-124`); hash from raw bytes (`Manifest.lean:258`); `Host.lean:57-59` |
| 79 | "`connect-src` MAY name only the exact granted origins ... wildcard or scheme-wide sources SHOULD NOT be used" | MAY / SHOULD NOT | HOST | Baseline CSP (`connect-src 'none'`) per `Host.lean:58-59`; no direct-network policy modelled |
| 80 | "Shells MUST NOT substitute the broader `'unsafe-eval'`" | MUST NOT | HOST | `Host.lean:58-59` (the baseline policy, which has `'wasm-unsafe-eval'` only) |
| 81 | "A shell that needs to restrict its own embedders MUST set `frame-ancestors` on the shell's HTTP response" | MUST (conditional) | RESOLVED (was MISMATCH) (host doc) | Outside the iframe model; `Host.lean` does not mention it |
| 82 | "Shells SHOULD treat data released to a napplet as disclosable by that napplet" | SHOULD | OK | Design stance; nothing in the model assumes otherwise |
