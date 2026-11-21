# Napplet protocol: Lean 4 model

A machine-checked, executable model of a napplet shell: the NIP-5D core, all
nineteen live NAPs, the JSON wire codec, the composed runtime that ties them
together, the host interface, and the napplet-side bootstrap and binding.
818 theorems and 511 evaluated vectors (92 of them end to end through the
composed runtime). Section numbers refer to [`../NAPPLETS-SPEC.md`](../NAPPLETS-SPEC.md),
but the model was built from the upstream texts at the commits listed below.

- Lean `v4.36.0`, no Mathlib, no dependencies.
- No `sorry`. Proofs use only Lean's standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`). No `native_decide`.
- Every definition is computable, so the model runs as a test oracle
  (`Napplet/Test/Harness.lean`).
- Coverage against upstream: every one of the 177 type strings in the 19 NAP wire
  tables is decoded or produced by its component; all 91 JSON request examples in the
  NAP specs decode (`Napplet/Test/UpstreamExamples.lean`); `Napplet/Test/E2E.lean`
  feeds upstream example JSON for every NAP through `Runtime.step`.

```bash
cd lean && lake build
```

```bash
cd lean && lake env lean Audit.lean
```

`lake build` checks every proof and runs every vector. `Audit.lean` prints the axioms
behind the headline theorems; CI fails if anything other than the three standard
axioms appears, and fails on any `sorry`.

## Implementing from this model

A shell implementation is a faithful port of four things.

| What | Where | Notes |
|---|---|---|
| Entry point | `Napplet.Runtime.step` in [`Napplet/Runtime.lean`](Napplet/Runtime.lean) | `step : Host → Config → RtState → Input → RtState × List Output`. Start from `RtState.init cfg`. Inputs: browser events (`create`, `load`, `hello`, `windowMsg`, `portClosed`), `grant`, `message p json` (a JSON value posted on port `p`), `reply tag r`, `event e`, `tick now`. Outputs: `send p json`, browser actions (`iframeCreated`, `bound`, `closePort`, `removeFrame`, `rejected`), host `call tag c` and `effect e`. Generated from the component table by `scripts/gen_runtime.py`. |
| Host interface | [`Napplet/Host.lean`](Napplet/Host.lean) | Everything the host supplies, each with its contract: pure functions (`Host`: SHA-256, signature checks, MIME sniffing, SVG rasterisation, ciphertext detection), asynchronous calls and replies (signing, encryption, decryption, fetch, prompts, relay pool, NIP-65, NAP-specific operations), effects, events, the clock, persistence, and the list of external standards. |
| Shell configuration | `Runtime.Config` and each component's `Cfg` | Policy that is not a host call (exposure policy, quotas, rails, allowlists, limits). Defaults follow the upstream recommendations. |
| Per-NAP behaviour | `Napplet/Run/<Name>.lean` | One component per NAP: `decode` (wire JSON → typed request, with upstream type strings, fields, errors), `encodeReq` (proved inverse of `decode`), `handle`, `onReply`, `onEvent`, `drop` (teardown), and the encoders for every result and push. Each file starts with its upstream wire summary and ends with vectors built from the upstream examples. |
| Napplet side | [`Napplet/Binding.lean`](Napplet/Binding.lean), [`Napplet/BindingApi.lean`](Napplet/BindingApi.lean), [`Napplet/BindingUri.lean`](Napplet/BindingUri.lean), [`Napplet/Nip19.lean`](Napplet/Nip19.lean) | Bootstrap (`napplet.hello` once), the `window.napplet.<domain>` method surface and its mapping to wire requests, request ids and correlation, push buffering, sidecar hydration order, convention URI normalisation and `naddr` handler hints. |

Identity: `checkManifest` (`Napplet/Manifest.lean`) computes the bound `Identity`
from the signed manifest event and the artifact bytes: NIP-5D's `(dTag, artifactHash)`
plus the publisher, kind and event id. Every NAP gets its endpoint context from the
binding through one function, `Ctx.ofBinding` (`Napplet/Component.lean`), which gives
the manifest key (`Identity.key`) used by the STORAGE, RESOURCE and CONFIG scopes, the
INTENT catalog id (`Identity.catalogId`, kehto's encoding) and the INC endpoint id.

### What an implementer still needs from outside the model

Nothing beyond browser behaviour and the standards named in `Napplet/Host.lean`:

1. **Browser behaviour of the web projection** (NIP-5D, HTML standard, CSP Level 3):
   creating the `srcdoc` iframe with `sandbox="allow-scripts"`, injecting the CSP
   `meta`, the bootstrap and `window.napplet` before napplet scripts run,
   `MessageChannel` and transfer-list `postMessage` with target `'*'`, structured
   clone of messages, telling windows apart by `MessageEvent.source`, `load` events,
   `MessagePort.close()` and port errors, removing iframes, and opening links
   without an opener. `Napplet/Host.lean` §Global contracts says which runtime
   input or output each corresponds to.
2. **The external standards the host contracts name**, implemented by the host:
   NIP-01, -04, -07/-46, -13, -17/-59, -19/-21, -44, -47, -51, -57, -58, -65,
   -92/-94, -96, -98; Blossom BUD-01, -02, -10, -11; HTS-01; LUD-06/-16; ContextVM
   CEP-4/-6/-8/-15/-17/-35 and MCP 2025-11-25; BIP-340, BIP-173, FIPS 180-4,
   RFC 8259, RFC 4648, RFC 2397, WHATWG MIME Sniffing.

Everything else (wire formats, validation, error strings, policy decisions,
correlation, teardown, buffering, scopes, identity derivation, the JSON Schema core
subset for NAP-CONFIG, NIP-19 `naddr` decoding, base64, `data:` URLs, NIP-13
difficulty) is defined by the Lean definitions.

The host-side pieces are not open questions. Each is a contract in
`Napplet/Host.lean`, and fulfilling it takes only items 1 and 2:

| Host piece | Fulfilled by |
|---|---|
| Signer (`Call.sign`) | NIP-01 event id and BIP-340 signature with the user's key (local, NIP-07 or NIP-46). |
| Encryption (`Call.encrypt`, `Call.decrypt`, `Host.encryptedWith`, `Host.looksCiphertext`) | NIP-04, NIP-44; which incoming events are encrypted per NIP-17/NIP-59. |
| Relay pool (`Call.subscribe`, `Call.publish`, `Call.relayList`) | NIP-01 relay protocol, NIP-65 relay lists. |
| Fetch (`Call.fetch`) | HTTPS with DNS (browser `fetch` from the shell's own origin), BUD-10, NIP-19, HTS-01, RFC 2397; hop reporting and limits are stated in the contract. |
| Storage servers, wallet, miner, ContextVM | NIP-96/NIP-98, BUD-02/BUD-11; NIP-47, NIP-57, LUD-06/16; NIP-13; ContextVM CEPs with MCP 2025-11-25. The JSON each operation exchanges is defined in the model. |
| Prompts, settings panel, notifications, media player, displays, key input | Shell UI in the browser. The contract fixes what each shows, what reply it gives, and that it never blocks other inputs; how it looks is not protocol. |
| Persistence | Storing the runtime state across reloads with browser storage. Which fields persist is stated in the contract. |
| Clock | `Input.tick now` from the browser clock. |
| Hashing, sniffing, rasterising | FIPS 180-4, WHATWG MIME Sniffing, SVG rendering in an isolated browser context. |

The five items under "Not modelled yet" that upstream leaves undefined need nothing
either. The model's behaviour for each is fixed:
- MEDIA out-of-band source binding: there is no such binding. Shell-owned playback
  uses the `source` given at create.
- Gift-wrap depth: decided by `Host.encryptedWith` and `Call.decrypt` (NIP-17/59).
- Resource sidecar carriers: no sidecar resources are ever sent.
- Upload cancel: no wire message exists, so there is nothing to handle.
- Paged `relay.query`: not part of the wire.

### Upstream texts used

| Spec | Source | Commit |
|---|---|---|
| NIP-5D | `dskvr/nips` branch `nip/5d` (nostr-protocol/nips#2303) | `f60550c3409d6d81a875088ec83e660571e10504` |
| Web projection | `napplet/naps` `master` `projections/web.md` | `377bf939c6c906817084b43dd21d424de646dbc2` |
| NAP-SHELL, NAP-INTENT, NAP-INC, NAP-THEME, NAP-IDENTITY | `napplet/naps` `master` | `377bf939c6c906817084b43dd21d424de646dbc2` |
| NAP-RELAY | PR #2, `nub-relay` | `9f30b3505335a52c574ff570576687d6467021ff` |
| NAP-STORAGE | PR #3, `nub-storage` | `4f4cf0ca7ecbd24c284a5d63bcd85e3de6af37ca` |
| NAP-KEYS | PR #9, `nub-keys` | `8869a4cf77b023f4b049f47c546910a0280dc1a6` |
| NAP-MEDIA | PR #10, `nub-media` | `7806f438530251fce5129f8e6239d6b642278759` |
| NAP-NOTIFY | PR #11, `nub-notify` | `67877ef6c31ec8acee3125c1d8b4c781010e37dc` |
| NAP-CONFIG | PR #14, `nub-config` | `bed9cb5b1e7c9b5babee8870aa18b12949af1d62` |
| NAP-VALUE | PR #30, `nap-value` | `e468764d9f8a4f40107244cebed921bbebc0a0bf` |
| NAP-CVM | PR #31, `nap-cvm` | `28cf1bdb5c6412bfbfcecb79a5a5121e18376f2f` |
| NAP-OUTBOX | PR #32, `nap-outbox` | `8865f73d52a4864afee145f28d26520476273927` |
| NAP-UPLOAD | PR #33, `nap-upload` | `f5cc981e527e2cc1572793a7a6e5082e5271ac49` |
| NAP-POW | PR #39, `nap-pow` | `d85b4252f26fccd6c61bba18429ca9a6c0559210` |
| NAP-LINK | PR #53, `nap-link` | `100e5c939ae6b1ea82cc58587c6da45a1cf8a760` |
| NAP-RESOURCE | PR #80, `nub-resource` | `ae5b9c64ab8a4d8909f288829a01e99d6bd713bc` |
| NAP-DISPLAY | PR #97, `nap-display` | `2c2e1b5ca3849dbab8c3a721704e30646a641079` |
| SDK (where the text is silent) | `napplet/web` `main` | `49022721f5ed6067c158f1fee0a8daff6057d0e8` |
| Reference runtime (where the text is silent) | `kehto/web` `main` | `3181ac164eee4a4fc96020c053e8df16d1938298` |

All PRs were still open on 2026-11-21; none had merged since the digest was written.

## What is proved

### The composed machine (`Napplet/Runtime.lean`)

Over every `Runtime.Reachable` state:

- `Reachable.inv`: the composed invariant holds. It contains the NIP-5D shell
  invariant (`shell_inv`), says every bound port is listed, and says no NAP
  component holds state for a port that is not bound.
- `teardown_clears`: teardown clears every NAP's per-endpoint state, so a port that
  is later bound again starts clean. `port_closed_teardown` and
  `second_hello_teardown`: a closed port or a second `napplet.hello` closes the port,
  removes the frame, drops the binding and grants, and leaves no state in any NAP.
- `ctx_verified`: every endpoint context a component sees, which is its only source
  of the sender's identity, came from verified artifact bytes and carries exactly the
  policy exposure (lifts `dispatch_sender_verified`).
- `message_unbound_silent`, `message_unexposed_silent`: JSON on an unbound port, or
  for an unknown or unexposed domain, produces nothing.

Each component proves `decode (encodeReq r) = .ok r` and lifts its NAP's pure
results to what it actually emits. Examples: `Run.Relay.handle_sign`,
`onReply_delivers_plaintext`, `Run.Outbox.onReply_publish_relays`,
`Run.Resource.jobItems_policy` (no private hop, caps, sniffed MIME, no raw SVG),
`Run.Resource.cancel_drops_late`, `Run.Upload.onReply_put_requires_policy`,
`Run.Value.onReply_pay_authorized`, `Run.Link.onReply_opened_scheme_safe`,
`Run.Keys.handle_inv`, `Run.Media.handle_inv`, `Run.Config.snapshot_valid`,
`Run.Cvm.late_reply_dropped`, `Run.Pow.onReply_done_ok`, `Run.Inc.emit_delivery`,
`Run.Intent.handle_sends`, `Run.Storage.handle_isolated`. `Audit.lean` lists them.

### Napplet side

`Binding.boot_once` (one hello per document), `request_fresh` (fresh request ids),
`resolve_once` (a request settles once), `register_delivers_buffer` (retained pushes
reach a late handler in order). `Nip19` and `BindingUri` carry their vectors.

### Pure NAP models (`Napplet/Nap/*.lean`)

| Module | Spec | Results |
|---|---|---|
| `Manifest` | §5, §6 | `checkManifest_identity`: `artifactHash` is computed from the bytes. `checkManifest_single_x`, `checkManifest_rejects_mismatch`, `checkManifest_dTag` (`d` iff kind 35129). |
| `Capability` | §9, §11 | `exposure_ignores_declarations`: `R`/`O`/`z`/`i` never widen exposure. `missingRequired_none`: the full `R` set is checked. `compatible_iff`. `andFilter_is_not_compatibility` and `andFilter_admits_incompatible`: NIP-91 `&R` is not a compatibility test (the spec's own example). |
| `Wire` | §8 | `domain.action` routing vectors. |
| `Shell` | §6, §7, §16 | The shell transition function `step` and the inductive invariant `Inv` over every `Reachable` state. `nap_unbound_dropped` and `nap_dispatch_requires_binding`: NAP traffic is only processed from a bound port. `dispatch_sender_verified`: the sender identity on every dispatched message came from verified bytes, and its domain is in the policy exposure. `revoke_second_hello`, `revoke_window_msg`, `revoke_second_load`, `revoke_port_closed`: each closes the port, drops the binding and all grants, and removes the frame. `removed_stays_removed`, `no_rebind_removed`, `binding_unique_window`, `grants_only_bound`, `create_exposure`. |
| `Nap.Shell` | §15.1 | `init_exactly_once`, `init_at_most_once`, `init_capabilities` (the environment lists only that napplet's exposure). |
| `Nap.Intent` | §15.2, §8.1 | Handler precedence: `explicit_no_fallback`, `default_wins`, `unusable_recommendation_falls_back`. `invoke_delivery`: delivery goes only to the resolved handler and carries the authenticated sender. `invoke_single_delivery`, `invoke_result_first`. Convention URI binding: `bindUri_ok` (identity queryless and fragment-free, unique parameter names, no fragment outside `intent.invoke`), plus 10 vectors. |
| `Nap.Inc` | §15.3 | `emit_delivery`: exact-topic subscribers only, never the emitter, sender stamped by the runtime. `open_ok`: `opened` is enqueued before the result. `open_fail_unchanged`, `chEmit_delivery`, `close_notifies_both`, `destroy_clears`, `destroy_notifies_peers`. |
| `Nap.Theme` | §15.4 | `get_same_id`, `get_theme_xor_error`, `broadcast_only_exposed`, `broadcast_complete`. Required colours are enforced by the type. |
| `Nap.Storage` | §15.7 | `handle_isolated`: a request only touches the scope the runtime derived. `quota_preserved` (per-scope quota is an invariant), `keys_nodup_preserved`, `set_then_get`, `set_fail_unchanged`, `handle_same_id`. Scope separation: `shared_ne_instance`, `instances_isolated`, `bare_d_not_scope` (same `d`, different publisher, different scope), `artifact_hash_isolated`. |
| `Nap.Resource` | §15.8 | `bytes_no_private_hop`: no delivery through a private, loopback, link-local, ULA, CGNAT or metadata address on any hop (SSRF). `bytes_redirects_capped`, `bytes_size_capped`. `bytes_mime_sniffed_not_svg`: MIME is sniffed from the delivered bytes, and raw SVG is never delivered. `blossom_hash_verified`, `http_disabled_by_default`, `unknown_scheme_unsupported`. `bytesMany_items`: results keep input order and length, and each URL is independent. `cancel_drops_late`, `at_most_one_terminal`. IP classification vectors. |
| `Nap.Relay` | §15.6 | `broadcast_signed_by_shell`, `publish_requires_write`, `no_napplet_ciphertext_broadcast` (NIP-5D §Security 7), `publishEncrypted_shell_encrypts`. `delivery_plaintext` and `undecryptable_not_delivered`: napplets never see ciphertext. `delivery_only_matching_subscribers`, `subscribe_requires_read`, `close_stops_delivery`, `close_only_own`, `sidecar_default_off`, `sidecar_opt_out`, `publish_same_id`. |
| `Nap.Outbox` | §15.9 | `publish_single_event`, `publish_signed_by_shell`, `publish_requires_write`. Fanout: `plan_nodup`, `plan_allowed` (napplet-named relays cannot bypass relay policy), `plan_includes_outbox`, `plan_includes_inboxes`, `missing_inbox_reported`, `fallback_not_for_inboxes`. Queries: `query_nodup`, `query_sound`, `query_verified`, `getEvent_matches`. |
| `Nap.Upload` | §15.10 | `send_requires_policy`: bytes leave only after the rail, size, MIME and consent checks pass, to the shell-configured server. `send_auth_by_shell`. `complete_requires_confirmation` and `complete_hashes` (`sha256` covers the stored bytes; `originalSha256` appears exactly when transformed). `consent_latch`, `unsupported_rail_no_send`, `rejected_no_send`, `upload_same_id`. |
| `Nap.Value` | §15.16 | `pay_requires_consent_or_allowance`, `pay_within_policy`, `settled_requires_proof`, `failure_not_success`, `zap_signed_by_shell`. Allowances: `allowance_other_napplets_untouched`, `allowance_no_overspend` (the pool shrinks by exactly the amount paid, or not at all). `quote_not_binding`, `send_same_id`. |
| `Nap.Link` | §15.15 | `opened_scheme_safe`, `forbidden_never_opened` (`javascript:`, `data:`, `blob:`, `file:` and the like, even if policy lists them), `relative_rejected`, `label_irrelevant`, `opened_requires_user_or_rule`, `opened_noopener`, `open_same_id`. |
| `Nap.Notify` | §15.13 | `render_attributed`, `render_sanitized`, `render_actions_capped` (≤ 3), `send_requires_permission`, `send_error_creates_nothing`, `dismiss_only_own`, `dismiss_foreign_ignored`, `cleanup_removes_all`, `send_same_id`. |
| `Nap.Display` | §15.19 | `list_permitted`. `push_atomic`: an invalid batch changes nothing. `push_applies`: a valid batch sets exactly its pixels and touches no other pixel or display. |
| `Nap.Keys` | §15.11 | Canonical combos: `parse_render`, `normalize_idem`, `normalize_order_free`. The invariant (no reserved binding, no combo bound twice) is preserved by `Inv.register` and `Inv.unregister`. `reserved_never_suppressed`, `suppress_list_safe`, `text_input_never_forwarded`, `register_duplicate_rejected`, `register_other_napplets_untouched`, `bindings_push_complete`. |
| `Nap.Pow` | §15.18 | `submit_accepted` (fresh per-napplet id, target cap, queue room), `jobs_namespaced`. `mine_done`: the target is met, the user's pubkey is stamped, there is exactly one nonce tag, and template tags are kept. `publish_verbatim`, `pushes_to_owner`. |
| `Nap.Config` | §15.14 | `register_accepts_only_core` (no unsupported feature, depth ≤ 4, no secret with a default), `values_valid`, `values_declared`, `secret_never_defaulted`, `default_resolution`, `no_schema_error`, `handle_values_valid`. The shell is the sole writer by construction. |
| `Nap.Media` | §15.12 | The invariant is preserved by create, retire, command, focus and pause. `create_fresh`: ids are never reused, retired ones included. `retire_once`, `retired_silent`, `ops_preserve_owner`, `fetch_only_shell_owned`, `resume_only_after_focus_pause`, `user_pause_blocks_resume`. |
| `Nap.Cvm` | §15.17 | `timeout_ok` (never clamped), `timeout_120s_accepted`, `paid_requires_authority`, `deny_never_pays`, `free_always_allowed`, `reserve_never_overspends`. `response_routed_to_owner`, `transport_ids_fresh`, `late_response_dropped`, `duplicate_response_dropped`, `registry_call_hash_checked`, `exactly_one_result`, `unimplemented_has_false`, `unimplemented_unsupported`. |
| `Nap.Identity` | §15.5 | `handle_same_id`, `getPublicKey_no_error`, `change_notifies`, `signout_notifies`, `change_only_exposed`. Read-only by construction: `handle` returns no new state, and the request type has no signing or encryption operations. |

### Existing theorems and upstream

Every theorem from the earlier model still holds as stated about its own pure model.
Three pure models are narrower than upstream, and the runtime components follow
upstream instead:

- `NapIntent.invoke` delivers with the sender's *endpoint* (`invoke_delivery`);
  upstream's `IntentDelivery.sender` is the source's *catalog id*. `Run.Intent` uses
  the catalog id.
- `NapUpload.upload` answers a declined consent prompt with a top-level error;
  upstream's own example returns a `cancelled` result. `Run.Upload` follows the
  example, and `Run.Upload.gates_agree` relates the two.
- `NapInc` carries payloads as text; upstream payloads are any JSON. `Run.Inc`
  carries JSON and re-proves the delivery results.

None of the earlier theorems is false against the upstream text.

## Assumptions (not proved)

- The browser guarantees of the web projection: `Input.message p` really came from
  the port the shell bound, `Input.hello w ports` reports the true
  `MessageEvent.source` and transferred ports, the `sandbox="allow-scripts"` and CSP
  isolation hold, and the bootstrap's retained port is unreachable from napplet code
  (NIP-5D itself says no platform mechanism enforces this).
- The host meets the contracts in `Napplet/Host.lean` (cryptography, signer,
  network, prompts, storage servers, wallet, miner, ContextVM transport).

## Modelling decisions where the spec is silent

Each of these is a candidate clarification for the spec:

1. **`hello` with zero or several ports, before handoff.** The spec says to accept
   only exactly one port. The model drops it silently rather than tearing down.
2. **Window messages other than `hello` before handoff.** The spec revokes only
   "after handoff". The model ignores earlier ones.
3. **`hello` naming a port already bound to another frame.** This is not covered by
   the spec. The model drops it, which the invariant needs, because a port must
   belong to at most one window.
4. **Window ids are never reused.** This follows from "MUST NOT re-bind an identity to
   an existing iframe". The model makes `create` on any known window a no-op.
5. **Unknown names in `R`.** These are treated as missing required domains.
6. **INC `channel.open` to oneself.** This is not covered by the spec. The model
   rejects it as `"target not found"`.
7. **INTENT explicit handler that is not authorised.** The runtime asks the user
   (`Call.prompt .intent "authorize"`); a refusal or an incompatible handler gives
   `"invoke rejected"` (kehto's string), and it never falls back to a recommendation.
   (The pure `NapIntent.resolve` still returns no handler for an unauthorised
   explicit selection.)
8. **RELAY: decrypted delivery keeps the original `id` and `sig`.** The model
   delivers the event with `content` replaced by plaintext, as the spec says. The
   result is an event whose signature no longer verifies. This is the open
   review issue on napplet/naps#2. A `view` form would fix it.
9. **RELAY `relay.close` reply.** The spec defines none. The model replies with
   `relay.closed`. A refused `subscribe` also gets `relay.closed` with
   `"policy denied"`.
10. **RELAY: reusing a `subId`.** The new subscription replaces the caller's
    previous one with that `subId`. Subscriptions are namespaced per endpoint, so
    one napplet cannot close another's.
11. **RELAY ciphertext detection.** NIP-5D forbids signing ciphertext a napplet
    supplies, but gives no test for it. The model uses an opaque
    `looksCiphertext` predicate on the napplet-supplied content. For
    `publishEncrypted`, it checks the plaintext before the shell encrypts.
12. **RESOURCE address classes.** The spec lists RFC1918, loopback, link-local,
    ULA and 169.254.169.254. The model also blocks CGNAT (100.64/10),
    unspecified addresses (0/8 and `::`), broadcast, and IPv4-mapped IPv6.
13. **RESOURCE: duplicate in-flight request ids.** These are not covered by the
    spec. The model ignores the duplicate, so each accepted request gets exactly
    one terminal envelope.
14. **OUTBOX: unresolved `toInboxes` authors.** The model still publishes to every
    resolved relay. It lists unresolved authors in `missing` with
    `"relay list unavailable"`, and never substitutes fallback relays for them.
    The spec allows "include … or report failure" but does not say whether to
    publish at all.
15. **OUTBOX: own write set when NIP-65 is unavailable.** The model uses the
    fallback relays. The spec permits this for the user's own write set only.
16. **UPLOAD: MIME policy.** The model checks the shell's sniffed type, not the
    napplet-supplied `mimeType`. The spec does not say which the policy uses.
17. **UPLOAD: when consent is asked.** The model prompts on the first upload that
    passes every other check, and remembers approval per napplet. The spec says
    SHOULD and is otherwise silent.
18. **VALUE: allowance debit timing.** The model debits a covering allowance when
    it authorises the payment, before the backend replies, and does not refund a
    failed payment. This is conservative: budget is never double-spent. Whether
    failures should refund is unspecified.
19. **VALUE: allowance and consent.** A covering allowance replaces the prompt.
    Without one, the user is asked. A request no allowance covers is never
    partially charged against one.
20. **KEYS: modifier order.** The spec calls `Alt+Ctrl+Shift+Meta` "alphabetical",
    but it is not alphabetical (the open review issue). The model uses the stated
    order, and parses modifiers in any order to one canonical form. The key segment
    is compared exactly, so reserved Ctrl+W/T/L are listed in both cases.
21. **KEYS: conflicting `defaultKey`.** The spec says the shell MAY bind. The model
    leaves an action unbound if its hint is reserved or already bound, so no combo
    is ever bound twice.
22. **MEDIA: initial state.** After a successful create, the model starts a session
    `stopped`. The spec does not define the first state (open review issue).
23. **MEDIA: focus pause and user pause.** The model records that focus loss
    paused a session. A later user or napplet pause clears that, so focus regain
    never resumes it.
24. **NOTIFY: who may dismiss.** The spec says only to ignore unknown ids. The
    model also ignores ids owned by another napplet.
25. **LINK: `blocked-by-policy` vs `user-denied`.** A persisted deny rule gives
    `blocked-by-policy`. A declined prompt gives `user-denied`. The open review
    question is whether to pass the shell's own reason through instead.
26. **CONFIG: invalid defaults.** The model delivers a declared default only if it
    validates, consistent with "validate every value before delivery".
27. **CVM: payment price.** Price is an input. CEP-8 negotiation is not modelled,
    nor are the `-32042` interception mechanics.
28. **POW: timeout.** A search that returns a nonce failing the target is treated
    as a timeout. The shell never returns a result below target.

### Decisions added with the wire codec, composition and coverage

Shared:

29. **Repeated JSON members.** The last member with a name wins, as in browser
    `JSON.parse` (`Json.get?`).
30. **Event templates.** Upstream types templates as open maps. The shell reads
    NIP-01 fields only: `kind` is required, `content` defaults to `""`, `tags` to `[]`
    and `created_at` to the shell clock; other members are dropped before signing.
31. **Malformed requests.** A known type with a malformed payload and a string `id`
    gets its result envelope with the NAP's own error string where upstream defines
    one for invalid input, else `"invalid request"`. Without a usable `id`, or for
    fire-and-forget types, it is dropped. Unknown types are always silently ignored.
    This matches kehto's practice.
32. **Request ids on the napplet side.** The SDK uses `crypto.randomUUID()`; the model
    uses a counter. Only freshness among pending requests matters.
33. **Endpoint and catalog identifiers.** INC endpoint ids are `endpoint-<window>`
    (window ids are never reused); catalog ids use kehto's `nip5d:<kind>:…` encoding.
34. **Async host work.** Network, signer, prompts, wallet, storage servers, mining and
    ContextVM are host calls with tagged replies; a reply whose tag the runtime no
    longer holds (teardown, cancel) has no effect. Prompts never block other inputs.

INC: subscriptions are a set per (endpoint, topic), so `inc.unsubscribe {topic}`
removes it; channel ids are `c-<n>`; an open to an unknown, non-live, self or
`inc`-unexposed target fails with `"target not found"`, ACL refusal with
`"target denied"` and a channel cap with `"channel limit reached"` (kehto); endpoint
destruction sends `"peer destroyed"` to the surviving peer only.

INTENT: unknown request members (including any `sender`) are ignored; a malformed
`request` gets `{ok:false, error:"invalid convention"}`; `"no handler"` when no
candidate serves the role, `"unsupported convention"` when candidates exist but
none matches; a hint address maps to the catalog id `nip5d:<address>`; one
compatible candidate is used directly, several prompt a chooser; a default applies
only if it supports the convention; accepted deliveries are retained FIFO until a
target with that catalog id is bound (`Effect launch`), or the host reports
`launchFailed`. Uninstalled-recommendation discovery (MAY) is not offered.

RELAY: `relay.close` and a refused `subscribe` reply `relay.closed` (decision 9,
also kehto); a refused query replies `{id, error:"policy denied"}`; scoped relay
URLs must be `wss://` (`"invalid relay destination"`, kehto); `relay.eose` and the
query result wait for in-flight decryptions of stored events; relay hints carry the
relay an event was observed on; sidecar byte pre-resolution is never performed (a
MAY; this satisfies default-off and every opt-out). Error strings not defined
upstream follow kehto (`"no signer configured"`, `"publish failed"`, `"relay query
closed"`).

OUTBOX: reads route to the authors' allowed NIP-65 write relays, else fallback
relays, plus allowed napplet hints, with `incomplete:true` when a list is missing;
`resolveRelays` reports `source` `nip65` or `fallback` and an empty `policy` plan on
error; an empty publish plan is `ok:false` with `"relay list unavailable"`;
`outbox.close` replies `outbox.closed`; `timeoutMs` is enforced by the host closing
the stream; the NIP-5D ciphertext check also applies to `outbox.publish`.

RESOURCE: wire blobs are strict canonical base64 (non-canonical rejected); `data:`
URLs are decoded in the model; duplicate in-flight ids are ignored (decision 13);
at most 10 URLs per endpoint are in flight, the rest queue; the per-minute rate
limit has no upstream error code and is not modelled; `resource.info.error` only
when the shell does not disclose schemes; `htree` identifiers must be `npub` or
64-hex (aliases rejected), and `nostr:` accepts only non-secret NIP-19 entities.

UPLOAD: the structured-clone `Blob` is modelled as its byte list (a JSON array of
bytes); a declined consent is a `cancelled` result per upstream's example; errors
before an upload exists are top-level (upstream's open issue); `"unknown upload"`
for an unknown status id (kehto); uploads up to 1 MiB answer `complete` directly,
larger ones `uploading` then push; success requires the server's hash to match the
bytes sent (`"server rejected"` otherwise).

LINK: a missing URL is `invalid-url`; `http`/`https` without a host is
`invalid-url`; with prompting off or too many outstanding prompts the answer is
`blocked-by-policy`; the scheme is re-checked when the prompt is answered; rules
are keyed by manifest key and a deny rule wins.

NOTIFY: only the wire names `notify.channel.register` and
`notify.permission.request` are decoded (upstream's API table also says
`registerChannel`/`requestPermission`); permission is required by default and
lasts for the endpoint's lifetime; ids are `shell-<n>`; more than three actions are
truncated (MAY limit); `notify.controls` is pushed once per endpoint; a malformed
`permission.request` gets `granted:false`.

DISPLAY: device access is denied unless policy permits; checks run `not-found`,
`unavailable`, `denied`, then the batch; a missing `displayId` is
`"invalid request"`.

KEYS: single-character keys are upper-cased before matching (`Ctrl+s` matches a
`Ctrl+S` binding; upstream's examples use both, kehto upper-cases); a trailing `++`
is the `+` key; re-registering an action id is `"duplicate action ID"` (kehto
replaces); an unparseable `defaultKey` is `"invalid action"`; a forwarded combo that
is bound also fires `keys.action` to the owner.

MEDIA: creation errors are decided synchronously; later backend failures retire the
session with reason `error`; a napplet's session id hint is honoured if fresh and not
`shell-` prefixed; ids are never reused in a runtime session; out-of-range numbers
are dropped; caller reasons on commands are replaced by `user`; a napplet-owned
session that cannot pause on focus loss is retired with `policy`; a failed create
result omits `sessionId` (upstream's prose; its example includes it).

CONFIG: a rejected schema is reported only in `config.registerSchema.result`;
unknown standard keywords are `invalid-schema`; `$schema` may be draft-07, 2019-09 or
2020-12; a lower version is `version-conflict`; defaults resolve persisted → own
default → ancestor default, invalid candidates skipped (decision 26); secrets
resolve only from a persisted value; orphaned properties are pruned when a schema is
accepted; schemas persist per scope; `openSettings` without a schema is ignored.

VALUE: errors before a transfer exists are top-level (upstream's wire table marks
`result` required); preimages are not disclosed by default (upstream says both
"keep out of the sandbox" and "when safe to disclose"); `"transfer not found"` for
an unknown status id (kehto); a zero amount is out of policy; a zap target needs a
pubkey or address.

CVM: each network operation has a host timer for its deadline; payment gates
return to the shell as an offer and are settled only after `decidePay`; payments
are off by default (`"payment required"`); the registry is off by default
(`"unsupported method"`, `registry.has` → `false`); only server notifications and
requests become `cvm.event`.

POW: FIFO scheduling (priority reported, not used); rejections carry
`state:"error"`; the host's nonce is re-checked in the shell and a miss is
`"timeout"` (decision 28); `pause`/`resume` without `jobId` act on the whole miner;
publish asks for consent by default; NIP-01 ids and leading-zero bits are computed in
the model.

## Not modelled yet

- The deferred CLASS and CONNECT tracks.
- Behaviour upstream leaves undefined:
  - NAP-MEDIA's out-of-band source binding.
  - NIP-59 gift-wrap decryption depth (the host's `encryptedWith`/`decrypt` decide it).
  - Carrier attachment of NAP-RESOURCE sidecars (NAP-RESOURCE defers it to the
    carrier specs; NAP-RELAY's attachment is never produced, see RELAY above).
  - Cancelling an in-progress upload (NAP-UPLOAD has no wire message for it).
  - Paged `relay.query` (`stream: true`), proposed in review but absent.

Optional behaviours the model leaves out on purpose (all MAY or unquantified SHOULD):
INC `shell:*` topic interception and emit ACLs, INTENT discovery of uninstalled
recommendations, RESOURCE single-flight caching and per-minute rate limits, MEDIA
promoted (detached) playback, CONFIG's `config.settingsOpened` acknowledgement and
`$version` migration across artifact hashes.

## Licence

[Mozilla Public License 2.0](../LICENSE).
