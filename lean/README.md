# Napplet protocol: Lean 4 model

A machine-checked model of the NIP-5D core, the five NAPs merged to
`napplet/naps` `master` (SHELL, INTENT, INC, THEME, IDENTITY), and three NAPs from
open PR branches (STORAGE, RESOURCE, RELAY). Section numbers refer
to [`../NAPPLETS-SPEC.md`](../NAPPLETS-SPEC.md).

- Lean `v4.36.0`, no Mathlib, no dependencies.
- No `sorry`. Proofs use only Lean's standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`). Cryptography is passed in as an opaque `Crypto` record, so the model
  adds no axioms of its own.
- Conformance vectors that need evaluation (string splitting, percent-decoding) are
  `#guard` checks, run on every build.

```bash
cd lean && lake build
```

## What is proved

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
| `Nap.Identity` | §15.5 | `handle_same_id`, `getPublicKey_no_error`, `change_notifies`, `signout_notifies`, `change_only_exposed`. Read-only by construction: `handle` returns no new state, and the request type has no signing or encryption operations. |

## Assumptions (not proved)

These are browser guarantees, modelled as the shape of the inputs:

- The `WindowId` on an event is the true `MessageEvent.source`.
- The ports listed in `hello` are the ports actually transferred.
- The bootstrap's retained port is unreachable from napplet code. NIP-5D itself says
  no platform mechanism enforces this.
- The `sandbox="allow-scripts"` and CSP isolation hold.
- `sha256` and signature checks are sound (`Crypto` is opaque).

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
7. **INTENT explicit handler that is not authorised.** The model resolves to no
   handler (`"no handler"`) and never falls back.
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

## Not modelled yet

OUTBOX, UPLOAD, KEYS, MEDIA, NOTIFY, CONFIG, LINK, VALUE, CVM, POW and DISPLAY
(all on open PR branches); RESOURCE's `hashtree`/`htree`/`nostr` scheme details and
canonical base64; message payload schemas beyond what the proofs need; NIP-19
`naddr` decoding; and the deferred CLASS and CONNECT tracks.
