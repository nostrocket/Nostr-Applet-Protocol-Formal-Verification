# Napplet protocol: Lean 4 model

A machine-checked model of the NIP-5D core and the five NAPs merged to
`napplet/naps` `master` (SHELL, INTENT, INC, THEME, IDENTITY). Section numbers refer
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

## Not modelled yet

The 16 NAPs that are still on PR branches (RELAY, STORAGE, RESOURCE, …), message
payload schemas beyond what these proofs need, NIP-19 `naddr` decoding, and the
deferred CLASS and CONNECT tracks.
