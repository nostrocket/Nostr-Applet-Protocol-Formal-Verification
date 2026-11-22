/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet

/-!
# Axiom audit

Prints the axioms each headline theorem depends on. CI fails if anything other than
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) appears, which
rules out `sorryAx` and `Lean.ofReduceBool` (`native_decide`).

Run with `lake env lean Audit.lean`.
-/

open Napplet

-- The composed machine (Runtime.step over JSON): headline results
#print axioms Runtime.Reachable.inv
#print axioms Runtime.shell_inv
#print axioms Runtime.teardown_clears
#print axioms Runtime.port_closed_teardown
#print axioms Runtime.second_hello_teardown
#print axioms Runtime.ctx_verified
#print axioms Runtime.message_unbound_silent
#print axioms Runtime.message_unexposed_silent
-- routing: each NAP's component, with the binding-derived context, is exactly what
-- Runtime.step runs for that domain, so every component theorem below holds of it
#print axioms Runtime.message_dispatch
#print axioms Runtime.message_shellNap
#print axioms Runtime.message_theme
#print axioms Runtime.message_identity
#print axioms Runtime.message_storage
#print axioms Runtime.message_inc
#print axioms Runtime.message_intent
#print axioms Runtime.message_notify
#print axioms Runtime.message_display
#print axioms Runtime.message_keys
#print axioms Runtime.message_relay
#print axioms Runtime.message_outbox
#print axioms Runtime.message_media
#print axioms Runtime.message_config
#print axioms Runtime.message_resource
#print axioms Runtime.message_upload
#print axioms Runtime.message_link
#print axioms Runtime.message_value
#print axioms Runtime.message_cvm
#print axioms Runtime.message_pow
-- components as composed (each runs with the context Runtime derives from the binding)
#print axioms Run.Shell.init_exactly_once
#print axioms Run.Shell.check_one_reply
#print axioms Run.Shell.check_caller_independent
#print axioms Run.Shell.check_agrees_with_load
#print axioms Run.Identity.profile_present
#print axioms Run.Theme.changed_only_exposed
#print axioms Run.Identity.getPublicKey_no_error
#print axioms Run.Storage.handle_isolated
#print axioms Run.Storage.handle_quota
#print axioms Run.Inc.emit_delivery
#print axioms Run.Inc.open_ok
#print axioms Run.Intent.handle_sends
#print axioms Run.Intent.launch_outputs
#print axioms Run.Intent.launch_absent_rejected
#print axioms Run.Intent.replay_effects
#print axioms Run.Relay.handle_sign
#print axioms Run.Relay.onReply_delivers_plaintext
#print axioms Run.Outbox.onReply_publish_relays
#print axioms Run.Resource.jobItems_policy
#print axioms Run.Resource.cancel_drops_late
#print axioms Run.Upload.onReply_put_requires_policy
#print axioms Run.Value.onReply_pay_authorized
#print axioms Run.Link.onReply_opened_scheme_safe
#print axioms Run.Notify.show_safe
#print axioms Run.Display.push_applies
#print axioms Run.Keys.handle_inv
#print axioms Run.Media.handle_inv
#print axioms Run.Config.snapshot_valid
#print axioms Run.Cvm.late_reply_dropped
#print axioms Run.Pow.onReply_done_ok
-- wire codec round trips
#print axioms NostrEvent.ofJson?_toJson
#print axioms EventTemplate.ofJson?_toJson
#print axioms Run.Storage.decode_encodeReq
#print axioms Run.Relay.decode_encodeReq
#print axioms Run.Resource.Base64.encode_decode?
-- napplet side (bootstrap and binding)
#print axioms Binding.boot_once
#print axioms Binding.request_fresh
#print axioms Binding.resolve_once
#print axioms Binding.register_delivers_buffer
-- identity
#print axioms checkManifest_principal

-- NIP-5D core (pure shell)
#print axioms checkManifest_identity
#print axioms checkManifest_dTag
#print axioms andFilter_is_not_compatibility
#print axioms Inv.step
#print axioms dispatch_sender_verified
#print axioms revoke_port_closed
#print axioms no_rebind_removed
#print axioms binding_unique_window
-- merged NAPs
#print axioms NapShell.init_exactly_once
#print axioms NapShell.init_capabilities
#print axioms NapShell.domains_supports
#print axioms NapShell.assess_incompatible_iff
#print axioms NapShell.assess_agrees_with_load
#print axioms checkManifestEvent_agrees
#print axioms NapIntent.explicit_no_fallback
#print axioms NapIntent.invoke_delivery
#print axioms NapIntent.bindUri_ok
#print axioms NapInc.emit_delivery
#print axioms NapInc.open_ok
#print axioms NapTheme.broadcast_only_exposed
#print axioms NapIdentity.handle_same_id
-- NAPs on PR branches
#print axioms NapStorage.quota_preserved
#print axioms NapStorage.handle_isolated
#print axioms NapResource.bytes_no_private_hop
#print axioms NapResource.at_most_one_terminal
#print axioms NapRelay.delivery_plaintext
#print axioms NapRelay.no_napplet_ciphertext_broadcast
#print axioms NapOutbox.plan_allowed
#print axioms NapUpload.send_requires_policy
#print axioms NapValue.pay_requires_consent_or_allowance
#print axioms NapValue.allowance_no_overspend
#print axioms NapLink.forbidden_never_opened
#print axioms NapNotify.dismiss_only_own
#print axioms NapDisplay.push_applies
#print axioms NapKeys.Inv.register
#print axioms NapPow.mine_done
#print axioms NapConfig.secret_never_defaulted
#print axioms NapMedia.create_fresh
#print axioms NapMedia.retire_once
#print axioms NapCvm.paid_requires_authority
#print axioms NapCvm.duplicate_response_dropped
-- finite representation (Refine): step' refines Runtime.step, memory follows live state
#print axioms Refine.abs_step'
#print axioms Refine.step'_outputs
#print axioms Refine.WF.step'
#print axioms Refine.Reachable'.abs
#print axioms Refine.live_keys
#print axioms Refine.bindings_keys
#print axioms Refine.grants_keys
#print axioms Refine.inst_keys
#print axioms Refine.ports_bound
#print axioms Refine.components_bound
#print axioms Refine.removed_length_le
#print axioms Ivs.length_le
#print axioms Runtime.step_frame
-- persistence and restore
#print axioms Persist.persist_restore
#print axioms Persist.decPersisted_enc
#print axioms Persist.restore_clean
#print axioms Persist.Inv.restore
#print axioms Persist.Restored.inv
#print axioms Persist.Restored.teardown_clears
#print axioms Persist.Restored.port_closed_teardown
#print axioms Persist.Restored.second_hello_teardown
#print axioms Persist.Restored.ctx_verified
#print axioms Persist.Restored.quota
#print axioms Persist.Reachable.quota
#print axioms Persist.Reachable''.abs
#print axioms Persist.Persisted.check_wf
-- JSON codecs of the runtime interface
#print axioms Codec.decInput_enc
#print axioms Codec.decOutput_enc
#print axioms Codec.decCall_enc
#print axioms Codec.decReply_enc
#print axioms Codec.decEffect_enc
#print axioms Codec.decHostEvent_enc
#print axioms Codec.decManifestEvent_enc
-- srcdoc
#print axioms Srcdoc.csp_first
#print axioms Srcdoc.buildSrcdoc_bytes
#print axioms Srcdoc.step_app
