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

-- NIP-5D core
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
