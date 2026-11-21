/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-IDENTITY (`identity`)

Read-only queries about the shell user. By construction `handle` returns only a
response and never a new user state, and the request type has no signing,
encryption or decryption operation.
-/

namespace Napplet.NapIdentity

inductive IdentityReq where
  | getPublicKey (id : String)
  | getRelays (id : String)
  | getProfile (id : String)
  | getFollows (id : String)
  | getList (id : String) (listType : String)
  | getZaps (id : String)
  | getMutes (id : String)
  | getBlocked (id : String)
  | getBadges (id : String)
  deriving DecidableEq, Repr

def IdentityReq.id : IdentityReq → String
  | getPublicKey i | getRelays i | getProfile i | getFollows i | getList i _
  | getZaps i | getMutes i | getBlocked i | getBadges i => i

/-- What the shell knows about the user. `pubkey = ""` means no signer. -/
structure UserView where
  pubkey : String
  follows : List String
  mutes : List String
  blocked : List String
  lists : String → Option (List String)

inductive Payload where
  | pubkey (pk : String)
  | pubkeys (pks : List String)
  | entries (es : List String)
  | opaque
  deriving DecidableEq, Repr

inductive IdentityOut where
  | result (to : Endpoint) (id : String) (payload : Option Payload) (error : Option String)
  | changed (to : Endpoint) (pubkey : String)
  deriving DecidableEq, Repr

/-- Answer a request on endpoint `to`. -/
def handle (u : UserView) (to : Endpoint) : IdentityReq → IdentityOut
  | .getPublicKey i => .result to i (some (.pubkey u.pubkey)) none
  | .getFollows i => .result to i (some (.pubkeys u.follows)) none
  | .getMutes i => .result to i (some (.pubkeys u.mutes)) none
  | .getBlocked i => .result to i (some (.pubkeys u.blocked)) none
  | .getList i lt =>
    match u.lists lt with
    | some es => .result to i (some (.entries es)) none
    | none => .result to i none (some "unsupported list type")
  | .getRelays i | .getProfile i | .getZaps i | .getBadges i => .result to i (some .opaque) none

/-- Every request gets a result on the same endpoint with the same `id`. -/
theorem handle_same_id (u : UserView) (to : Endpoint) (r : IdentityReq) :
    ∃ p e, handle u to r = .result to r.id p e := by
  cases r <;> simp only [handle, IdentityReq.id]
  case getList i lt => split <;> exact ⟨_, _, rfl⟩
  all_goals exact ⟨_, _, rfl⟩

/-- `identity.getPublicKey.result` never carries `error`. -/
theorem getPublicKey_no_error (u : UserView) (to : Endpoint) (i : String) :
    handle u to (.getPublicKey i) = .result to i (some (.pubkey u.pubkey)) none := rfl

/-- On a user change (including sign-out to `""`), notify every endpoint with
`identity` exposed. -/
def onUserChange (eps : List (Endpoint × List Domain)) (old new : String) : List IdentityOut :=
  if old = new then []
  else (eps.filter fun e => decide (Domain.identity ∈ e.2)).map fun e => .changed e.1 new

theorem change_notifies {eps : List (Endpoint × List Domain)} {old new : String}
    (hne : old ≠ new) {to : Endpoint} {ds : List Domain} (hm : (to, ds) ∈ eps)
    (hd : Domain.identity ∈ ds) : IdentityOut.changed to new ∈ onUserChange eps old new := by
  simp [onUserChange, hne]
  exact ⟨ds, hm, hd⟩

theorem signout_notifies {eps : List (Endpoint × List Domain)} {old : String} (h : old ≠ "")
    {to : Endpoint} {ds : List Domain} (hm : (to, ds) ∈ eps) (hd : Domain.identity ∈ ds) :
    IdentityOut.changed to "" ∈ onUserChange eps old "" :=
  change_notifies h hm hd

theorem change_only_exposed {eps : List (Endpoint × List Domain)} {old new pk : String}
    {to : Endpoint} (h : IdentityOut.changed to pk ∈ onUserChange eps old new) :
    ∃ ds, (to, ds) ∈ eps ∧ Domain.identity ∈ ds := by
  unfold onUserChange at h
  split at h
  · simp at h
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq,
      IdentityOut.changed.injEq] at h
    obtain ⟨⟨a, ds⟩, ⟨hm, hd⟩, rfl, -⟩ := h
    exact ⟨ds, hm, hd⟩

end Napplet.NapIdentity
