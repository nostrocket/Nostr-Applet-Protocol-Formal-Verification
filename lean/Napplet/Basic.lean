/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

/-!
# Napplet: basic types

Shared vocabulary for the NIP-5D / NAP model. See `NAPPLETS-SPEC.md` §3–§4.

Cryptography is not modelled. Hashing and signature checks are supplied as an
opaque `Crypto` record (see `Napplet.Manifest`), so no axioms are introduced.
-/

namespace Napplet

/-- Lowercase-hex SHA-256 digest. Opaque in this model. -/
abbrev Hash := String
/-- Hex public key. -/
abbrev Pubkey := String
/-- Artifact bytes. -/
abbrev Bytes := List UInt8
/-- Identifies an iframe `Window` the shell created (`MessageEvent.source`). -/
abbrev WindowId := Nat
/-- Identifies a transferred `MessagePort`. -/
abbrev PortId := Nat
/-- An authenticated napplet endpoint is its bound port. -/
abbrev Endpoint := PortId

/-- NAP domains from the registry (spec §15). -/
inductive Domain where
  | shell | intent | inc | theme | identity | relay | storage | keys | media
  | notify | resource | config | upload | value | outbox | cvm | link | pow | display
  deriving DecidableEq, Repr, Inhabited

namespace Domain

/-- Bare domain name as used in `R`, `O`, `N` tags and `type` prefixes. -/
def name : Domain → String
  | shell => "shell" | intent => "intent" | inc => "inc" | theme => "theme"
  | identity => "identity" | relay => "relay" | storage => "storage" | keys => "keys"
  | media => "media" | notify => "notify" | resource => "resource" | config => "config"
  | upload => "upload" | value => "value" | outbox => "outbox" | cvm => "cvm"
  | link => "link" | pow => "pow" | display => "display"

/-- Parse a bare domain name. Unknown names are `none`. -/
def ofName? : String → Option Domain
  | "shell" => some shell | "intent" => some intent | "inc" => some inc
  | "theme" => some theme | "identity" => some identity | "relay" => some relay
  | "storage" => some storage | "keys" => some keys | "media" => some media
  | "notify" => some notify | "resource" => some resource | "config" => some config
  | "upload" => some upload | "value" => some value | "outbox" => some outbox
  | "cvm" => some cvm | "link" => some link | "pow" => some pow | "display" => some display
  | _ => none

theorem ofName?_name (d : Domain) : ofName? d.name = some d := by
  cases d <;> rfl

/-- Spec-form names (`NAP-RELAY`) are not domain names (NIP-5D shell handlers). -/
example : ofName? "NAP-RELAY" = none := by decide

end Domain

/-- Manifest kinds (NIP-5D §Manifest). -/
inductive ManifestKind where
  /-- 5129: regular event pinning one immutable version. -/
  | snapshot
  /-- 15129: replaceable root napplet. -/
  | root
  /-- 35129: addressable named napplet (has `d`). -/
  | named
  deriving DecidableEq, Repr

namespace ManifestKind

def toNat : ManifestKind → Nat
  | snapshot => 5129 | root => 15129 | named => 35129

def ofNat? : Nat → Option ManifestKind
  | 5129 => some snapshot | 15129 => some root | 35129 => some named | _ => none

theorem ofNat?_toNat (k : ManifestKind) : ofNat? k.toNat = some k := by
  cases k <;> rfl

end ManifestKind

/-- Napplet identity `(dTag, artifactHash)` (NIP-5D §Identity). -/
structure Identity where
  dTag : Option String
  artifactHash : Hash
  deriving DecidableEq, Repr

/-- Point update of a function. Used for all finite-map state in the model. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

@[simp] theorem upd_other {α β : Type} [DecidableEq α] (f : α → β) (a x : α) (b : β)
    (h : x ≠ a) : upd f a b x = f x := by simp [upd, h]

end Napplet
