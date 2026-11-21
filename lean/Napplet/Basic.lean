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

/-- Manifest key (NAP-STORAGE, NAP-RESOURCE and NAP-CONFIG §Identity Scope; NAP-INTENT
§Catalog identifiers): named = (publisher, kind, `d`), root = (publisher, kind),
snapshot = signed event id. A bare `d` never identifies anything. -/
inductive ManifestKey where
  | named (publisher : Pubkey) (d : String)
  | root (publisher : Pubkey)
  | snapshot (eventId : String)
  deriving DecidableEq, Repr

/-- The verified napplet principal the runtime binds to a port.

NIP-5D §Identity defines napplet identity as `(dTag, artifactHash)`; those are the
first two fields. The NAP identity scopes also need the manifest's publisher, kind
and signed event id, which NIP-5D's identity tuple does not carry (a bare `d` is
not publisher-scoped). The runtime computes all five from the verified manifest
event and artifact bytes (`checkManifest`); none comes from the napplet or a host. -/
structure Identity where
  dTag : Option String
  artifactHash : Hash
  /-- Manifest event `pubkey` (the publisher). -/
  publisher : Pubkey := ""
  kind : ManifestKind := .named
  /-- Manifest event `id` (NIP-01 event id). -/
  eventId : String := ""
  deriving DecidableEq, Repr

namespace Identity

/-- NIP-5D's identity tuple. -/
def nip5d (i : Identity) : Option String × Hash := (i.dTag, i.artifactHash)

/-- The manifest key, derived in exactly one place. -/
def key (i : Identity) : ManifestKey :=
  match i.kind with
  | .named => .named i.publisher (i.dTag.getD "")
  | .root => .root i.publisher
  | .snapshot => .snapshot i.eventId

/-- Runtime catalog identifier (NAP-INTENT §Catalog identifiers), using the
encoding of the kehto reference runtime (`@kehto/nip` `getNappletCatalogId`):
`nip5d:35129:<pubkey>:<d>`, `nip5d:15129:<pubkey>`, `nip5d:5129:<event id>`. -/
def catalogId (i : Identity) : String :=
  match i.key with
  | .named p d => "nip5d:35129:" ++ p ++ ":" ++ d
  | .root p => "nip5d:15129:" ++ p
  | .snapshot e => "nip5d:5129:" ++ e

end Identity

/-- Point update of a function. Used for all finite-map state in the model. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

@[simp] theorem upd_other {α β : Type} [DecidableEq α] (f : α → β) (a x : α) (b : β)
    (h : x ≠ a) : upd f a b x = f x := by simp [upd, h]

end Napplet
