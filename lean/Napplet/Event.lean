/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Json
import Napplet.Basic

/-!
# Nostr events on the wire (NIP-01)

The shared event shapes several NAPs carry: a signed `NostrEvent`, an unsigned
event the shell asks its signer to sign, and the napplet-supplied
`EventTemplate`. Field names are NIP-01's (`created_at`, not `createdAt`).

NAP-RELAY types templates and events as open maps (`{ * tstr => any }`). The model
reads the NIP-01 fields and drops anything else: the shell signs only what NIP-01
defines (modelling decision 30). A template must carry an unsigned-integer `kind`;
`content` defaults to `""`, `tags` to `[]`, and `created_at` to the shell clock.
-/

namespace Napplet

abbrev EventTag := List String

/-- A signed NIP-01 event. -/
structure NostrEvent where
  id : String
  pubkey : Pubkey
  createdAt : Nat
  kind : Nat
  tags : List EventTag
  content : String
  sig : String
  deriving DecidableEq, Repr, Inhabited

/-- An event ready for the signer: the shell has stamped `pubkey` and `created_at`. -/
structure UnsignedEvent where
  pubkey : Pubkey
  createdAt : Nat
  kind : Nat
  tags : List EventTag
  content : String
  deriving DecidableEq, Repr, Inhabited

/-- A napplet-supplied event template. -/
structure EventTemplate where
  kind : Nat
  content : String := ""
  tags : List EventTag := []
  createdAt : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

namespace EventTemplate

/-- Stamp a template for signing with the user's key and the shell clock. -/
def stamp (t : EventTemplate) (pubkey : Pubkey) (now : Nat) : UnsignedEvent :=
  { pubkey, createdAt := t.createdAt.getD now, kind := t.kind, tags := t.tags, content := t.content }

end EventTemplate


namespace NostrEvent

def toJson (e : NostrEvent) : Json :=
  .obj [("id", .str e.id), ("pubkey", .str e.pubkey), ("created_at", .nat e.createdAt),
        ("kind", .nat e.kind), ("tags", Json.tags e.tags), ("content", .str e.content),
        ("sig", .str e.sig)]

def ofJson? (j : Json) : Option NostrEvent := do
  let id ← (j.get? "id").bind Json.asStr?
  let pubkey ← (j.get? "pubkey").bind Json.asStr?
  let createdAt ← (j.get? "created_at").bind Json.asNat?
  let kind ← (j.get? "kind").bind Json.asNat?
  let tags ← (j.get? "tags").bind Json.asTags?
  let content ← (j.get? "content").bind Json.asStr?
  let sig ← (j.get? "sig").bind Json.asStr?
  some { id, pubkey, createdAt, kind, tags, content, sig }

end NostrEvent

namespace UnsignedEvent

def toJson (e : UnsignedEvent) : Json :=
  .obj [("pubkey", .str e.pubkey), ("created_at", .nat e.createdAt), ("kind", .nat e.kind),
        ("tags", Json.tags e.tags), ("content", .str e.content)]

end UnsignedEvent

namespace EventTemplate

/-- Decode a template. `kind` is required; other NIP-01 fields default; extra
members are ignored. A present member of the wrong type is malformed. -/
def ofJson? (j : Json) : Option EventTemplate := do
  guard j.isObj
  let kind ← (j.get? "kind").bind Json.asNat?
  let content ← match j.get? "content" with
    | none => some ""
    | some c => c.asStr?
  let tags ← match j.get? "tags" with
    | none => some []
    | some t => t.asTags?
  let createdAt ← match j.get? "created_at" with
    | none => some none
    | some c => c.asNat?.map some
  some { kind, content, tags, createdAt }

def toJson (t : EventTemplate) : Json :=
  Json.mkObj [("kind", some (.nat t.kind)), ("content", some (.str t.content)),
              ("tags", some (Json.tags t.tags)), ("created_at", t.createdAt.map Json.nat)]

end EventTemplate

/-! ### Round trips -/

@[simp] theorem NostrEvent.ofJson?_toJson (e : NostrEvent) :
    NostrEvent.ofJson? e.toJson = some e := by
  simp [NostrEvent.ofJson?, NostrEvent.toJson, Json.get?, Json.lookup, Json.asStr?]

@[simp] theorem EventTemplate.ofJson?_toJson (t : EventTemplate) :
    EventTemplate.ofJson? t.toJson = some t := by
  obtain ⟨k, c, ts, ca⟩ := t
  cases ca <;> simp [EventTemplate.ofJson?, EventTemplate.toJson, Json.mkObj, Json.get?,
    Json.lookup, Json.isObj, Json.asNat?_nat] <;> rfl

#guard (NostrEvent.ofJson? (NostrEvent.toJson
  { id := "a", pubkey := "b", createdAt := 1, kind := 1, tags := [["p", "x"]], content := "hi",
    sig := "s" })).isSome
#guard EventTemplate.ofJson? (Json.parse! "{\"kind\":1,\"content\":\"hello world\",\"tags\":[],\"created_at\":1234567890}") ==
  some { kind := 1, content := "hello world", tags := [], createdAt := some 1234567890 }
#guard EventTemplate.ofJson? (Json.parse! "{\"content\":\"x\"}") == none
#guard EventTemplate.ofJson? (Json.parse! "{\"kind\":1,\"tags\":\"no\"}") == none

end Napplet
