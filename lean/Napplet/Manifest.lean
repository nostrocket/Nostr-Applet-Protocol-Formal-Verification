/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# Manifest verification (NIP-5D §Manifest, §Identity)

`checkManifest` is the runtime's pre-iframe verification: signature, kind, the
single `x` tag, `d` cardinality, non-empty `content`, lineage only on snapshots,
and `sha256(bytes) = x`.

The key property is `checkManifest_identity`: the napplet identity's
`artifactHash` is computed from the artifact bytes, never taken from a host.
-/

namespace Napplet

/-- A Nostr tag `[name, values...]`. -/
structure Tag where
  name : String
  values : List String
  deriving DecidableEq, Repr

/-- The parts of a manifest event the runtime inspects. -/
structure ManifestEvent where
  kind : Nat
  pubkey : Pubkey
  content : String
  tags : List Tag
  deriving Repr

namespace ManifestEvent

def tagsNamed (m : ManifestEvent) (n : String) : List Tag :=
  m.tags.filter (·.name == n)

/-- First value of every tag with this name (e.g. all `R` domains). -/
def firstValues (m : ManifestEvent) (n : String) : List String :=
  (m.tagsNamed n).filterMap (·.values.head?)

end ManifestEvent

/-- Opaque cryptographic primitives supplied by the environment. -/
structure Crypto where
  sha256 : Bytes → Hash
  verifySig : ManifestEvent → Bool

inductive ManifestError where
  | badSignature
  | badKind
  | xTagCount
  | dTagCount
  | emptyContent
  | lineageOnNonSnapshot
  | hashMismatch
  | missingRequired (name : String)
  deriving DecidableEq, Repr

/-- A manifest that passed `checkManifest` against specific bytes. -/
structure VerifiedManifest where
  kind : ManifestKind
  identity : Identity
  required : List String
  optional : List String
  archetypes : List String
  /-- Each `i` tag: intent identity followed by advertised parameter names. -/
  intents : List (List String)
  deriving Repr

/-- The value of the single `x` tag, if there is exactly one with one value. -/
def xValue? (m : ManifestEvent) : Option Hash :=
  match m.tagsNamed "x" with
  | [⟨_, [v]⟩] => some v
  | _ => none

/-- `d` is exactly one on 35129 and absent otherwise. -/
def dValue? (k : ManifestKind) (m : ManifestEvent) : Except ManifestError (Option String) :=
  match k, m.tagsNamed "d" with
  | .named, [⟨_, [v]⟩] => .ok (some v)
  | .named, _ => .error .dTagCount
  | .snapshot, [] => .ok none
  | .root, [] => .ok none
  | _, _ => .error .dTagCount

/-- `a` / `A` lineage tags are only allowed on snapshots. -/
def lineageOk (k : ManifestKind) (m : ManifestEvent) : Bool :=
  k == .snapshot || ((m.tagsNamed "a").isEmpty && (m.tagsNamed "A").isEmpty)

/-- Runtime verification before the iframe is created (NIP-5D §Identity step 2). -/
def checkManifest (c : Crypto) (m : ManifestEvent) (bytes : Bytes) :
    Except ManifestError VerifiedManifest :=
  if c.verifySig m = false then .error .badSignature else
  match ManifestKind.ofNat? m.kind with
  | none => .error .badKind
  | some k =>
    match xValue? m with
    | none => .error .xTagCount
    | some x =>
      match dValue? k m with
      | .error e => .error e
      | .ok d =>
        if m.content.isEmpty then .error .emptyContent
        else if lineageOk k m = false then .error .lineageOnNonSnapshot
        else if c.sha256 bytes ≠ x then .error .hashMismatch
        else .ok {
          kind := k
          identity := { dTag := d, artifactHash := c.sha256 bytes }
          required := m.firstValues "R"
          optional := m.firstValues "O"
          archetypes := m.firstValues "z"
          intents := (m.tagsNamed "i").map (·.values) }

theorem xValue?_some {m : ManifestEvent} {x : Hash} (h : xValue? m = some x) :
    (m.tagsNamed "x").length = 1 := by
  unfold xValue? at h
  split at h <;> simp_all

/-- Everything a successful verification guarantees. -/
theorem checkManifest_ok {c : Crypto} {m : ManifestEvent} {bytes : Bytes}
    {v : VerifiedManifest} (h : checkManifest c m bytes = .ok v) :
    c.verifySig m = true ∧
    ManifestKind.ofNat? m.kind = some v.kind ∧
    xValue? m = some (c.sha256 bytes) ∧
    v.identity.artifactHash = c.sha256 bytes ∧
    m.content.isEmpty = false ∧
    lineageOk v.kind m = true ∧
    dValue? v.kind m = .ok v.identity.dTag := by
  unfold checkManifest at h
  split at h
  · simp at h
  · rename_i hsig
    split at h
    · simp at h
    · rename_i k hk
      split at h
      · simp at h
      · rename_i x hx
        split at h
        · simp at h
        · rename_i d hd
          split at h
          · simp at h
          · rename_i hc
            split at h
            · simp at h
            · rename_i hl
              split at h
              · simp at h
              · rename_i hh
                simp only [Except.ok.injEq] at h
                subst h
                simp_all

/-- Identity is computed from the bytes the runtime holds (NIP-5D §Identity 1). -/
theorem checkManifest_identity {c : Crypto} {m : ManifestEvent} {bytes : Bytes}
    {v : VerifiedManifest} (h : checkManifest c m bytes = .ok v) :
    v.identity.artifactHash = c.sha256 bytes :=
  (checkManifest_ok h).2.2.2.1

/-- A manifest without exactly one `x` tag is rejected. -/
theorem checkManifest_single_x {c : Crypto} {m : ManifestEvent} {bytes : Bytes}
    {v : VerifiedManifest} (h : checkManifest c m bytes = .ok v) :
    (m.tagsNamed "x").length = 1 :=
  xValue?_some (checkManifest_ok h).2.2.1

/-- Bytes whose hash differs from `x` are rejected. -/
theorem checkManifest_rejects_mismatch {c : Crypto} {m : ManifestEvent} {bytes : Bytes}
    {x : Hash} (hx : xValue? m = some x) (hne : c.sha256 bytes ≠ x) :
    ∀ v, checkManifest c m bytes ≠ .ok v := by
  intro v h
  have := (checkManifest_ok h).2.2.1
  rw [hx] at this
  exact hne (Option.some.inj this).symm

theorem dValue?_named {m : ManifestEvent} {d : Option String}
    (h : dValue? .named m = .ok d) : d.isSome := by
  unfold dValue? at h
  split at h <;> cases h <;> simp_all

theorem dValue?_not_named {k : ManifestKind} {m : ManifestEvent} {d : Option String}
    (hk : k ≠ .named) (h : dValue? k m = .ok d) : d = none := by
  unfold dValue? at h
  split at h <;> simp_all

/-- Named napplets carry a `d`; roots and snapshots do not. -/
theorem checkManifest_dTag {c : Crypto} {m : ManifestEvent} {bytes : Bytes}
    {v : VerifiedManifest} (h : checkManifest c m bytes = .ok v) :
    (v.kind = .named ↔ v.identity.dTag.isSome) := by
  have hd := (checkManifest_ok h).2.2.2.2.2.2
  constructor
  · intro hk
    rw [hk] at hd
    exact dValue?_named hd
  · intro hs
    cases hk : v.kind with
    | named => rfl
    | snapshot =>
      rw [hk] at hd
      rw [dValue?_not_named (by decide) hd] at hs
      simp at hs
    | root =>
      rw [hk] at hd
      rw [dValue?_not_named (by decide) hd] at hs
      simp at hs

end Napplet
