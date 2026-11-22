/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic
import Napplet.Nip19

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

/-- The parts of a manifest event the runtime inspects. `id` is the NIP-01 event id
and `pubkey` the publisher; the host checks both with the signature (`Crypto.verifySig`). -/
structure ManifestEvent where
  kind : Nat
  pubkey : Pubkey
  content : String
  tags : List Tag
  id : String := ""
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

/-! ### Descriptive metadata (NIP-5D §Manifest, §Source, §Presentation media, §Icon)

None of this affects verification or identity. Malformed, repeated or unusable
entries are dropped, never fatal: "Missing or unusable source metadata MUST NOT
prevent playback", unusable screenshots "MUST NOT suppress other usable
screenshots", and a bad icon "MUST fall back to generic artwork". The host still
fetches and hash-checks any blob before rendering it (`Host.fetchBlob`). -/

def isLowerHex (n : Nat) (s : String) : Bool :=
  s.length == n && s.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- `["icon", <sha256>, <mime>]`: PNG, JPEG or WebP only. -/
structure Icon where
  sha256 : Hash
  mime : String
  deriving DecidableEq, Repr

def iconMimes : List String := ["image/png", "image/jpeg", "image/webp"]

/-- A `screenshot` or `preview` blob (NIP-92 `key value` fields). -/
structure MediaBlob where
  sha256 : Hash
  mime : Option String := none
  dim : Option String := none
  size : Option Nat := none
  alt : Option String := none
  duration : Option String := none
  deriving DecidableEq, Repr

/-- `["source-archive", <https-url>, <sha256>, <mime>]`. -/
structure SourceArchive where
  url : String
  sha256 : Hash
  mime : String
  deriving DecidableEq, Repr

structure Metadata where
  title : Option String := none
  icon : Option Icon := none
  screenshots : List MediaBlob := []
  preview : Option MediaBlob := none
  servers : List String := []
  source : Option String := none
  sourceCommit : Option String := none
  sourceArchive : Option SourceArchive := none
  /-- `a` (immediate antecedent) and `A` (root) on snapshots. Provenance only. -/
  parent : Option String := none
  rootAddr : Option String := none
  deriving DecidableEq, Repr

/-- Split a NIP-92 field at the first ASCII space. -/
def splitField (f : String) : String × String :=
  let cs := f.toList
  (String.ofList (cs.takeWhile (· != ' ')), String.ofList ((cs.dropWhile (· != ' ')).drop 1))

def decimalNat? (s : String) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit then some (s.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)
  else none

/-- `dim` is `<width>x<height>` with positive decimal integers. -/
def dimOk (s : String) : Bool :=
  match s.splitOn "x" with
  | [w, h] => (decimalNat? w).any (· > 0) && (decimalNat? h).any (· > 0)
  | _ => false

/-- `duration` is non-negative decimal seconds (`8.5`). -/
def durationOk (s : String) : Bool :=
  match s.splitOn "." with
  | [a] => (decimalNat? a).isSome
  | [a, b] => (decimalNat? a).isSome && (decimalNat? b).isSome
  | _ => false

/-- The single value of field `k`, if present exactly once and valid. Absent,
malformed or repeated optional fields are ignored. -/
def oneField (fs : List (String × String)) (k : String) (ok : String → Bool) : Option String :=
  match fs.filter (·.1 == k) with
  | [(_, v)] => if ok v then some v else none
  | _ => none

def parseMediaBlob (allowDuration : Bool) (values : List String) : Option MediaBlob :=
  let fs := values.map splitField
  match fs.filter (·.1 == "x") with
  | [(_, x)] =>
    if isLowerHex 64 x then
      some { sha256 := x
             mime := oneField fs "m" (fun v => !v.isEmpty)
             dim := oneField fs "dim" dimOk
             size := (oneField fs "size" (fun v => (decimalNat? v).isSome)).bind decimalNat?
             alt := oneField fs "alt" (fun _ => true)
             duration := if allowDuration then oneField fs "duration" durationOk else none }
    else none
  | _ => none

/-- Absolute URL with one of the given schemes and a non-empty rest. -/
def urlWithScheme (schemes : List String) (u : String) : Bool :=
  match u.splitOn ":" with
  | sch :: rest => schemes.contains sch && !(":".intercalate rest).isEmpty
  | [] => false

/-- Git scp-like SSH location `[user@]host:path` (no scheme, no `//`). -/
def scpLike (u : String) : Bool :=
  match u.splitOn ":" with
  | [hostPart, path] =>
    !hostPart.isEmpty && !path.isEmpty && !path.startsWith "//" && !hostPart.contains '/'
  | _ => false

/-- A NIP-34 `nostr` clone location (`nostr:` or `nostr://` followed by a non-empty
rest). NIP-5D: "A `nostr` location MUST identify a kind-30617 repository announcement":
a rest that decodes as an `naddr` must carry kind 30617, else the location is
unusable (and the `source` field is dropped); other NIP-34 forms
(`<npub>/<identifier>`, with or without relay hint) are kept as given. -/
def nostrSourceOk (u : String) : Bool :=
  let rest := if u.startsWith "nostr://" then (u.drop 8).toString else (u.drop 6).toString
  !rest.isEmpty &&
    match Nip19.decodeNaddr rest with
    | some a => a.kind == 30617
    | none => true

def sourceOk (u : String) : Bool :=
  if u.startsWith "nostr:" then nostrSourceOk u
  else urlWithScheme ["http", "https", "ssh", "git"] u || scpLike u

-- `nostr` sources: an `naddr` must name a kind-30617 repository announcement
#guard sourceOk ("nostr://" ++ Nip19.encodeNaddr { Nip19.sample with kind := 30617 } Nip19.author)
#guard sourceOk ("nostr:" ++ Nip19.encodeNaddr { Nip19.sample with kind := 30617 } Nip19.author)
#guard !sourceOk ("nostr://" ++ Nip19.encodeNaddr Nip19.sample Nip19.author)
#guard !sourceOk ("nostr:" ++ Nip19.encodeNaddr { Nip19.sample with kind := 1 } Nip19.author)
#guard sourceOk "nostr://npub1abc/my-repo"
#guard !sourceOk "nostr:" && !sourceOk "nostr://"
#guard sourceOk "https://example.com/repo.git" && sourceOk "git@example.com:repo.git"

/-- `https:` URL without credentials or fragment. -/
def archiveUrlOk (u : String) : Bool :=
  u.startsWith "https://" && !u.contains '#' &&
    !((u.drop 8).toString.takeWhile (· != '/')).toString.contains '@'

/-- Value of a tag that must appear at most once with exactly `n` values. -/
def uniqueTag (m : ManifestEvent) (name : String) (n : Nat) : Option (List String) :=
  match m.tagsNamed name with
  | [t] => if t.values.length = n then some t.values else none
  | _ => none

def parseMetadata (k : ManifestKind) (m : ManifestEvent) : Metadata :=
  let source := (uniqueTag m "source" 1).bind fun vs => vs.head?.filter sourceOk
  { title := (uniqueTag m "title" 1).bind (·.head?)
    icon := (uniqueTag m "icon" 2).bind fun vs =>
      match vs with
      | [h, mime] => if isLowerHex 64 h && iconMimes.contains mime then some ⟨h, mime⟩ else none
      | _ => none
    screenshots := (m.tagsNamed "screenshot").filterMap (parseMediaBlob false ·.values)
    preview := match m.tagsNamed "preview" with
      | [t] => parseMediaBlob true t.values
      | _ => none
    servers := m.firstValues "server"
    source
    sourceCommit := if source.isSome then
        (uniqueTag m "source-commit" 1).bind fun vs =>
          vs.head?.filter fun c => isLowerHex 40 c || isLowerHex 64 c
      else none
    sourceArchive := (uniqueTag m "source-archive" 3).bind fun vs =>
      match vs with
      | [u, h, mime] =>
        if archiveUrlOk u && isLowerHex 64 h && !mime.isEmpty then some ⟨u, h, mime⟩ else none
      | _ => none
    parent := if k = .snapshot then (uniqueTag m "a" 1).bind (·.head?) else none
    rootAddr := if k = .snapshot then (uniqueTag m "A" 1).bind (·.head?) else none }

/-- A manifest that passed `checkManifest` against specific bytes. -/
structure VerifiedManifest where
  kind : ManifestKind
  identity : Identity
  required : List String
  optional : List String
  archetypes : List String
  /-- Each `i` tag: intent identity followed by advertised parameter names. -/
  intents : List (List String)
  /-- Plain-text description (event `content`). -/
  content : String := ""
  metadata : Metadata := {}
  deriving Repr

/-- The value of the single `x` tag, if there is exactly one with one value. -/
def xValue? (m : ManifestEvent) : Option Hash :=
  match m.tagsNamed "x" with
  | [⟨_, [v]⟩] => some v
  | _ => none

/-- `d` is exactly one on 35129 and absent otherwise. -/
def dValue? (k : ManifestKind) (m : ManifestEvent) : Except ManifestError (Option String) :=
  match k, m.tagsNamed "d" with
  | .named, [⟨_, [v]⟩] => if v = "" then .error .dTagCount else .ok (some v)
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
          identity := { dTag := d, artifactHash := c.sha256 bytes, publisher := m.pubkey,
                        kind := k, eventId := m.id }
          content := m.content
          metadata := parseMetadata k m
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
    dValue? v.kind m = .ok v.identity.dTag ∧
    v.identity.publisher = m.pubkey ∧ v.identity.eventId = m.id ∧ v.identity.kind = v.kind := by
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

/-- The publisher, event id and kind in the bound identity are the signed event's
own fields (the manifest key is derived from them by `Identity.key`). -/
theorem checkManifest_principal {c : Crypto} {m : ManifestEvent} {bytes : Bytes}
    {v : VerifiedManifest} (h : checkManifest c m bytes = .ok v) :
    c.verifySig m = true ∧ v.identity.publisher = m.pubkey ∧ v.identity.eventId = m.id ∧
    v.identity.kind = v.kind :=
  ⟨(checkManifest_ok h).1, (checkManifest_ok h).2.2.2.2.2.2.2⟩

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
  split at h
  · split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; rw [← h]; rfl
  all_goals simp_all

theorem dValue?_not_named {k : ManifestKind} {m : ManifestEvent} {d : Option String}
    (hk : k ≠ .named) (h : dValue? k m = .ok d) : d = none := by
  unfold dValue? at h
  split at h <;> simp_all

/-- Named napplets carry a `d`; roots and snapshots do not. -/
theorem checkManifest_dTag {c : Crypto} {m : ManifestEvent} {bytes : Bytes}
    {v : VerifiedManifest} (h : checkManifest c m bytes = .ok v) :
    (v.kind = .named ↔ v.identity.dTag.isSome) := by
  have hd := (checkManifest_ok h).2.2.2.2.2.2.1
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
