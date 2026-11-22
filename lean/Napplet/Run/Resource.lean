/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Resource

/-!
# NAP-RESOURCE runtime component

Upstream: `napplet/naps` PR #80, `naps/NAP-RESOURCE.md` at `ae5b9c64`.

Wire (napplet → runtime): `resource.info {id}`, `resource.bytes {id, url}`,
`resource.bytesMany {id, urls}`, `resource.cancel {id}`.
Wire (runtime → napplet): `resource.info.result {id, info}`,
`resource.bytes.result {id, blob, mime}`, `resource.bytesMany.result {id, items}`,
and `resource.{info,bytes,bytesMany}.error {id, error, message?}`. `blob` is
canonical padded RFC 4648 §4 base64 text (`Base64`), never a byte array.

Per URL (`bytes`, and each `bytesMany` item independently):
1. A bare `nhash1…` is the alias of `hashtree:nhash1…` (`norm`).
2. Pre-checks without network (`precheck`): unknown scheme or a scheme the
   policy disables → `unsupported-scheme` (`http:` is off by default);
   malformed `blossom:` (BUD-10 `blossom:<64 lowercase hex>.<ext>`), `nostr:`
   (NIP-21 / NIP-19 bech32 with checksum, `npub`/`nprofile`/`note`/`nevent`/`naddr`;
   never `nsec`), `hashtree:` (bech32 `nhash` with checksum, no query, fragment or
   path) or `htree://` (identifier `npub…` or 64-hex, then a non-empty tree segment
   and optional entry segments, every segment non-empty with valid `%XX` escapes
   and no `:`, no query, fragment only `#k=<64 hex>` or `#private`; so
   `#link-visible` is refused) → `invalid-request`.
3. `data:` URLs are decoded here (RFC 2397: `data:[<mediatype>][;base64],<data>`,
   `%XX` escapes decoded first, base64 strictly canonical) and never touch the
   network; a malformed one is `invalid-request`.
4. Everything else is one host fetch (`Call.fetch`), at most `Cfg.maxInFlight`
   per endpoint at a time (bulk counts per URL); the rest wait in order.
5. The outcome goes through `NapResource.bytes` (hop, redirect, size, Blossom hash,
   sniffing and rasterisation policy), exactly as for a single URL, so a
   `bytesMany` item is processed as an independent `bytes(url)`.
6. The sniffed MIME type must be on the URL scheme's allowlist (`Cfg.mimeAllowed`,
   default `defaultMimeAllowed`, upstream "Enforce scheme-appropriate allowlists");
   otherwise the item is `blocked-by-policy`. The default compares the type's essence
   (before `;`, ASCII-lowercased) against: for `nostr:` (a NIP-19 hop yields event
   JSON) `application/json`, `text/plain`; for every other scheme the images
   `image/png`, `image/jpeg`, `image/gif`, `image/webp`, `image/avif`, `image/bmp`,
   `image/x-icon` (rasterised SVG arrives as PNG/WebP), the audio/video types WHATWG
   sniffing produces (`audio/mpeg`, `audio/wave`, `audio/aiff`, `audio/basic`,
   `audio/midi`, `audio/ogg`, `audio/flac`, `audio/mp4`, `audio/webm`,
   `application/ogg`, `video/mp4`, `video/webm`, `video/ogg`, `video/avi`), and
   `application/octet-stream`, `text/plain`, `application/json`, `application/pdf`.
   Never allowed by default: `text/html`, XML, scripts, CSS, fonts, `image/svg+xml`
   (already refused raw), archives.
7. Decoded bytes delivered in one envelope count against `Cfg.quota`; an item
   that would exceed it is `quota-exceeded`.

A request with an `id` that is already in flight on the endpoint is ignored.
`resource.cancel` withdraws the request's outstanding host calls and drops the
request, so no terminal envelope follows. Teardown does the same for every request
of the endpoint.

Malformed requests: no string `id` → nothing; `bytes` without a string `url`, or
`bytesMany` without an array of strings → that operation's `.error` envelope with
`invalid-request`. An empty `urls` is `resource.bytesMany.error` `invalid-request`;
more than `maxUrls` is `too-large`. `bytes` `opts` (API surface only, no wire
field) is ignored.

## Host operations

* `Call.fetch url` → `Reply.fetched o` (`NapResource.FetchOutcome`), or
  `Reply.json {error, message?}` for failures `FetchOutcome` cannot express.
  `url` is a napplet URL after the `nhash` alias rewrite; `data:` is never sent.
  Contract (in addition to `Call.fetch` in `Napplet.Host`): resolve `https:` with
  DNS; `blossom:` per BUD-10 from servers the host chooses, treating `xs`/`as`/`sz`
  hints as advisory and fetching upstream hosts under `https:` policy; `nostr:` by
  one NIP-19 hop, never following URLs or `nostr:` references in the result;
  `hashtree:`/`htree:` per HTS-01 (§6.2–6.3 `nhash` TLV fields, §9 `htree` URL
  profile, URL-ENCODING segment rules), verifying the root, nodes, chunks and CHK
  decryption, and never sending `#k=` secrets or keys to relays, storage servers,
  FIPS peers or HTTP bodies. Report every address connected to in `o.hops`, in
  order (private-address checks happen after DNS and before connecting, so the
  host MUST refuse to connect to an address `NapResource.isPrivate` classifies as
  private and report it as a hop); stop after `Cfg.pol.maxRedirects` redirects;
  set `o.timedOut` after `Cfg.timeoutSecs` (recommended 30 s) per URL; `o.body`
  is the complete response body or `none` when the resource does not exist.
  `o.upstreamType` is never used. `Reply.json` `error` is one of the NAP-RESOURCE
  codes: `network-error` (DNS, TCP, TLS or upstream failure), `invalid-request`
  (an `nhash` whose TLV fields are invalid, an unresolvable `self`/petname, or a
  Hashtree directory), `decode-failed` (Hashtree hash or key mismatch),
  `blocked-by-policy`, `not-found`, `timeout`, `too-large`; `message` is
  diagnostic text passed to the napplet. Any other reply is `network-error`.
* `Effect.cancel tag`: abandon a fetch whose request was cancelled or whose
  endpoint was torn down.
* Pure host functions used: `Host.crypto.sha256` (Blossom hash check),
  `Host.sniff` (MIME, WHATWG MIME Sniffing over the bytes only), `Host.rasterize`
  (SVG to PNG/WebP in an isolated, network-less context within 5 MiB input,
  4096 × 4096 output and 2 s).
-/

namespace Napplet.Run.Resource

open NapResource

/-! ## RFC 4648 §4 base64 (canonical, padded) -/

namespace Base64

def ch (k : Nat) : Char :=
  if k < 26 then Char.ofNat (65 + k)
  else if k < 52 then Char.ofNat (97 + (k - 26))
  else if k < 62 then Char.ofNat (48 + (k - 52))
  else if k = 62 then '+' else '/'

def valN (n : Nat) : Option Nat :=
  if 65 ≤ n ∧ n ≤ 90 then some (n - 65)
  else if 97 ≤ n ∧ n ≤ 122 then some (n - 71)
  else if 48 ≤ n ∧ n ≤ 57 then some (n + 4)
  else if n = 43 then some 62
  else if n = 47 then some 63
  else none

def val (c : Char) : Option Nat := valN c.toNat

def chN (k : Nat) : Nat :=
  if k < 26 then 65 + k else if k < 52 then 71 + k else if k < 62 then k - 4
  else if k = 62 then 43 else 47

theorem ch_toNat_fin : ∀ k : Fin 64, (ch k.val).toNat = chN k.val := by decide
theorem val_ch_fin : ∀ k : Fin 64, val (ch k.val) = some k.val := by decide
theorem val_ch {k : Nat} (h : k < 64) : val (ch k) = some k := val_ch_fin ⟨k, h⟩
theorem ch_ne_pad_fin : ∀ k : Fin 64, ch k.val ≠ '=' := by decide
theorem ch_ne_pad {k : Nat} (h : k < 64) : ch k ≠ '=' := ch_ne_pad_fin ⟨k, h⟩

/-- Encode: each 3 bytes become 4 characters; a final 1 or 2 bytes are padded. -/
def enc : Bytes → List Char
  | a :: b :: c :: rest =>
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    ch (n / 262144) :: ch (n / 4096 % 64) :: ch (n / 64 % 64) :: ch (n % 64) :: enc rest
  | [a, b] =>
    let n := a.toNat * 65536 + b.toNat * 256
    [ch (n / 262144), ch (n / 4096 % 64), ch (n / 64 % 64), '=']
  | [a] =>
    let n := a.toNat * 65536
    [ch (n / 262144), ch (n / 4096 % 64), '=', '=']
  | [] => []

def group (c1 c2 c3 c4 : Char) : Option Bytes := do
  let v1 ← val c1; let v2 ← val c2; let v3 ← val c3; let v4 ← val c4
  some [UInt8.ofNat (v1 * 4 + v2 / 16), UInt8.ofNat (v2 % 16 * 16 + v3 / 4), UInt8.ofNat (v3 % 4 * 64 + v4)]

/-- The last quantum: `xx==` (pad bits must be zero), `xxx=` (likewise), or full. -/
def lastGroup (c1 c2 c3 c4 : Char) : Option Bytes :=
  if c3 = '=' ∧ c4 = '=' then do
    let v1 ← val c1; let v2 ← val c2
    if v2 % 16 = 0 then some [UInt8.ofNat (v1 * 4 + v2 / 16)] else none
  else if c4 = '=' then do
    let v1 ← val c1; let v2 ← val c2; let v3 ← val c3
    if v3 % 4 = 0 then some [UInt8.ofNat (v1 * 4 + v2 / 16), UInt8.ofNat (v2 % 16 * 16 + v3 / 4)] else none
  else group c1 c2 c3 c4

/-- Strict decode: standard alphabet, length a multiple of 4, `=` only as final
padding, zero pad bits, no whitespace. -/
def dec : List Char → Option Bytes
  | [] => some []
  | c1 :: c2 :: c3 :: c4 :: rest =>
    match rest with
    | [] => lastGroup c1 c2 c3 c4
    | _ :: _ => do let g ← group c1 c2 c3 c4; let r ← dec rest; some (g ++ r)
  | _ => none

def encode (bs : Bytes) : String := String.ofList (enc bs)
def decode? (s : String) : Option Bytes := dec s.toList

theorem enc_eq_nil {bs : Bytes} : enc bs = [] ↔ bs = [] := by
  constructor
  · intro h; cases bs using enc.induct <;> simp_all [enc]
  · rintro rfl; rfl

theorem group_enc (a b c : UInt8) :
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    group (ch (n / 262144)) (ch (n / 4096 % 64)) (ch (n / 64 % 64)) (ch (n % 64)) = some [a, b, c] := by
  intro n
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt
  have h1 : n / 262144 < 64 := by omega
  simp only [group, val_ch h1, val_ch (Nat.mod_lt _ (by decide : 64 > 0)), Option.bind_eq_bind,
    Option.bind_some, Option.some.injEq, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> (apply UInt8.toNat_inj.mp; simp; omega)

theorem dec_enc (bs : Bytes) : dec (enc bs) = some bs := by
  induction bs using enc.induct with
  | case1 a b c rest ih =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt
    simp only [enc]
    cases hr : enc rest with
    | nil =>
      have := enc_eq_nil.mp hr; subst this
      simp only [dec, lastGroup, ch_ne_pad (Nat.mod_lt _ (by decide : 64 > 0)), and_false, ite_false]
      exact group_enc a b c
    | cons x xs =>
      rw [hr] at ih
      simp only [dec, group_enc, ih, Option.bind_eq_bind, Option.bind_some]
      rfl
  | case2 a b =>
    have ha := a.toNat_lt; have hb := b.toNat_lt
    have h1 : (a.toNat * 65536 + b.toNat * 256) / 262144 < 64 := by omega
    simp only [enc, dec, lastGroup, ch_ne_pad (Nat.mod_lt _ (by decide : 64 > 0)), false_and,
      ite_false, ite_true, val_ch h1, val_ch (Nat.mod_lt _ (by decide : 64 > 0)), Option.bind_eq_bind,
      Option.bind_some]
    rw [if_pos (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;> (apply UInt8.toNat_inj.mp; simp; omega)
  | case3 a =>
    have ha := a.toNat_lt
    have h1 : (a.toNat * 65536) / 262144 < 64 := by omega
    simp only [enc, dec, lastGroup, and_self, ite_true, val_ch h1,
      val_ch (Nat.mod_lt _ (by decide : 64 > 0)), Option.bind_eq_bind, Option.bind_some]
    rw [if_pos (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    apply UInt8.toNat_inj.mp; simp; omega
  | case4 => rfl

theorem valN_some {n k : Nat} (h : valN n = some k) : k < 64 ∧ chN k = n := by
  unfold valN at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    refine ⟨by omega, ?_⟩; unfold chN; repeat' split
    all_goals omega
  · split at h
    · simp only [Option.some.injEq] at h; subst h
      refine ⟨by omega, ?_⟩; unfold chN; repeat' split
      all_goals omega
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        refine ⟨by omega, ?_⟩; unfold chN; repeat' split
        all_goals omega
      · split at h
        · simp only [Option.some.injEq] at h; subst h
          refine ⟨by omega, ?_⟩; unfold chN; repeat' split
          all_goals omega
        · split at h
          · simp only [Option.some.injEq] at h; subst h
            refine ⟨by omega, ?_⟩; unfold chN; repeat' split
            all_goals omega
          · cases h

theorem val_lt {c : Char} {k : Nat} (h : val c = some k) : k < 64 := (valN_some h).1

theorem ch_val {c : Char} {k : Nat} (h : val c = some k) : ch k = c := by
  have ⟨hk, hn⟩ := valN_some h
  rw [← Char.ofNat_toNat (ch k), ← Char.ofNat_toNat c, ch_toNat_fin ⟨k, hk⟩]
  rw [hn]

theorem toNat_ofNat_lt {x : Nat} (h : x < 256) : (UInt8.ofNat x).toNat = x := by
  simp; omega

theorem group_canon {c1 c2 c3 c4 : Char} {bs : Bytes} (h : group c1 c2 c3 c4 = some bs) :
    enc bs = [c1, c2, c3, c4] := by
  simp only [group, Option.bind_eq_bind] at h
  cases h1 : val c1 <;> simp only [h1, Option.bind_none, Option.bind_some, reduceCtorEq] at h
  cases h2 : val c2 <;> simp only [h2, Option.bind_none, Option.bind_some, reduceCtorEq] at h
  cases h3 : val c3 <;> simp only [h3, Option.bind_none, Option.bind_some, reduceCtorEq] at h
  cases h4 : val c4 <;> simp only [h4, Option.bind_none, Option.bind_some, reduceCtorEq] at h
  rename_i v1 v2 v3 v4
  simp only [Option.some.injEq] at h
  subst h
  have l1 := val_lt h1; have l2 := val_lt h2; have l3 := val_lt h3; have l4 := val_lt h4
  simp only [enc, toNat_ofNat_lt (show v1 * 4 + v2 / 16 < 256 by omega),
    toNat_ofNat_lt (show v2 % 16 * 16 + v3 / 4 < 256 by omega),
    toNat_ofNat_lt (show v3 % 4 * 64 + v4 < 256 by omega), List.cons.injEq, and_true]
  rw [← ch_val h1, ← ch_val h2, ← ch_val h3, ← ch_val h4]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> congr 1 <;> omega

theorem lastGroup_canon {c1 c2 c3 c4 : Char} {bs : Bytes} (h : lastGroup c1 c2 c3 c4 = some bs) :
    enc bs = [c1, c2, c3, c4] := by
  unfold lastGroup at h
  split at h
  · rename_i hp
    obtain ⟨rfl, rfl⟩ := hp
    simp only [Option.bind_eq_bind] at h
    cases h1 : val c1 <;> simp only [h1, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    cases h2 : val c2 <;> simp only [h2, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    rename_i v1 v2
    split at h
    case isFalse => cases h
    simp only [Option.some.injEq] at h
    subst h
    have l1 := val_lt h1; have l2 := val_lt h2
    simp only [enc, toNat_ofNat_lt (show v1 * 4 + v2 / 16 < 256 by omega), List.cons.injEq, and_true]
    rw [← ch_val h1, ← ch_val h2]
    refine ⟨?_, ?_⟩ <;> congr 1 <;> omega
  · split at h
    · rename_i hp hc4
      subst hc4
      simp only [Option.bind_eq_bind] at h
      cases h1 : val c1 <;> simp only [h1, Option.bind_none, Option.bind_some, reduceCtorEq] at h
      cases h2 : val c2 <;> simp only [h2, Option.bind_none, Option.bind_some, reduceCtorEq] at h
      cases h3 : val c3 <;> simp only [h3, Option.bind_none, Option.bind_some, reduceCtorEq] at h
      rename_i v1 v2 v3
      split at h
      case isFalse => cases h
      simp only [Option.some.injEq] at h
      subst h
      have l1 := val_lt h1; have l2 := val_lt h2; have l3 := val_lt h3
      simp only [enc, toNat_ofNat_lt (show v1 * 4 + v2 / 16 < 256 by omega),
        toNat_ofNat_lt (show v2 % 16 * 16 + v3 / 4 < 256 by omega), List.cons.injEq, and_true]
      rw [← ch_val h1, ← ch_val h2, ← ch_val h3]
      refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> omega
    · exact group_canon h

theorem enc_dec {cs : List Char} {bs : Bytes} (h : dec cs = some bs) : enc bs = cs := by
  induction cs using dec.induct generalizing bs with
  | case1 => simp [dec] at h; subst h; rfl
  | case2 c1 c2 c3 c4 => simp only [dec] at h; exact lastGroup_canon h
  | case3 c1 c2 c3 c4 x xs ih =>
    simp only [dec, Option.bind_eq_bind] at h
    cases hg : group c1 c2 c3 c4 <;> simp [hg] at h
    cases hr : dec (x :: xs) <;> simp [hr] at h
    rename_i g r
    subst h
    have hc := group_canon hg
    have ihr := ih hr
    simp only [group, Option.bind_eq_bind] at hg
    cases h1 : val c1 <;> simp only [h1, Option.bind_none, Option.bind_some, reduceCtorEq] at hg
    cases h2 : val c2 <;> simp only [h2, Option.bind_none, Option.bind_some, reduceCtorEq] at hg
    cases h3 : val c3 <;> simp only [h3, Option.bind_none, Option.bind_some, reduceCtorEq] at hg
    cases h4 : val c4 <;> simp only [h4, Option.bind_none, Option.bind_some, reduceCtorEq] at hg
    simp only [Option.some.injEq] at hg
    subst hg
    simp only [enc] at hc ⊢
    simp only [List.nil_append, List.cons_append, List.cons.injEq, and_true] at hc ⊢
    obtain ⟨e1, e2, e3, e4⟩ := hc
    rw [enc.eq_1]; simp only [ihr, e1, e2, e3, e4]
  | case4 => simp [dec] at h

/-- Round trip: decoding an encoding gives the bytes back. -/
theorem decode?_encode (bs : Bytes) : decode? (encode bs) = some bs := by
  simp [decode?, encode, String.toList_ofList, dec_enc]

/-- Canonicity: the only text that decodes to `bs` is `encode bs`, so every
non-canonical encoding (missing padding, non-zero pad bits, whitespace, other
alphabets) is rejected. -/
theorem encode_decode? {s : String} {bs : Bytes} (h : decode? s = some bs) : encode bs = s := by
  simp only [decode?] at h
  simp only [encode, enc_dec h, String.ofList_toList]

#guard encode [0x00, 0x01, 0x02, 0xff] == "AAEC/w=="
#guard encode [] == ""
#guard encode "f".toUTF8.toList == "Zg==" && encode "fo".toUTF8.toList == "Zm8="
#guard encode "foobar".toUTF8.toList == "Zm9vYmFy"
#guard decode? "AAEC/w==" == some [0x00, 0x01, 0x02, 0xff]
#guard decode? "Zh==" == none   -- non-zero pad bits
#guard decode? "Zg" == none     -- missing padding
#guard decode? "Zg==\n" == none -- whitespace
#guard decode? "Z-==" == none   -- URL-safe alphabet

end Base64

/-! ## BIP-173 bech32 (NIP-19 and HTS-01 `nhash` checksums) -/

namespace Bech32

def charset : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList

def idx : List Char → Char → Nat → Option Nat
  | [], _, _ => none
  | c :: cs, x, i => if c = x then some i else idx cs x (i + 1)

def cval (c : Char) : Option Nat := idx charset c 0

def gens : List (Nat × Nat) :=
  [(0x3b6a57b2, 0), (0x26508e6d, 1), (0x1ea119fa, 2), (0x3d4233dd, 3), (0x2a1462b3, 4)]

def step (chk v : Nat) : Nat :=
  let b := chk / 2 ^ 25
  gens.foldl (fun c (g, i) => if b / 2 ^ i % 2 = 1 then c ^^^ g else c) (((chk % 2 ^ 25) * 32) ^^^ v)

def polymod (vs : List Nat) : Nat := vs.foldl step 1

def hrpExpand (hrp : List Char) : List Nat := hrp.map (·.toNat / 32) ++ [0] ++ hrp.map (·.toNat % 32)

/-- The human-readable part of a lowercase bech32 string with a valid checksum.
(No 90-character limit: NIP-19 TLV strings exceed it.) -/
def hrp? (s : String) : Option String :=
  let r := s.toList.reverse
  let dataRev := r.takeWhile (· != '1')
  if dataRev.length = r.length then none else
  let hrp := (r.drop (dataRev.length + 1)).reverse
  let data := dataRev.reverse
  if hrp.isEmpty || data.length < 6 then none else
  if hrp.any (fun c => c.toNat < 33 || c.toNat > 126 || c.isUpper) then none else
  match data.mapM cval with
  | none => none
  | some vs => if polymod (hrpExpand hrp ++ vs) = 1 then some (String.ofList hrp) else none

#guard hrp? "a12uel5l" == some "a"
#guard hrp? "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw" == some "abcdef"
#guard hrp? "npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjptg" == some "npub"
#guard hrp? "npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjpth" == none

end Bech32

/-! ## URL forms -/

def isHex (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
def isLowerHex (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')
def hex64 (cs : List Char) : Bool := cs.length == 64 && cs.all isLowerHex

def hexNib (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else c.toNat - 55

/-- Percent-decode to bytes: `%XX` is one byte, any other character its UTF-8
encoding. Malformed escapes are `none`. -/
def pctDecode : List Char → Option Bytes
  | [] => some []
  | '%' :: a :: b :: rest =>
    if isHex a && isHex b then (pctDecode rest).map (UInt8.ofNat (hexNib a * 16 + hexNib b) :: ·)
    else none
  | '%' :: _ => none
  | c :: rest => (pctDecode rest).map (String.utf8EncodeChar c ++ ·)

def escapesOk (cs : List Char) : Bool := (pctDecode cs).isSome

def splitOn (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitOn sep cs
    else match splitOn sep cs with
      | s :: ss => (c :: s) :: ss
      | [] => [[c]]

/-- `data:[<mediatype>][;base64],<data>` → the decoded bytes (RFC 2397). The
media type is ignored: MIME comes from sniffing. -/
def dataBytes? (url : String) : Option Bytes :=
  let cs := url.toList.drop 5
  let header := cs.takeWhile (· != ',')
  if header.length = cs.length then none else
  let body := cs.drop (header.length + 1)
  let isB64 := (header.map Char.toLower).reverse.take 7 == ";base64".toList.reverse
  match pctDecode body with
  | none => none
  | some raw => if isB64 then Base64.dec (raw.map fun b => Char.ofNat b.toNat) else some raw

/-- `hashtree:<nhash>`: a bech32 `nhash` with a valid checksum and nothing else. -/
def hashtreeOk (url : String) : Bool :=
  let rest := url.toList.drop 9
  !(rest.contains '?') && !(rest.contains '#') && !(rest.contains '/') &&
    Bech32.hrp? (String.ofList rest) == some "nhash"

def htreeFragOk (frag : List Char) : Bool :=
  frag == "private".toList || (frag.take 2 == "k=".toList && hex64 (frag.drop 2))

def htreeIdOk (ident : List Char) : Bool :=
  hex64 ident || Bech32.hrp? (String.ofList ident) == some "npub"

/-- `htree://<identifier>/<tree>[/<entry-path>][#k=<secret>]` (HTS-01 §9). -/
def htreeOk (url : String) : Bool :=
  let cs := url.toList
  if cs.take 8 != "htree://".toList then false else
  let rest := cs.drop 8
  let path := rest.takeWhile (· != '#')
  let fragOk := if path.length = rest.length then true else htreeFragOk (rest.drop (path.length + 1))
  fragOk && !(path.contains '?') && !(path.contains ':') &&
  match splitOn '/' path with
  | ident :: tree :: entries =>
    htreeIdOk ident && (tree :: entries).all fun seg => !seg.isEmpty && escapesOk seg
  | _ => false

def nostrOk (url : String) : Bool :=
  match Bech32.hrp? (String.ofList (url.toList.drop 6)) with
  | some h => ["npub", "nprofile", "note", "nevent", "naddr"].contains h
  | none => false

def blossomOk (url : String) : Bool :=
  match blossomHash? url with
  | some h => hex64 h.toList
  | none => false

/-- The bare `nhash` alias. -/
def norm (url : String) : String :=
  if url.startsWith "nhash1" then "hashtree:" ++ url else url

/-- Pre-checks that need no network; `none` means fetch. -/
def precheck (pol : Policy) (url : String) : Option ResErr :=
  match schemeOf url with
  | none => some .unsupportedScheme
  | some s =>
    if schemeAllowed pol s = false then some .unsupportedScheme
    else match s with
      | .blossom => if blossomOk url then none else some .invalidRequest
      | .hashtree => if hashtreeOk url then none else some .invalidRequest
      | .htree => if htreeOk url then none else some .invalidRequest
      | .nostr => if nostrOk url then none else some .invalidRequest
      | .data => if (dataBytes? url).isSome then none else some .invalidRequest
      | _ => none

/-! ## Errors and outcomes -/

def errName : ResErr → String
  | .invalidRequest => "invalid-request" | .notFound => "not-found"
  | .blockedByPolicy => "blocked-by-policy" | .timeout => "timeout" | .tooLarge => "too-large"
  | .unsupportedScheme => "unsupported-scheme" | .decodeFailed => "decode-failed"
  | .networkError => "network-error" | .quotaExceeded => "quota-exceeded"

def errOf? : String → Option ResErr
  | "invalid-request" => some .invalidRequest | "not-found" => some .notFound
  | "blocked-by-policy" => some .blockedByPolicy | "timeout" => some .timeout
  | "too-large" => some .tooLarge | "unsupported-scheme" => some .unsupportedScheme
  | "decode-failed" => some .decodeFailed | "network-error" => some .networkError
  | "quota-exceeded" => some .quotaExceeded
  | _ => none

/-- What resolving one URL produced: a fetch outcome (from the host, or local for
`data:`), or a failure with an optional diagnostic message. This extends
`NapResource.FetchOutcome`, which cannot express a network error. -/
inductive Outcome where
  | fetched (o : FetchOutcome)
  | failed (e : ResErr) (message : Option String)

def outcomeOf : Reply → Outcome
  | .fetched o => .fetched o
  | .json j =>
    match (j.getStr? "error").bind errOf? with
    | some e => .failed e (j.getStr? "message")
    | none => .failed .networkError none
  | _ => .failed .networkError none

/-- The policy environment for one outcome: the host's pure functions, and a fetch
that returns exactly what the host reported. -/
def envOf (h : Host) (o : FetchOutcome) : Env :=
  { fetch := fun _ => o, sha256 := h.crypto.sha256, sniff := h.sniff, rasterize := h.rasterize }

abbrev Item := Except (ResErr × Option String) Delivered

/-- One URL's result: `NapResource.bytes` over its outcome. -/
def itemOf (h : Host) (pol : Policy) (url : String) : Outcome → Item
  | .failed e m => .error (e, m)
  | .fetched o =>
    match NapResource.bytes (envOf h o) pol (norm url) with
    | .ok d => .ok d
    | .error e => .error (e, none)

/-! ## MIME allowlist -/

/-- MIME essence: the part before `;`, without surrounding spaces, ASCII-lowercased. -/
def mimeEssence (m : String) : String :=
  let cs := (m.toList.takeWhile (· ≠ ';')).dropWhile (· = ' ')
  let cs := (cs.reverse.dropWhile (· = ' ')).reverse
  String.ofList (cs.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c)

def mediaMimes : List String :=
  ["image/png", "image/jpeg", "image/gif", "image/webp", "image/avif", "image/bmp", "image/x-icon",
   "audio/mpeg", "audio/wave", "audio/aiff", "audio/basic", "audio/midi", "audio/ogg", "audio/flac",
   "audio/mp4", "audio/webm", "application/ogg",
   "video/mp4", "video/webm", "video/ogg", "video/avi",
   "application/octet-stream", "text/plain", "application/json", "application/pdf"]

/-- Default scheme-appropriate MIME allowlist (see the module docstring, step 6). -/
def defaultMimeAllowed : Scheme → String → Bool
  | .nostr, m => ["application/json", "text/plain"].contains (mimeEssence m)
  | _, m => mediaMimes.contains (mimeEssence m)

/-- Apply the MIME allowlist of the URL's scheme to a delivered item. -/
def gateMime (mimeOk : Scheme → String → Bool) (url : String) : Item → Item
  | .ok d =>
    match schemeOf (norm url) with
    | some sc => if mimeOk sc d.mime then .ok d else .error (.blockedByPolicy, none)
    | none => .error (.blockedByPolicy, none)
  | .error e => .error e

theorem gateMime_ok {mimeOk : Scheme → String → Bool} {url : String} {it : Item} {d : Delivered}
    (h : gateMime mimeOk url it = .ok d) :
    it = .ok d ∧ ∃ sc, schemeOf (norm url) = some sc ∧ mimeOk sc d.mime = true := by
  cases it with
  | error e => simp [gateMime] at h
  | ok d' =>
    simp only [gateMime] at h
    split at h
    · rename_i sc hsc
      split at h
      · rename_i hm
        cases h
        exact ⟨rfl, sc, hsc, hm⟩
      · cases h
    · cases h

/-- Decoded bytes in one envelope count against the quota, in order. -/
def applyQuota (quota : Nat) : Nat → List Item → List Item
  | _, [] => []
  | used, .ok d :: rest =>
    if used + d.blob.length > quota then .error (.quotaExceeded, none) :: applyQuota quota used rest
    else .ok d :: applyQuota quota (used + d.blob.length) rest
  | used, .error e :: rest => .error e :: applyQuota quota used rest

/-! ## Configuration and state -/

structure Cfg where
  pol : Policy := {}
  /-- Decoded bytes outstanding per envelope (recommended 50 MiB). -/
  quota : Nat := 50 * 1024 * 1024
  /-- Host fetches in flight per endpoint (recommended 10). -/
  maxInFlight : Nat := 10
  /-- Per-URL fetch timeout the host applies (recommended 30 s). -/
  timeoutSecs : Nat := 30
  /-- Answer `resource.info`; `false` redacts it (`resource.info.error`). -/
  discloseInfo : Bool := true
  /-- Disclose `maxBytes`/`maxUrls` in `resource.info`. -/
  discloseLimits : Bool := true
  /-- Scheme-appropriate allowlist for the sniffed MIME type; anything else is
  `blocked-by-policy`. -/
  mimeAllowed : Scheme → String → Bool := defaultMimeAllowed

inductive SlotSt where
  | queued
  | waiting (n : Nat)
  | got (o : Outcome)

structure Slot where
  url : String
  st : SlotSt

structure Job where
  port : PortId
  id : String
  many : Bool
  slots : List Slot

structure St where
  cfg : Cfg
  jobs : List Job
  next : Nat

def St.init (cfg : Cfg := {}) : St := ⟨cfg, [], 0⟩

inductive Req where
  | info (id : String)
  | bytes (id : String) (url : String)
  | bytesMany (id : String) (urls : List String)
  | cancel (id : String)
  deriving DecidableEq, Repr

/-! ## Codec -/

def requestTypes : List String := ["resource.info", "resource.bytes", "resource.bytesMany", "resource.cancel"]

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some t =>
    if t ∉ requestTypes then .unknown else
    match reqId? j with
    | none => .reject []
    | some id =>
      if t = "resource.info" then .ok (.info id)
      else if t = "resource.cancel" then .ok (.cancel id)
      else if t = "resource.bytes" then
        match j.getStr? "url" with
        | some u => .ok (.bytes id u)
        | none => .reject (errorReply "resource.bytes.error" j "invalid-request")
      else
        match (j.get? "urls").bind Json.asStrs? with
        | some us => .ok (.bytesMany id us)
        | none => .reject (errorReply "resource.bytesMany.error" j "invalid-request")
  | none => .unknown

def encodeReq : Req → Json
  | .info id => Json.msg "resource.info" [("id", some (.str id))]
  | .bytes id u => Json.msg "resource.bytes" [("id", some (.str id)), ("url", some (.str u))]
  | .bytesMany id us => Json.msg "resource.bytesMany" [("id", some (.str id)), ("urls", some (Json.strs us))]
  | .cancel id => Json.msg "resource.cancel" [("id", some (.str id))]

def errorMsg (t id : String) (e : ResErr) (m : Option String) : Json :=
  Json.msg t [("id", some (.str id)), ("error", some (.str (errName e))), ("message", m.map .str)]

def schemeName : Scheme → String
  | .https => "https" | .http => "http" | .data => "data" | .blossom => "blossom"
  | .hashtree => "hashtree" | .htree => "htree" | .nostr => "nostr"

def infoJson (cfg : Cfg) : Json :=
  Json.mkObj
    [("schemes", some (.arr ([Scheme.https, .blossom, .nostr, .hashtree, .htree, .data, .http].map fun sc =>
        .obj [("scheme", .str (schemeName sc)), ("enabled", .bool (schemeAllowed cfg.pol sc))]))),
     ("maxBytes", if cfg.discloseLimits then some (.nat cfg.pol.maxBytes) else none),
     ("maxUrls", if cfg.discloseLimits then some (.nat cfg.pol.maxUrls) else none)]

def itemJson (url : String) : Item → Json
  | .ok d => .obj [("url", .str url), ("ok", .bool true), ("blob", .str (Base64.encode d.blob)),
                   ("mime", .str d.mime)]
  | .error (e, m) => Json.mkObj [("url", some (.str url)), ("ok", some (.bool false)),
                   ("error", some (.str (errName e))), ("message", m.map .str)]

def slotItem (h : Host) (pol : Policy) (mimeOk : Scheme → String → Bool) (sl : Slot) : Item :=
  match sl.st with
  | .got o => gateMime mimeOk sl.url (itemOf h pol sl.url o)
  | _ => .error (.networkError, none)

/-- The items a finished job delivers, in input order. -/
def jobItems (h : Host) (cfg : Cfg) (j : Job) : List Item :=
  applyQuota cfg.quota 0 (j.slots.map (slotItem h cfg.pol cfg.mimeAllowed))

/-- The terminal envelope of a finished job. -/
def finishMsg (h : Host) (cfg : Cfg) (j : Job) : Json :=
  if j.many then
    Json.msg "resource.bytesMany.result"
      [("id", some (.str j.id)),
       ("items", some (.arr ((j.slots.map (·.url)).zipWith (fun u it => itemJson u it) (jobItems h cfg j))))]
  else
    match jobItems h cfg j with
    | .ok d :: _ => Json.msg "resource.bytes.result"
        [("id", some (.str j.id)), ("blob", some (.str (Base64.encode d.blob))), ("mime", some (.str d.mime))]
    | .error (e, m) :: _ => errorMsg "resource.bytes.error" j.id e m
    | [] => errorMsg "resource.bytes.error" j.id .invalidRequest none

/-! ## Scheduling -/

def SlotSt.busy : SlotSt → Bool
  | .got _ => false
  | _ => true

def Job.done (j : Job) : Bool := !(j.slots.any (·.st.busy))

def waitingTags (j : Job) : List Nat :=
  j.slots.filterMap fun sl => match sl.st with | .waiting n => some n | _ => none

def inFlight (jobs : List Job) (p : PortId) : Nat :=
  ((jobs.filter (·.port == p)).map fun j => (waitingTags j).length).sum

/-- Start up to `budget` queued slots. Returns slots, next tag, budget left, calls. -/
def launch : Nat → Nat → List Slot → List Slot × Nat × Nat × List Eff
  | next, budget, [] => ([], next, budget, [])
  | next, budget + 1, ⟨u, .queued⟩ :: rest =>
    let r := launch (next + 1) budget rest
    (⟨u, .waiting next⟩ :: r.1, r.2.1, r.2.2.1, .call ⟨.resource, next⟩ (.fetch (norm u)) :: r.2.2.2)
  | next, budget, sl :: rest =>
    let r := launch next budget rest
    (sl :: r.1, r.2.1, r.2.2.1, r.2.2.2)

/-- Start queued URLs of endpoint `p`, oldest request first, within its budget. -/
def pumpJobs (p : PortId) : Nat → Nat → List Job → List Job × Nat × List Eff
  | next, _, [] => ([], next, [])
  | next, budget, j :: js =>
    if j.port = p then
      let (sl, nx, b, es) := launch next budget j.slots
      let (rs, nx', es') := pumpJobs p nx b js
      ({ j with slots := sl } :: rs, nx', es ++ es')
    else
      let (rs, nx', es') := pumpJobs p next budget js
      (j :: rs, nx', es')

def pump (s : St) (p : PortId) : St × List Eff :=
  let (jobs, next, es) := pumpJobs p s.next (s.cfg.maxInFlight - inFlight s.jobs p) s.jobs
  ({ s with jobs, next }, es)

/-- Send the terminal envelope of every finished job and forget it. -/
def flush (h : Host) (s : St) : St × List Eff :=
  ({ s with jobs := s.jobs.filter (!·.done) },
   (s.jobs.filter (·.done)).map fun j => .send j.port (finishMsg h s.cfg j))

/-- After any change for endpoint `p`: start what may start, then answer what is done. -/
def settle (h : Host) (s : St) (p : PortId) : St × List Eff :=
  let (s1, e1) := pump s p
  let (s2, e2) := flush h s1
  (s2, e1 ++ e2)

def initSlot (pol : Policy) (url : String) : Slot :=
  let u := norm url
  match precheck pol u with
  | some e => ⟨url, .got (.failed e none)⟩
  | none =>
    if schemeOf u = some .data then
      match dataBytes? u with
      | some b => ⟨url, .got (.fetched ⟨[], some b, false, ""⟩)⟩
      | none => ⟨url, .got (.failed .invalidRequest none)⟩
    else ⟨url, .queued⟩

def inUse (s : St) (p : PortId) (id : String) : Bool := s.jobs.any fun j => j.port == p && j.id == id

def start (h : Host) (cx : Ctx) (s : St) (id : String) (many : Bool) (urls : List String) : St × List Eff :=
  if inUse s cx.port id then (s, [])
  else settle h { s with jobs := s.jobs ++ [⟨cx.port, id, many, urls.map (initSlot s.cfg.pol)⟩] } cx.port

/-! ## Component -/

def handle (h : Host) (_w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .info id =>
    if s.cfg.discloseInfo then
      (s, [.send cx.port (Json.msg "resource.info.result" [("id", some (.str id)), ("info", some (infoJson s.cfg))])])
    else (s, [.send cx.port (errorMsg "resource.info.error" id .blockedByPolicy none)])
  | .bytes id url => start h cx s id false [url]
  | .bytesMany id urls =>
    if urls = [] then (s, [.send cx.port (errorMsg "resource.bytesMany.error" id .invalidRequest none)])
    else if urls.length > s.cfg.pol.maxUrls then
      (s, [.send cx.port (errorMsg "resource.bytesMany.error" id .tooLarge none)])
    else start h cx s id true urls
  | .cancel id =>
    let gone := s.jobs.filter fun j => j.port == cx.port && j.id == id
    let (s', es) := settle h { s with jobs := s.jobs.filter fun j => !(j.port == cx.port && j.id == id) } cx.port
    (s', (gone.flatMap waitingTags).map (fun n => .effect (.cancel ⟨.resource, n⟩)) ++ es)

/-- Record a host reply in the slot waiting on tag `n`. -/
def record (n : Nat) (o : Outcome) (sl : Slot) : Slot :=
  match sl.st with
  | .waiting m => if m = n then ⟨sl.url, .got o⟩ else sl
  | _ => sl

def onReply (h : Host) (_w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.jobs.find? (fun j => (waitingTags j).contains n) with
  | none => (s, [])
  | some j =>
    let o := outcomeOf rep
    settle h { s with jobs := s.jobs.map fun j' => { j' with slots := j'.slots.map (record n o) } } j.port

def onEvent (_h : Host) (_w : World) (s : St) (_e : HostEvent) : St × List Eff := (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with jobs := s.jobs.filter (·.port != p) },
   ((s.jobs.filter (·.port == p)).flatMap waitingTags).map fun n => .effect (.cancel ⟨.resource, n⟩))

def mentions (s : St) (p : PortId) : Bool := s.jobs.any (·.port == p)

/-! ## Properties: codec -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r <;> simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
    Json.lookup, reqId?]

/-! ## Properties: per-endpoint state -/

theorem pumpJobs_ports (p : PortId) (next budget : Nat) (js : List Job) :
    (pumpJobs p next budget js).1.map (fun j => (j.port, j.id)) = js.map (fun j => (j.port, j.id)) := by
  induction js generalizing next budget with
  | nil => rfl
  | cons j js ih =>
    simp only [pumpJobs]
    split <;> simp [ih]

theorem mentions_of_pairs {s s' : St} (hp : s'.jobs.map (fun j => (j.port, j.id)) = s.jobs.map (fun j => (j.port, j.id)))
    (q : PortId) : mentions s' q = mentions s q := by
  have e : ∀ t : St, mentions t q = (t.jobs.map (fun j => (j.port, j.id))).any (fun x => x.1 == q) := by
    intro t; simp [mentions, List.any_map, Function.comp_def]
  rw [e, e, hp]

theorem pump_mentions (s : St) (p q : PortId) : mentions (pump s p).1 q = mentions s q :=
  mentions_of_pairs (pumpJobs_ports _ _ _ _) q

theorem flush_mentions (h : Host) (s : St) (q : PortId) (hm : mentions (flush h s).1 q = true) :
    mentions s q = true := by
  simp only [flush, mentions, List.any_filter] at hm ⊢
  simp only [List.any_eq_true, Bool.and_eq_true] at hm ⊢
  obtain ⟨x, hx, -, hq⟩ := hm
  exact ⟨x, hx, hq⟩

theorem settle_mentions (h : Host) (s : St) (p q : PortId) (hm : mentions (settle h s p).1 q = true) :
    mentions s q = true := by
  simp only [settle] at hm
  rw [← pump_mentions s p q]
  exact flush_mentions h _ q hm

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp [drop, mentions] at h ⊢
  obtain ⟨x, hx, -, hq⟩ := h
  exact ⟨x, hx, hq⟩

theorem start_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (id : String) (many : Bool)
    (urls : List String) (q : PortId) (hcx : cx ∈ w.live) (hm : mentions (start h cx s id many urls).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  simp only [start] at hm
  split at hm
  · exact .inl hm
  · have := settle_mentions h _ _ q hm
    simp only [mentions, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true] at this
    rcases this with h1 | h1
    · exact .inl h1
    · exact .inr ⟨cx, hcx, by simpa using h1⟩

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  cases r with
  | info id => simp only [handle] at hm; split at hm <;> exact .inl hm
  | bytes id url => exact start_mentions h w cx s id false [url] q hcx hm
  | bytesMany id urls =>
    simp only [handle] at hm
    split at hm
    · exact .inl hm
    · split at hm
      · exact .inl hm
      · exact start_mentions h w cx s id true urls q hcx hm
  | cancel id =>
    simp only [handle] at hm
    have := settle_mentions h _ _ q hm
    apply Or.inl
    simp only [mentions, List.any_filter, List.any_eq_true, Bool.and_eq_true] at this ⊢
    obtain ⟨x, hx, -, hq⟩ := this
    exact ⟨x, hx, hq⟩

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  simp only [onReply] at hm
  split at hm
  · exact hm
  · have := settle_mentions h _ _ q hm
    simpa [mentions, List.any_map] using this

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q :=
  .inl hm

/-! ## Properties lifted from `NapResource` -/

theorem applyQuota_ok {quota used : Nat} {items : List Item} {d : Delivered}
    (h : .ok d ∈ applyQuota quota used items) : .ok d ∈ items := by
  induction items generalizing used with
  | nil => simp [applyQuota] at h
  | cons it rest ih =>
    cases it with
    | ok d' =>
      simp only [applyQuota] at h
      split at h
      · simp only [List.mem_cons, reduceCtorEq, false_or] at h
        exact List.mem_cons_of_mem _ (ih h)
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h)
    | error e =>
      simp only [applyQuota, List.mem_cons, reduceCtorEq, false_or] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem applyQuota_length (quota used : Nat) (items : List Item) :
    (applyQuota quota used items).length = items.length := by
  induction items generalizing used with
  | nil => rfl
  | cons it rest ih =>
    cases it with
    | ok d => simp only [applyQuota]; split <;> simp [ih]
    | error e => simp [applyQuota, ih]

/-- Every delivered item is `NapResource.bytes` of some fetch outcome for its slot's URL,
and its MIME type is on the allowlist of that URL's scheme. -/
theorem jobItems_slot {h : Host} {cfg : Cfg} {j : Job} {d : Delivered} (hd : .ok d ∈ jobItems h cfg j) :
    ∃ sl ∈ j.slots, ∃ o, NapResource.bytes (envOf h o) cfg.pol (norm sl.url) = .ok d ∧
      ∃ sc, schemeOf (norm sl.url) = some sc ∧ cfg.mimeAllowed sc d.mime = true := by
  have := applyQuota_ok hd
  simp only [List.mem_map] at this
  obtain ⟨sl, hsl, hs⟩ := this
  simp only [slotItem] at hs
  split at hs
  · rename_i o _
    obtain ⟨hi, hm⟩ := gateMime_ok hs
    cases o with
    | failed e m => simp [itemOf] at hi
    | fetched o =>
      simp only [itemOf] at hi
      split at hi
      · rename_i d' hb
        simp only [Except.ok.injEq] at hi
        exact ⟨sl, hsl, o, hi ▸ hb, hm⟩
      · simp at hi
  · simp at hs

theorem jobItems_ok {h : Host} {cfg : Cfg} {j : Job} {d : Delivered} (hd : .ok d ∈ jobItems h cfg j) :
    ∃ u o, NapResource.bytes (envOf h o) cfg.pol u = .ok d := by
  obtain ⟨sl, -, o, hb, -⟩ := jobItems_slot hd
  exact ⟨_, o, hb⟩

/-- SSRF: no delivered byte came through a private, loopback, link-local, ULA or
metadata address on any hop the host reported; redirects and size were within
policy; MIME is sniffed from the delivered bytes, never raw SVG, and on the
scheme-appropriate allowlist (`Cfg.mimeAllowed`). -/
theorem jobItems_policy {h : Host} {cfg : Cfg} {j : Job} {d : Delivered} (hd : .ok d ∈ jobItems h cfg j) :
    ∃ o : FetchOutcome, (∀ ip ∈ o.hops, isPrivate ip = false) ∧ o.hops.length ≤ cfg.pol.maxRedirects + 1 ∧
      (∃ b, o.body = some b ∧ b.length ≤ cfg.pol.maxBytes) ∧
      d.mime ≠ svgMime ∧ d.mime = h.sniff d.blob ∧
      ∃ sl ∈ j.slots, ∃ sc, schemeOf (norm sl.url) = some sc ∧ cfg.mimeAllowed sc d.mime = true := by
  obtain ⟨sl, hsl, o, hb, hm⟩ := jobItems_slot hd
  obtain ⟨hn, hs⟩ := bytes_mime_sniffed_not_svg hb
  exact ⟨o, bytes_no_private_hop hb, bytes_redirects_capped hb, bytes_size_capped hb,
    hn, hs, sl, hsl, hm⟩

/-- A delivered `blossom:` item matched its content hash. -/
theorem itemOf_blossom {h : Host} {pol : Policy} {url : String} {o : FetchOutcome} {d : Delivered}
    (hs : schemeOf (norm url) = some .blossom) (hd : itemOf h pol url (.fetched o) = .ok d) :
    ∃ hh b, blossomHash? (norm url) = some hh ∧ o.body = some b ∧ h.crypto.sha256 b = hh := by
  simp only [itemOf] at hd
  split at hd
  · rename_i d' hb
    simp only [Except.ok.injEq] at hd
    subst hd
    exact blossom_hash_verified hs hb
  · simp at hd

/-- `bytesMany` items keep the input order and length. -/
theorem jobItems_length (h : Host) (cfg : Cfg) (j : Job) : (jobItems h cfg j).length = j.slots.length := by
  simp [jobItems, applyQuota_length]

/-- `http:` is off by default, and unknown schemes are unsupported, before any network. -/
theorem http_unsupported_by_default (url : String) (hs : schemeOf url = some .http) :
    precheck {} url = some .unsupportedScheme := by
  simp [precheck, hs, schemeAllowed]

theorem unknown_scheme_unsupported (pol : Policy) (url : String) (hs : schemeOf url = none) :
    precheck pol url = some .unsupportedScheme := by
  simp [precheck, hs]

/-! ## Properties: terminal envelopes and cancellation -/

theorem finishMsg_id (h : Host) (cfg : Cfg) (j : Job) : (finishMsg h cfg j).getStr? "id" = some j.id := by
  unfold finishMsg
  split
  · simp [Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]
  · split
    · simp [Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]
    · rename_i m _ _
      cases m <;> simp [errorMsg, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]
    · simp [errorMsg, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

theorem launch_calls (next budget : Nat) (sl : List Slot) (e : Eff) (he : e ∈ (launch next budget sl).2.2.2) :
    ∃ t c, e = .call t c := by
  induction next, budget, sl using launch.induct with
  | case1 => simp [launch] at he
  | case2 next budget u rest ih =>
    simp only [launch, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨_, _, rfl⟩
    · exact ih he
  | case3 next budget sl rest _ ih =>
    rw [launch.eq_3 _ _ _ _ (by assumption)] at he
    exact ih he

theorem pumpJobs_calls (p : PortId) (next budget : Nat) (js : List Job) (e : Eff)
    (he : e ∈ (pumpJobs p next budget js).2.2) : ∃ t c, e = .call t c := by
  induction js generalizing next budget with
  | nil => simp [pumpJobs] at he
  | cons j js ih =>
    simp only [pumpJobs] at he
    split at he
    · simp only [List.mem_append] at he
      rcases he with he | he
      · exact launch_calls _ _ _ _ he
      · exact ih _ _ he
    · exact ih _ _ he

/-- Every message `settle` sends is the terminal envelope of a job it was given
(same endpoint, same `id`). -/
theorem settle_sends (h : Host) (s : St) (p q : PortId) (m : Json) (he : Eff.send q m ∈ (settle h s p).2) :
    ∃ j ∈ s.jobs, ∃ j' : Job, j'.port = j.port ∧ j'.id = j.id ∧ q = j.port ∧ m = finishMsg h s.cfg j' := by
  simp only [settle, pump, flush, List.mem_append, List.mem_map, List.mem_filter] at he
  rcases he with he | ⟨j', ⟨hj', -⟩, he⟩
  · obtain ⟨_, _, he⟩ := pumpJobs_calls _ _ _ _ _ he
    cases he
  · simp only [Eff.send.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hp := pumpJobs_ports p s.next (s.cfg.maxInFlight - inFlight s.jobs p) s.jobs
    have : (j'.port, j'.id) ∈ s.jobs.map (fun j => (j.port, j.id)) := by
      rw [← hp]; exact List.mem_map_of_mem hj'
    simp only [List.mem_map, Prod.mk.injEq] at this
    obtain ⟨j, hj, e1, e2⟩ := this
    exact ⟨j, hj, j', e1.symm, e2.symm, e1.symm, rfl⟩

/-- Host replies only ever produce terminal envelopes of requests still held. -/
theorem onReply_sends (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId) (m : Json)
    (he : Eff.send q m ∈ (onReply h w s n rep).2) :
    ∃ j ∈ s.jobs, ∃ j' : Job, j'.port = j.port ∧ j'.id = j.id ∧ q = j.port ∧ m = finishMsg h s.cfg j' := by
  simp only [onReply] at he
  split at he
  · simp at he
  · obtain ⟨j, hj, j', e1, e2, e3, e4⟩ := settle_sends h _ _ q m he
    simp only [List.mem_map] at hj
    obtain ⟨j0, hj0, rfl⟩ := hj
    exact ⟨j0, hj0, j', e1, e2, e3, e4⟩

/-- Cancellation drops late terminals: after `resource.cancel id`, no host reply
produces an envelope for that `id` on that endpoint. -/
theorem cancel_drops_late (h : Host) (w : World) (cx : Ctx) (s : St) (id : String) (n : Nat) (rep : Reply)
    (m : Json) (he : Eff.send cx.port m ∈ (onReply h w (handle h w cx s (.cancel id)).1 n rep).2) :
    m.getStr? "id" ≠ some id := by
  obtain ⟨j, hj, j', e1, e2, e3, rfl⟩ := onReply_sends h w _ n rep cx.port m he
  rw [finishMsg_id, e2]
  intro hid
  simp only [Option.some.injEq] at hid
  simp only [handle, settle, flush] at hj
  simp only [List.mem_filter] at hj
  obtain ⟨hj, -⟩ := hj
  have hp := pumpJobs_ports cx.port s.next
    (s.cfg.maxInFlight - inFlight (s.jobs.filter fun j => !(j.port == cx.port && j.id == id)) cx.port)
    (s.jobs.filter fun j => !(j.port == cx.port && j.id == id))
  have : (j.port, j.id) ∈ (s.jobs.filter fun j => !(j.port == cx.port && j.id == id)).map (fun j => (j.port, j.id)) := by
    rw [← hp]; exact List.mem_map_of_mem hj
  simp only [List.mem_map, List.mem_filter, Prod.mk.injEq] at this
  obtain ⟨j0, ⟨-, hn⟩, a1, a2⟩ := this
  rw [a1, a2, ← e3, hid] at hn
  simp at hn

/-- Teardown abandons exactly the endpoint's outstanding fetches and sends nothing. -/
theorem drop_cancels (s : St) (p : PortId) (e : Eff) (he : e ∈ (drop s p).2) :
    ∃ n, e = .effect (.cancel ⟨.resource, n⟩) := by
  simp only [drop, List.mem_map] at he
  obtain ⟨n, -, rfl⟩ := he
  exact ⟨n, rfl⟩

/-! ## Vectors -/

def sampleHost : Host :=
  { crypto := ⟨fun _ => "", fun _ => true⟩, verifyEvent := fun _ => true,
    sniff := fun _ => "application/octet-stream", rasterize := fun _ => none,
    looksCiphertext := fun _ => false, encryptedWith := fun _ => none, transform := id }

def sampleCtx : Ctx :=
  { port := 3, window := 1, identity := { dTag := some "viewer", artifactHash := "aa", publisher := "pk" },
    exposed := [.resource], inst := 0 }

def sampleWorld : World := { now := 0, live := [sampleCtx], user := "" }

def run (j : Json) (s : St := .init) : St × List Eff :=
  match decode j with
  | .ok r => handle sampleHost sampleWorld sampleCtx s r
  | .reject rs => (s, rs.map (.send sampleCtx.port))
  | .unknown => (s, [])

def sends (es : List Eff) : List Json := es.filterMap fun | .send _ m => some m | _ => none

-- Upstream byte-encoding example: bytes `00 01 02 ff` (here from a `data:` URL).
#guard match sends (run (Json.parse! "{ \"type\": \"resource.bytes\", \"id\": \"r1\", \"url\": \"data:application/octet-stream;base64,AAEC/w==\" }")).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytes.result\", \"id\": \"r1\", \"blob\": \"AAEC/w==\", \"mime\": \"application/octet-stream\" }")
  | _ => false
-- The percent form of the same bytes.
#guard match sends (run (Json.parse! "{ \"type\": \"resource.bytes\", \"id\": \"r1\", \"url\": \"data:,%00%01%02%FF\" }")).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytes.result\", \"id\": \"r1\", \"blob\": \"AAEC/w==\", \"mime\": \"application/octet-stream\" }")
  | _ => false

-- An https fetch: one host call, then the result when the host replies.
#guard match run (Json.parse! "{ \"type\": \"resource.bytes\", \"id\": \"r2\", \"url\": \"https://example.com/a.bin\" }") with
  | (s, [.call ⟨.resource, 0⟩ (.fetch "https://example.com/a.bin")]) =>
    match sends (onReply sampleHost sampleWorld s 0 (.fetched ⟨[.v4 93 184 216 34], some [0, 1, 2, 255], false, "text/html"⟩)).2 with
    | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytes.result\", \"id\": \"r2\", \"blob\": \"AAEC/w==\", \"mime\": \"application/octet-stream\" }")
    | _ => false
  | _ => false

-- A private hop is refused.
#guard match run (Json.parse! "{ \"type\": \"resource.bytes\", \"id\": \"r3\", \"url\": \"https://example.com/a\" }") with
  | (s, [_]) =>
    match sends (onReply sampleHost sampleWorld s 0 (.fetched ⟨[.v4 93 184 216 34, .v4 169 254 169 254], some [1], false, ""⟩)).2 with
    | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytes.error\", \"id\": \"r3\", \"error\": \"blocked-by-policy\" }")
    | _ => false
  | _ => false

-- A network error reported by the host, with its diagnostic message.
#guard match run (Json.parse! "{ \"type\": \"resource.bytes\", \"id\": \"r4\", \"url\": \"https://example.com/a\" }") with
  | (s, [_]) =>
    match sends (onReply sampleHost sampleWorld s 0 (.json (Json.parse! "{\"error\":\"network-error\",\"message\":\"TLS failure\"}"))).2 with
    | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytes.error\", \"id\": \"r4\", \"error\": \"network-error\", \"message\": \"TLS failure\" }")
    | _ => false
  | _ => false

-- bytesMany: per-item independence and input order; a cancelled request answers nothing.
#guard match run (Json.parse! "{ \"type\": \"resource.bytesMany\", \"id\": \"m1\", \"urls\": [\"https://example.com/a\", \"ftp://x\", \"data:,hi\", \"htree://npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjptg/tree#link-visible\"] }") with
  | (s, [.call ⟨.resource, 0⟩ (.fetch "https://example.com/a")]) =>
    (match sends (onReply sampleHost sampleWorld s 0 (.fetched ⟨[.v4 1 1 1 1], none, false, ""⟩)).2 with
     | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytesMany.result\", \"id\": \"m1\", \"items\": [ {\"url\": \"https://example.com/a\", \"ok\": false, \"error\": \"not-found\"}, {\"url\": \"ftp://x\", \"ok\": false, \"error\": \"unsupported-scheme\"}, {\"url\": \"data:,hi\", \"ok\": true, \"blob\": \"aGk=\", \"mime\": \"application/octet-stream\"}, {\"url\": \"htree://npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjptg/tree#link-visible\", \"ok\": false, \"error\": \"invalid-request\"} ] }")
     | _ => false) &&
    (match handle sampleHost sampleWorld sampleCtx s (.cancel "m1") with
     | (s', [.effect (.cancel ⟨.resource, 0⟩)]) => (onReply sampleHost sampleWorld s' 0 (.fetched ⟨[], some [1], false, ""⟩)).2.isEmpty
     | _ => false)
  | _ => false

#guard match sends (run (Json.parse! "{ \"type\": \"resource.bytesMany\", \"id\": \"m2\", \"urls\": [] }")).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytesMany.error\", \"id\": \"m2\", \"error\": \"invalid-request\" }")
  | _ => false
#guard match sends (run (Json.parse! "{ \"type\": \"resource.bytes\", \"id\": \"m3\" }")).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytes.error\", \"id\": \"m3\", \"error\": \"invalid-request\" }")
  | _ => false
#guard match sends (run (Json.parse! "{ \"type\": \"resource.info\", \"id\": \"i1\" }")).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.info.result\", \"id\": \"i1\", \"info\": { \"schemes\": [ {\"scheme\":\"https\",\"enabled\":true}, {\"scheme\":\"blossom\",\"enabled\":true}, {\"scheme\":\"nostr\",\"enabled\":true}, {\"scheme\":\"hashtree\",\"enabled\":true}, {\"scheme\":\"htree\",\"enabled\":true}, {\"scheme\":\"data\",\"enabled\":true}, {\"scheme\":\"http\",\"enabled\":false} ], \"maxBytes\": 10485760, \"maxUrls\": 100 } }")
  | _ => false
#guard decode (Json.parse! "{ \"type\": \"resource.stream\", \"id\": \"x\" }") matches .unknown
#guard decode (Json.parse! "{ \"type\": \"resource.cancel\" }") matches .reject []

-- Scheme-appropriate MIME allowlist: a sniffed type off the list is `blocked-by-policy`.
def sniffHost : Host :=
  { sampleHost with sniff := fun b => if b = [60] then "text/html" else "Image/PNG; x=1" }
#guard match run (Json.parse! "{ \"type\": \"resource.bytes\", \"id\": \"r5\", \"url\": \"https://example.com/a\" }") with
  | (s, [_]) =>
    match sends (onReply sniffHost sampleWorld s 0 (.fetched ⟨[.v4 93 184 216 34], some [60], false, "image/png"⟩)).2 with
    | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytes.error\", \"id\": \"r5\", \"error\": \"blocked-by-policy\" }")
    | _ => false
  | _ => false
#guard match run (Json.parse! "{ \"type\": \"resource.bytes\", \"id\": \"r6\", \"url\": \"https://example.com/a\" }") with
  | (s, [_]) =>
    match sends (onReply sniffHost sampleWorld s 0 (.fetched ⟨[.v4 93 184 216 34], some [1], false, ""⟩)).2 with
    | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytes.result\", \"id\": \"r6\", \"blob\": \"AQ==\", \"mime\": \"Image/PNG; x=1\" }")
    | _ => false
  | _ => false
-- `nostr:` resolves to event JSON; an image or octet stream is refused.
#guard match run (Json.parse! "{ \"type\": \"resource.bytes\", \"id\": \"r7\", \"url\": \"nostr:npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjptg\" }") with
  | (s, [_]) =>
    match sends (onReply sampleHost sampleWorld s 0 (.fetched ⟨[], some [1], false, ""⟩)).2 with
    | [m] => Json.same m (Json.parse! "{ \"type\": \"resource.bytes.error\", \"id\": \"r7\", \"error\": \"blocked-by-policy\" }")
    | _ => false
  | _ => false
#guard mimeEssence " Text/Plain ; charset=utf-8" == "text/plain"
#guard defaultMimeAllowed .https "image/webp" && !defaultMimeAllowed .https "text/html" &&
  !defaultMimeAllowed .data "application/javascript" && defaultMimeAllowed .nostr "application/json" &&
  !defaultMimeAllowed .nostr "image/png"

-- URL grammar.
#guard htreeOk "htree://npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjptg/my%2Ftree/a/b.png#k=0000000000000000000000000000000000000000000000000000000000000000"
#guard !htreeOk "htree://npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjptg:tree/a"
#guard !htreeOk "htree://npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjptg/tree?x=1"
#guard !htreeOk "htree://npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjptg/tree/%zz"
#guard !htreeOk "htree://self/tree"
#guard nostrOk "nostr:npub10elfcs4fr0l0r8af98jlmgdh9c8tcxjvz9qkw038js35mp4dma8qzvjptg"
#guard !nostrOk "nostr:nsec1vl029mgpspedva04g90vltkh6fvh240zqtv9k0t9af8935ke9laqsnlfe5"
#guard precheck {} (norm "nhash1qqqq") == some .invalidRequest
#guard precheck {} "http://example.com" == some .unsupportedScheme

end Napplet.Run.Resource
