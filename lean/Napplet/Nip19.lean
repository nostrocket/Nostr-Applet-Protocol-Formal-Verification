/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NIP-19 `naddr` (bech32, BIP-173)

The napplet-side binding decodes the `#<naddr>` fragment of an `intent.invoke`
convention URI into `IntentHandlerHint {address, relays?}` (NAP-INTENT §Convention
URI normalization). This module implements that decoding exactly:

* bech32 per BIP-173 (checksum constant 1, no mixed case), without the 90-character
  limit, which NIP-19 lifts for TLV entities;
* NIP-19 TLV: `0` special (`d` identifier, UTF-8), `1` relay (UTF-8, repeatable),
  `2` author (32 bytes), `3` kind (32-bit big-endian); unknown types are ignored;
* a handler hint must be kind 35129 with a non-empty `d`; its address is
  `35129:<64 lowercase hex pubkey>:<d>`, `d` kept byte for byte.
-/

namespace Napplet.Nip19

def charset : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList

def charVal? (c : Char) : Option Nat := charset.idxOf? c

def generators : List Nat := [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]

def polymod (vs : List Nat) : Nat :=
  vs.foldl (fun chk v =>
    let b := chk >>> 25
    let chk := ((chk &&& 0x1ffffff) <<< 5) ^^^ v
    (List.range 5).foldl (fun c i => if (b >>> i) &&& 1 = 1 then c ^^^ generators[i]! else c) chk) 1

def hrpExpand (hrp : List Char) : List Nat :=
  hrp.map (·.toNat >>> 5) ++ [0] ++ hrp.map (·.toNat &&& 31)

def checksum (hrp : List Char) (data : List Nat) : List Nat :=
  let pm := polymod (hrpExpand hrp ++ data ++ [0, 0, 0, 0, 0, 0]) ^^^ 1
  (List.range 6).map fun i => (pm >>> (5 * (5 - i))) &&& 31

/-- Regroup bits. `pad = false` (decoding) rejects non-zero or overlong padding. -/
def convertBits (fromBits toBits : Nat) (pad : Bool) (data : List Nat) : Option (List Nat) :=
  let maxv := (1 <<< toBits) - 1
  let step : Option (Nat × Nat × List Nat) → Nat → Option (Nat × Nat × List Nat) := fun st v =>
    st.bind fun (acc, bits, out) =>
      if v >>> fromBits ≠ 0 then none else
      let acc := (acc <<< fromBits) ||| v
      let bits := bits + fromBits
      let rec emit (fuel : Nat) (bits : Nat) (out : List Nat) : Nat × List Nat :=
        match fuel with
        | 0 => (bits, out)
        | f + 1 => if bits ≥ toBits then emit f (bits - toBits) (out ++ [(acc >>> (bits - toBits)) &&& maxv]) else (bits, out)
      let (bits, out) := emit (bits / toBits + 1) bits out
      some (acc, bits, out)
  match data.foldl step (some (0, 0, [])) with
  | none => none
  | some (acc, bits, out) =>
    if pad then (if bits > 0 then some (out ++ [(acc <<< (toBits - bits)) &&& maxv]) else some out)
    else if bits ≥ fromBits || ((acc <<< (toBits - bits)) &&& maxv) ≠ 0 then none
    else some out

/-- Decode bech32 text to (hrp, bytes). -/
def decode (s : String) : Option (String × List Nat) :=
  let cs := s.toList
  if cs.any Char.isUpper && cs.any Char.isLower then none else
  let cs := cs.map Char.toLower
  let sepIdx := cs.length - 1 - ((cs.reverse.idxOf? '1').getD cs.length)
  if (cs.reverse.idxOf? '1').isNone || sepIdx < 1 || sepIdx + 7 > cs.length then none else
  let hrp := cs.take sepIdx
  if hrp.any (fun c => c.toNat < 33 || c.toNat > 126) then none else
  match (cs.drop (sepIdx + 1)).mapM charVal? with
  | none => none
  | some vals =>
    if polymod (hrpExpand hrp ++ vals) ≠ 1 then none else
    (convertBits 5 8 false (vals.take (vals.length - 6))).map (String.ofList hrp, ·)

def encode (hrp : String) (bytes : List Nat) : String :=
  let data := (convertBits 8 5 true bytes).getD []
  let all := data ++ checksum hrp.toList data
  hrp ++ "1" ++ String.ofList (all.map fun v => charset[v]!)

/-! ### TLV and `naddr` -/

def parseTlv : Nat → List Nat → Option (List (Nat × List Nat))
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, t :: l :: rest =>
    if rest.length < l then none
    else (parseTlv fuel (rest.drop l)).map ((t, rest.take l) :: ·)
  | _ + 1, [_] => none

def hexByte (n : Nat) : String :=
  let d := fun k => if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
  String.ofList [d (n / 16), d (n % 16)]

def utf8? (bs : List Nat) : Option String :=
  String.fromUTF8? ⟨(bs.map Nat.toUInt8).toArray⟩

structure Naddr where
  kind : Nat
  pubkey : String
  d : String
  relays : List String
  deriving DecidableEq, Repr

def decodeNaddr (s : String) : Option Naddr := do
  let (hrp, bytes) ← decode s
  guard (hrp = "naddr")
  let tlv ← parseTlv (bytes.length + 1) bytes
  let d ← (tlv.find? (·.1 == 0)).bind (utf8? ·.2)
  let author ← (tlv.find? (·.1 == 2)).map (·.2)
  guard (author.length = 32)
  let kindB ← (tlv.find? (·.1 == 3)).map (·.2)
  guard (kindB.length = 4)
  let kind := kindB.foldl (fun a b => a * 256 + b) 0
  let relays ← (tlv.filter (·.1 == 1)).mapM (utf8? ·.2)
  some { kind, pubkey := String.join (author.map hexByte), d, relays }

def encodeNaddr (a : Naddr) (authorBytes : List Nat) : String :=
  let dB := a.d.toUTF8.toList.map UInt8.toNat
  let kindB := [a.kind / 16777216 % 256, a.kind / 65536 % 256, a.kind / 256 % 256, a.kind % 256]
  let relaysB := a.relays.flatMap fun r => let b := r.toUTF8.toList.map UInt8.toNat; 1 :: b.length :: b
  encode "naddr" ([0, dB.length] ++ dB ++ relaysB ++ [2, 32] ++ authorBytes ++ [3, 4] ++ kindB)

/-- NAP-INTENT `IntentHandlerHint` from a bare `naddr` fragment: kind 35129 only,
non-empty `d`. -/
def handlerHint? (frag : String) : Option (String × List String) := do
  let a ← decodeNaddr frag
  guard (a.kind = 35129 && !a.d.isEmpty)
  some ("35129:" ++ a.pubkey ++ ":" ++ a.d, a.relays)

/-- PR #148 web binding: `intent.launch(naddr)` decodes into `target.address` and
`target.relays`, and "MUST reject an `naddr` that is not a kind `35129` or `15129`
napplet coordinate" (35129 with a non-empty `d`, 15129 with an empty `d`, as
`IntentTarget` requires). -/
def launchTarget? (s : String) : Option (String × List String) := do
  let a ← decodeNaddr s
  guard ((a.kind = 35129 && !a.d.isEmpty) || (a.kind = 15129 && a.d.isEmpty))
  some (toString a.kind ++ ":" ++ a.pubkey ++ ":" ++ a.d, a.relays)

/-! ### Vectors -/

-- BIP-173 valid test vectors
#guard (decode "A12UEL5L").isSome
#guard (decode "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw").isSome
-- invalid: bad checksum, mixed case
#guard (decode "A12UEL5M").isNone
#guard (decode "A12uEL5L").isNone

def author : List Nat := (List.range 32).map (· + 1)
def sample : Naddr := { kind := 35129, pubkey := String.join (author.map hexByte), d := "my-napplet",
                        relays := ["wss://relay.example.com"] }
#guard decodeNaddr (encodeNaddr sample author) == some sample
#guard handlerHint? (encodeNaddr sample author) ==
  some ("35129:" ++ sample.pubkey ++ ":my-napplet", ["wss://relay.example.com"])
#guard handlerHint? (encodeNaddr { sample with kind := 15129 } author) == none
#guard launchTarget? (encodeNaddr sample author) ==
  some ("35129:" ++ sample.pubkey ++ ":my-napplet", ["wss://relay.example.com"])
#guard launchTarget? (encodeNaddr { sample with kind := 15129, d := "", relays := [] } author) ==
  some ("15129:" ++ sample.pubkey ++ ":", [])
#guard launchTarget? (encodeNaddr { sample with kind := 15129 } author) == none
#guard launchTarget? (encodeNaddr { sample with kind := 5129, d := "" } author) == none
#guard launchTarget? (encodeNaddr { sample with kind := 30023 } author) == none
-- a flipped character breaks the checksum
def flipLast (s : String) : String :=
  let cs := s.toList
  String.ofList (cs.dropLast ++ [if cs.getLast? = some 'q' then 'p' else 'q'])
#guard handlerHint? (flipLast (encodeNaddr sample author)) == none

end Napplet.Nip19
