/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# SHA-256 (FIPS 180-4)

A computable SHA-256 over `Bytes`, returning lowercase hex, so the oracle can verify
manifests (`Crypto.sha256`) without a host. Checked against the FIPS 180-4 / NIST
example vectors below. The model itself never depends on which hash the host uses
(`Basic.lean`: hashing is supplied by the host); this is the oracle's stand-in.
-/

namespace Napplet.Sha256

def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def h0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- Padding: `0x80`, zeros, then the bit length as a 64-bit big-endian integer. -/
def pad (m : Bytes) : Bytes :=
  let len := m.length
  let zeros := (64 + 56 - (len + 1) % 64) % 64
  let bits := len * 8
  m ++ [0x80] ++ List.replicate zeros 0 ++
    (List.range 8).reverse.map fun i => (bits / 2 ^ (8 * i) % 256).toUInt8

/-- Big-endian words of a 64-byte block. -/
def words (b : Array UInt8) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for i in [0:16] do
    let j := off + 4 * i
    w := w.push ((b[j]!.toUInt32 <<< 24) ||| (b[j + 1]!.toUInt32 <<< 16) |||
      (b[j + 2]!.toUInt32 <<< 8) ||| b[j + 3]!.toUInt32)
  for i in [16:64] do
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  return w

def compress (h : Array UInt32) (w : Array UInt32) : Array UInt32 := Id.run do
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + S1 + ch + k[i]! + w[i]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

def hex2 (n : Nat) : String :=
  let d (x : Nat) : Char := if x < 10 then Char.ofNat (48 + x) else Char.ofNat (87 + x)
  String.ofList [d (n / 16 % 16), d (n % 16)]

def hexWord (x : UInt32) : String :=
  hex2 (x.toNat / 2 ^ 24 % 256) ++ hex2 (x.toNat / 2 ^ 16 % 256) ++
    hex2 (x.toNat / 2 ^ 8 % 256) ++ hex2 (x.toNat % 256)

/-- SHA-256 digest bytes. -/
def digest (m : Bytes) : Array UInt32 := Id.run do
  let p := (pad m).toArray
  let mut h := h0
  for i in [0:p.size / 64] do
    h := compress h (words p (64 * i))
  return h

/-- SHA-256 of `m` as 64 lowercase hex digits. -/
def hash (m : Bytes) : Hash := (digest m).foldl (fun s x => s ++ hexWord x) ""

def ofString (s : String) : Bytes := s.toUTF8.toList

-- FIPS 180-4 / NIST examples
#guard hash [] == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hash (ofString "abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hash (ofString "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard hash (ofString "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") ==
  "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
-- block-boundary lengths: 55, 56 and 64 bytes
#guard hash (List.replicate 55 0x61) == "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
#guard hash (List.replicate 56 0x61) == "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"
#guard hash (List.replicate 64 0x61) == "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"

end Napplet.Sha256
