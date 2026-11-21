/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Runtime

/-!
# Test harness for end-to-end vectors

A deterministic test host and a helper that boots napplets through the real
NIP-5D sequence (`create`, `load`, `napplet.hello` with one port), so vectors drive
`Runtime.step` with upstream example JSON and compare the JSON it sends.

The test host's hash is not SHA-256: it is a stand-in that only has to be a
function of the bytes, which is all the model relies on.
-/

namespace Napplet.Test

open _root_.Napplet.Runtime

def hexOf (n : Nat) : String :=
  let digits := (Nat.toDigits 16 n)
  String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- Stand-in hash: 64 hex digits derived from the byte sum and length. -/
def fakeHash (b : Bytes) : Hash := hexOf ((b.map UInt8.toNat).sum * 1000 + b.length)

def testHost : Host where
  crypto := { sha256 := fakeHash, verifySig := fun _ => true }
  verifyEvent := fun _ => true
  sniff := fun b => if b.take 4 = [0x89, 0x50, 0x4e, 0x47] then "image/png" else "application/octet-stream"
  rasterize := fun _ => none
  looksCiphertext := fun c => (c.splitOn "?iv=").length > 1
  encryptedWith := fun e => if e.kind = 4 then some .nip04 else none
  transform := id
  services := []

def allDomains : List Domain :=
  [.shell, .intent, .inc, .theme, .identity, .relay, .storage, .keys, .media, .notify,
   .resource, .config, .upload, .value, .outbox, .cvm, .link, .pow, .display]

def testCfg : Config :=
  { shell := { supported := allDomains, policy := fun _ => allDomains } }

def publisher : Pubkey := hexOf 0xabc

/-- A named manifest for `d` whose `x` matches `bytes`. -/
def manifest (d : String) (bytes : Bytes) : ManifestEvent :=
  { kind := 35129, pubkey := publisher, content := "test napplet", id := hexOf (bytes.length + 7),
    tags := [⟨"d", [d]⟩, ⟨"x", [fakeHash bytes]⟩] }

def runAll (h : Host) (cfg : Config) (s : RtState) : List Input → RtState × List Runtime.Output
  | [] => (s, [])
  | i :: is =>
    let (s1, o1) := Runtime.step h cfg s i
    let (s2, o2) := runAll h cfg s1 is
    (s2, o1 ++ o2)

/-- Boot napplet `d` in window `w`, bound to port `p`. -/
def bootInputs (w : WindowId) (p : PortId) (d : String) (bytes : Bytes) : List Input :=
  [.create w (manifest d bytes) bytes w, .load w, .hello w [p]]

def booted (ws : List (WindowId × PortId × String)) : RtState :=
  (runAll testHost testCfg (.init testCfg)
    (ws.flatMap fun (w, p, d) => bootInputs w p d (d.toList.map fun c => c.toNat.toUInt8))).1

/-- Messages sent to port `p`. -/
def sentTo (p : PortId) (os : List Runtime.Output) : List Json :=
  os.filterMap fun o => match o with | .send q m => if q = p then some m else none | _ => none

/-- Every output is a `send`, and the sends are exactly `expected` (as JSON text), in order. -/
def sendsAre (p : PortId) (os : List Runtime.Output) (expected : List String) : Bool :=
  let got := sentTo p os
  got.length = expected.length && (got.zip expected).all fun (g, e) => Json.same g (Json.parse! e)

/-- Feed one JSON text on port `p`. -/
def post (s : RtState) (p : PortId) (text : String) : RtState × List Runtime.Output :=
  Runtime.step testHost testCfg s (.message p (Json.parse! text))

def calls (os : List Runtime.Output) : List (CallTag × Call) :=
  os.filterMap fun o => match o with | .call t c => some (t, c) | _ => none

end Napplet.Test
