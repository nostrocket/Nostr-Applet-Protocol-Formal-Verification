/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Nap.Resource
import Napplet.Event

/-!
# Network helpers shared by `relay` and `outbox`

## Relay URL policy

`relayAllowed url` is the default policy for napplet-named relay URLs
(`Run.Relay.Cfg.scopedAllowed`, `Run.Outbox.Cfg.allowed`). NAP-OUTBOX: napplets MUST NOT
be able to force connections to private network relays or disallowed hosts.

A URL is allowed only if

* its scheme is `wss://` (lowercase, exactly);
* its authority has no userinfo (`@`), and an optional `:port` of ASCII digits;
* its host is either
  * a bracketed IPv6 literal that parses to 16 bytes (`::` compression and a trailing
    dotted IPv4 supported, no zone id) and is not private, or
  * a strict dotted-quad IPv4 literal (four decimal octets, no leading zeros) that is
    not private, or
  * a DNS name of ASCII letters, digits, `-` and `.` (case-insensitive) with at least
    two non-empty labels whose last label is not numeric, that is not `localhost`,
    `*.localhost`, `*.local` (mDNS) or `*.home.arpa` (RFC 8375).

"Private" is `NapResource.isPrivate`, widened here for literals by
`extraRefused`: IPv4 multicast/reserved (`224.0.0.0/4`, `240.0.0.0/4`), IPv6 `::/8`
(covers the unspecified, loopback, IPv4-compatible and IPv4-mapped forms and NAT64
`64:ff9b::/96`), IPv6 multicast `ff00::/8`, and 6to4 `2002::/16` wrapping a private
IPv4.

Anything a WHATWG URL parser would reinterpret as an IP address is refused unless it is
the strict form above: a last label that is all digits or `0x…` (`2130706433`,
`127.1`, `0x7f.0.0.1`), leading-zero octets (`010.0.0.1`, octal to a browser),
percent-encoded or non-ASCII hosts (IDNA could map them to digits), a trailing dot is
stripped first. A DNS name can still resolve to a private address; refusing that is
the host's job after resolution (`Napplet.Host` contract).

## Template pubkey claims

`EventTemplate.ofJson?` drops members it does not know, so `claimedPubkey?` reads a
string `pubkey` from the raw `event` member. NIP-5D/NAP-POW: a template carrying a
pubkey other than the shell user's is rejected rather than re-stamped.
-/

namespace Napplet.Net

open NapResource

/-! ## Character helpers -/

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- ASCII lowercase only (non-ASCII is refused elsewhere). -/
def lower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def splitOn (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match splitOn sep cs with
    | [] => [[]]
    | w :: ws => if c = sep then [] :: w :: ws else (c :: w) :: ws

/-- Decimal value of a non-empty digit string without leading zeros. -/
def decVal? (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | '0' :: _ :: _ => none
  | _ => if cs.all isDigit then some (cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)
         else none

/-- Hex value of 1–4 lowercase hex digits. -/
def hex16? (cs : List Char) : Option Nat :=
  if cs.length = 0 || cs.length > 4 then none
  else cs.foldlM (fun n c => (hexVal? c).map (16 * n + ·)) 0

/-! ## IP literals -/

/-- Strict dotted-quad IPv4: four decimal octets ≤ 255, no leading zeros. -/
def v4Octets? (cs : List Char) : Option (List Nat) :=
  match splitOn '.' cs with
  | [a, b, c, d] => do
    let os ← [a, b, c, d].mapM decVal?
    if os.all (· ≤ 255) then some os else none
  | _ => none

/-- 16-bit words of one side of an IPv6 literal (`v4ok`: a dotted IPv4 may end it). -/
def v6Side? (v4ok : Bool) (cs : List Char) : Option (List Nat) :=
  if cs.isEmpty then some [] else
  let parts := splitOn ':' cs
  let init := parts.dropLast
  match parts.getLast? with
  | none => none
  | some last => do
    let ws ← init.mapM hex16?
    if v4ok && last.contains '.' then
      match v4Octets? last with
      | some [a, b, c, d] => some (ws ++ [a * 256 + b, c * 256 + d])
      | _ => none
    else
      let w ← hex16? last
      some (ws ++ [w])

/-- Split at the first `::`. -/
def splitDouble : List Char → Option (List Char × List Char)
  | [] => none
  | [_] => none
  | ':' :: ':' :: rest => some ([], rest)
  | c :: rest => (splitDouble rest).map fun (l, r) => (c :: l, r)

/-- Bracket contents of an IPv6 literal → 16 bytes. -/
def v6Bytes? (cs : List Char) : Option (List Nat) := do
  let words ← match splitDouble cs with
    | none =>
      let ws ← v6Side? true cs
      if ws.length = 8 then some ws else none
    | some (l, r) =>
      if (splitDouble r).isSome then none else
      let lw ← v6Side? false l
      let rw ← v6Side? true r
      if lw.length + rw.length ≤ 7 then
        some (lw ++ List.replicate (8 - lw.length - rw.length) 0 ++ rw)
      else none
  some (words.flatMap fun w => [w / 256, w % 256])

/-! ## Host classification -/

inductive Host where
  | name (labels : List (List Char))
  | ip (a : Ip)
  deriving DecidableEq, Repr

/-- Literals refused beyond `NapResource.isPrivate`. -/
def extraRefused : Ip → Bool
  | .v4 a _ _ _ => 224 ≤ a
  | .v6 bs =>
    match bs with
    | 0 :: _ => true
    | 0xff :: _ => true
    | 0x20 :: 0x02 :: a :: b :: c :: d :: _ => v4Private a b c d
    | _ => false

def nameChar (c : Char) : Bool := isDigit c || ('a' ≤ c && c ≤ 'z') || c = '-'

/-- A WHATWG parser treats a host whose last label is numeric as IPv4. -/
def numericLabel (l : List Char) : Bool :=
  (!l.isEmpty && l.all isDigit) || l.take 2 == ['0', 'x']

def localSuffix (labels : List (List Char)) : Bool :=
  match labels.reverse with
  | l :: rest =>
    l == "localhost".toList || l == "local".toList ||
    (l == "arpa".toList && rest.head? == some "home".toList)
  | [] => true

/-- Host part (lowercased, trailing dot removed) → literal or name; `none` = refused. -/
def classify? (host : List Char) : Option Host :=
  match host with
  | '[' :: rest =>
    match rest.reverse with
    | ']' :: inner => (v6Bytes? inner.reverse).map (.ip ∘ .v6)
    | _ => none
  | _ =>
    match v4Octets? host with
    | some [a, b, c, d] => some (.ip (.v4 a b c d))
    | some _ => none
    | none =>
      let labels := splitOn '.' host
      if host.all (fun c => nameChar c || c = '.') then
        if labels.any List.isEmpty || labels.length < 2 then none
        else match labels.getLast? with
          | some l => if numericLabel l then none else some (.name labels)
          | none => none
      else none

/-- `wss://` URL → host classification; `none` if malformed or refused by syntax. -/
def parseHost? (url : String) : Option Host :=
  let cs := url.toList
  if cs.take 6 != "wss://".toList then none else
  let auth := (cs.drop 6).takeWhile fun c => c != '/' && c != '?' && c != '#'
  if auth.contains '@' then none else
  let auth := auth.map lower
  let (host, port) : List Char × List Char :=
    match auth with
    | '[' :: _ =>
      let h := auth.takeWhile (· != ']')
      (h ++ [']'], (auth.dropWhile (· != ']')).drop 1)
    | _ => (auth.takeWhile (· != ':'), auth.dropWhile (· != ':'))
  let portOk := match port with
    | [] => true
    | ':' :: ds => ds.all isDigit
    | _ => false
  if !portOk || !auth.all (fun c => c.toNat < 128) || auth.contains '%' then none else
  let host := match host.reverse with
    | '.' :: h => h.reverse
    | _ => host
  if host.isEmpty then none else classify? host

/-- Default relay URL policy for napplet-named relays. -/
def relayAllowed (url : String) : Bool :=
  match parseHost? url with
  | none => false
  | some (.ip a) => !isPrivate a && !extraRefused a
  | some (.name labels) => !localSuffix labels

/-- The IP literal a URL names, if its host is one. -/
def hostIp? (url : String) : Option Ip :=
  match parseHost? url with
  | some (.ip a) => some a
  | _ => none

/-- An allowed URL whose host is an IP literal names a non-private address. -/
theorem relayAllowed_not_private {url : String} {a : Ip} (h : relayAllowed url = true)
    (ha : hostIp? url = some a) : isPrivate a = false := by
  unfold hostIp? at ha
  unfold relayAllowed at h
  split at ha
  · rename_i b hb
    cases ha
    rw [hb] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1
  · cases ha

theorem relayAllowed_wss {url : String} (h : relayAllowed url = true) :
    (parseHost? url).isSome = true := by
  unfold relayAllowed at h
  split at h <;> simp_all

#guard relayAllowed "wss://relay.example.com"
#guard relayAllowed "wss://Relay.Example.COM:443/path?x=1"
#guard relayAllowed "wss://relay.example.com./"
#guard relayAllowed "wss://93.184.216.34"
#guard relayAllowed "wss://[2606:4700::1]:443"
#guard !relayAllowed "ws://relay.example.com"
#guard !relayAllowed "https://relay.example.com"
#guard !relayAllowed "wss://localhost"
#guard !relayAllowed "wss://localhost:7777"
#guard !relayAllowed "wss://relay.localhost"
#guard !relayAllowed "wss://printer.local"
#guard !relayAllowed "wss://nas.home.arpa"
#guard !relayAllowed "wss://intranet"
#guard !relayAllowed "wss://127.0.0.1"
#guard !relayAllowed "wss://192.168.0.1:8080"
#guard !relayAllowed "wss://10.0.0.5"
#guard !relayAllowed "wss://169.254.169.254"
#guard !relayAllowed "wss://224.0.0.1"
#guard !relayAllowed "wss://2130706433"
#guard !relayAllowed "wss://127.1"
#guard !relayAllowed "wss://0x7f.0.0.1"
#guard !relayAllowed "wss://010.0.0.1"
#guard !relayAllowed "wss://%31%32%37.0.0.1"
#guard !relayAllowed "wss://user@relay.example.com"
#guard !relayAllowed "wss://[::1]"
#guard !relayAllowed "wss://[::]"
#guard !relayAllowed "wss://[::ffff:192.168.0.1]"
#guard !relayAllowed "wss://[::ffff:c0a8:1]"
#guard !relayAllowed "wss://[fd00::1]"
#guard !relayAllowed "wss://[fe80::1]"
#guard !relayAllowed "wss://[fe80::1%25eth0]"
#guard !relayAllowed "wss://[2002:c0a8:1::1]"
#guard !relayAllowed "wss://[ff02::1]"
#guard !relayAllowed "wss://[64:ff9b::a00:1]"
#guard !relayAllowed "wss://"
#guard !relayAllowed "wss://relay.example.com:abc"
#guard hostIp? "wss://[2606:4700::1]" ==
  some (.v6 [0x26, 0x06, 0x47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
#guard hostIp? "wss://[::ffff:192.168.0.1]" ==
  some (.v6 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 192, 168, 0, 1])

/-! ## Template pubkey claims -/

/-- The string `pubkey` member of a raw `event` object, if any. -/
def claimedPubkey? (ev : Json) : Option String := (ev.get? "pubkey").bind Json.asStr?

/-- Add a `pubkey` member to an object (encoder side of `claimedPubkey?`). -/
def withPubkey (j : Json) (pk : Option String) : Json :=
  match j, pk with
  | .obj kvs, some p => .obj (("pubkey", .str p) :: kvs)
  | j, _ => j

theorem get?_withPubkey {j : Json} {pk : Option String} {k : String} (hk : k ≠ "pubkey") :
    (withPubkey j pk).get? k = j.get? k := by
  cases j <;> cases pk <;> simp only [withPubkey]
  simp only [Json.get?, Json.lookup]
  split <;> simp_all [Ne.symm hk]

theorem isObj_withPubkey (j : Json) (pk : Option String) : (withPubkey j pk).isObj = j.isObj := by
  cases j <;> cases pk <;> rfl

theorem ofJson?_withPubkey (j : Json) (pk : Option String) :
    EventTemplate.ofJson? (withPubkey j pk) = EventTemplate.ofJson? j := by
  simp only [EventTemplate.ofJson?, isObj_withPubkey,
    get?_withPubkey (show "kind" ≠ "pubkey" by decide),
    get?_withPubkey (show "content" ≠ "pubkey" by decide),
    get?_withPubkey (show "tags" ≠ "pubkey" by decide),
    get?_withPubkey (show "created_at" ≠ "pubkey" by decide)]

theorem claimedPubkey?_withPubkey (t : EventTemplate) (pk : Option String) :
    claimedPubkey? (withPubkey t.toJson pk) = pk := by
  cases t with
  | mk kind content tags createdAt =>
    cases pk <;> cases createdAt <;>
      simp [claimedPubkey?, withPubkey, EventTemplate.toJson, Json.mkObj, Json.get?, Json.lookup]

/-- A submitted template may be signed for `user` only if it claims no other pubkey. -/
def pubkeyOk (user : String) : Option String → Bool
  | none => true
  | some p => p == user

#guard claimedPubkey? (Json.parse! "{ \"kind\": 1, \"pubkey\": \"abc\" }") == some "abc"
#guard claimedPubkey? (Json.parse! "{ \"kind\": 1, \"pubkey\": 7 }") == none
#guard pubkeyOk "me" (some "me") && pubkeyOk "me" none && !pubkeyOk "me" (some "other")

end Napplet.Net
