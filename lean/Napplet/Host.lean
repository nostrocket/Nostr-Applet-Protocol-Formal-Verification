/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Event
import Napplet.Manifest
import Napplet.Nap.Resource

/-!
# The host interface

Everything the composed runtime (`Napplet.Runtime.step`) needs from outside the
model is in this file, each item with its contract. An implementation supplies
exactly these; everything else is defined by the Lean definitions.

The host supplies four kinds of thing.

1. **Pure functions** (`Host`): deterministic, local computations. The runtime
   calls them inside a step and uses the answer immediately.
2. **Calls** (`Call` → `Reply`): operations that complete later, because they
   touch the network, the user's signer, the wallet, a storage server or the
   user. The runtime emits `Output.call tag c`; the host later feeds back
   `Input.reply tag r`, once (or, for a relay subscription, as a stream until it
   ends). The runtime ignores replies whose tag it no longer holds, so a reply for
   a torn-down napplet or a cancelled request has no effect.
3. **Effects** (`Effect`): fire-and-forget instructions to the host (show a
   notification, open a link, stop a subscription).
4. **Events** (`HostEvent`): things the host reports unprompted (the user
   changed, the theme changed, a key binding fired).

Browser events (iframe creation, `load`, window messages, ports) and the clock
are runtime inputs (`Napplet.Runtime.Input`); their meaning is fixed by NIP-5D
and the browser.

## Global contracts

* **Atomic steps.** The host feeds one input at a time and applies the outputs
  of a step, in order, before feeding the next input. Within one step's outputs,
  `send` messages to the same port keep their order.
* **Clock.** `Input.tick now` sets the runtime clock to `now` (Unix seconds,
  non-decreasing). The host sends it whenever its clock has advanced before
  feeding another input. Timeouts are host calls that fail with a timeout reply;
  the runtime does not count time itself.
* **Persistence.** The runtime state (`RtState`) is the durable state. Fields
  documented as persistent (NAP-STORAGE values, NAP-CONFIG values and schemas,
  user preferences such as intent defaults) MUST survive reloads; the host
  stores them. Everything keyed by port or window is per session.
* **Tags.** A tag (`CallTag`) is unique among the calls the runtime has outstanding.
  The host echoes it unchanged and never invents one.
* **Standards.** Where a contract names a standard (NIP-01, NIP-04, NIP-44,
  NIP-65, BIP-340, FIPS 180-4, WHATWG MIME Sniffing, BUD-10, HTS-01, NIP-19,
  NIP-96, NIP-98, NIP-57, NWC, ContextVM, NIP-13) the host implements that
  standard; the model does not restate it.
-/

namespace Napplet

open NapResource (FetchOutcome)

/-- NIP-44 (default) or NIP-04 (fallback) payload encryption. -/
inductive Encryption where
  | nip44
  | nip04
  deriving DecidableEq, Repr, Inhabited

def Encryption.name : Encryption → String
  | .nip44 => "nip44"
  | .nip04 => "nip04"

def Encryption.ofName? : String → Option Encryption
  | "nip44" => some .nip44
  | "nip04" => some .nip04
  | _ => none

/-- A NIP-65 relay list entry. -/
structure RelayEntry where
  url : String
  read : Bool
  write : Bool
  deriving DecidableEq, Repr

/-! ## 1. Pure functions -/

/-- Deterministic host functions. -/
structure Host where
  /-- `crypto.sha256`: FIPS 180-4 SHA-256, lowercase hex.
  `crypto.verifySig`: the manifest event's NIP-01 `id` is the SHA-256 of its
  serialisation and its `sig` is a valid BIP-340 signature by `pubkey` over `id`. -/
  crypto : Crypto
  /-- NIP-01 id check plus BIP-340 signature check for any event. -/
  verifyEvent : NostrEvent → Bool
  /-- WHATWG MIME Sniffing over the bytes alone (never an upstream `Content-Type`).
  Returns an essence such as `image/png`; `application/octet-stream` when unknown. -/
  sniff : Bytes → String
  /-- Rasterise SVG to PNG or WebP in an isolated context with no network access,
  within the SVG caps of NAP-RESOURCE. `none` on failure or cap overflow. -/
  rasterize : Bytes → Option Bytes
  /-- Does napplet-supplied event content look like NIP-04 (`<base64>?iv=<base64>`) or
  NIP-44 (version-prefixed base64 payload) ciphertext? Used to refuse signing
  ciphertext a napplet supplied (NIP-5D §Security 7). May over-approximate. -/
  looksCiphertext : String → Bool
  /-- Which scheme, if any, encrypts this incoming event to the user (NIP-04 kind 4,
  NIP-44 payloads per NIP-17/NIP-59). `none` for plaintext events. -/
  encryptedWith : NostrEvent → Option Encryption
  /-- NAP-UPLOAD: metadata stripping (for example EXIF) the shell applies unless the
  request sets `noTransform`. The identity function is a valid choice. -/
  transform : Bytes → Bytes
  /-- NAP-SHELL `services`: service names this shell reports. -/
  services : List String := []

/-! ## 2. Calls and replies -/

/-- A call's correlation tag: the issuing domain and a number unique among that
domain's outstanding calls. -/
structure CallTag where
  domain : Domain
  n : Nat
  deriving DecidableEq, Repr

/-- Operations that complete later with a `Reply`. -/
inductive Call where
  /-- Sign with the user's key (local key, NIP-07 or NIP-46). Reply: `signed`.
  Contract: `signed (some e)` has `e.pubkey, e.createdAt, e.kind, e.tags, e.content`
  equal to the input, `e.id` its NIP-01 id and `e.sig` a BIP-340 signature by the
  user's key; `signed none` if there is no signer or it refused. -/
  | sign (ev : UnsignedEvent)
  /-- Encrypt `plaintext` from the user to `recipient` (NIP-44 v2 or NIP-04).
  Reply: `text (some ciphertext)`, or `text none` on failure. The host MUST NOT fall
  back to another scheme on its own. -/
  | encrypt (scheme : Encryption) (recipient : Pubkey) (plaintext : String)
  /-- Decrypt an incoming event's `content` with the user's key. Reply: `text`. -/
  | decrypt (scheme : Encryption) (ev : NostrEvent)
  /-- Fetch one URL for NAP-RESOURCE. Reply: `fetched`. Contract: the host resolves
  the scheme (`https:` with DNS; `blossom:` per BUD-10 from servers it chooses;
  `nostr:` one NIP-19 hop; `hashtree:`/`htree:` per HTS-01 with root, node, chunk
  and CHK checks; `data:` locally) and reports every address it connected to, in
  order, *before* connecting to the next; it stops at the runtime's redirect cap.
  It never sends hashtree keys to relays, servers or peers. -/
  | fetch (url : String)
  /-- Ask the user. Reply: `decision`. The prompt shows the requesting napplet's
  verified identity and the `details`; the host never answers on the user's
  behalf except from a rule the user configured. Prompting MUST NOT block other
  inputs. -/
  | prompt (domain : Domain) (kind : String) (details : Json)
  /-- Open a relay subscription with NIP-01 filters, on the shell's pool or on the
  listed relays. Replies (a stream, same tag): `event` per matching stored or live
  event (NIP-01 signature already verified), one `eose` when stored events are
  exhausted, and `closed` if the pool ends it. Stopped by `Effect.unsubscribe`. -/
  | subscribe (filters : List Json) (relays : Option (List String))
  /-- Send a signed event to the shell's pool or to the listed relays.
  Reply: `published acks` with one `(relay, accepted)` per relay tried. -/
  | publish (ev : NostrEvent) (relays : Option (List String))
  /-- Resolve a pubkey's NIP-65 relay list (from cache or relays).
  Reply: `relayList (some entries)`, or `relayList none` if unavailable. -/
  | relayList (pubkey : Pubkey)
  /-- A NAP-specific host operation, named `op` in domain `domain`. Its arguments,
  reply (`json`) and contract are listed in the table of NAP operations below. -/
  | nap (domain : Domain) (op : String) (args : Json)
  deriving DecidableEq, Repr

/-- Replies to calls. -/
inductive Reply where
  | signed (ev : Option NostrEvent)
  | text (s : Option String)
  | fetched (o : FetchOutcome)
  | decision (allowed : Bool) (choice : Option String)
  /-- Subscription stream: one event and the relay it was observed on. -/
  | event (ev : NostrEvent) (relay : String)
  | eose
  | closed (reason : Option String)
  | published (acks : List (String × Bool))
  | relayList (entries : Option (List RelayEntry))
  | json (j : Json)

/-! ## 3. Effects -/

/-- Fire-and-forget instructions to the host. -/
inductive Effect where
  /-- Stop the relay subscription opened under this tag. -/
  | unsubscribe (tag : CallTag)
  /-- Abandon an outstanding call (for example a cancelled fetch); a later reply is
  ignored anyway. -/
  | cancel (tag : CallTag)
  /-- A NAP-specific instruction, listed in the table of NAP operations below. -/
  | nap (domain : Domain) (op : String) (args : Json)
  deriving DecidableEq, Repr

/-! ## 4. Events -/

/-- Things the host reports unprompted. -/
inductive HostEvent where
  /-- The shell user changed; `""` means signed out or no signer (NAP-IDENTITY). -/
  | userChanged (pubkey : String)
  /-- The active theme changed (NAP-THEME `Theme` JSON), or there is none. -/
  | themeChanged (theme : Option Json)
  /-- A NAP-specific event, listed in the table of NAP operations below. -/
  | nap (domain : Domain) (ev : String) (args : Json)
  deriving DecidableEq, Repr

/-! ## NAP operations

`Call.nap`, `Effect.nap` and `HostEvent.nap` entries, by domain. Each row gives the
operation name, its JSON arguments, the reply, and the contract. (Filled in per NAP.)
-/

end Napplet
