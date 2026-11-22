/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Host
import Napplet.Shell
import Napplet.Nap.Storage

/-!
# Shared vocabulary for the per-NAP runtime components

Each NAP's runtime component (`Napplet.Run.*`) has the same shape:

* `St`, `St.init`: the component's state.
* `decode : Json → Decoded Req`: a wire request to a typed request.
* `encodeReq : Req → Json`: the request as the napplet-side binding sends it.
* `handle : Host → World → Ctx → St → Req → St × List Eff`: one request from the
  authenticated endpoint `cx`.
* `onReply`, `onEvent`: host replies and host events.
* `drop : St → PortId → St × List Eff`: teardown of one endpoint.
* `mentions : St → PortId → Bool`: whether any per-endpoint state refers to a port.

`Runtime` composes them. The endpoint context `Ctx` is derived from the shell's
binding by one function, `Ctx.ofBinding`; components never see anything the
napplet sent about its own identity.
-/

namespace Napplet

/-- One authenticated napplet endpoint, as the runtime knows it. -/
structure Ctx where
  port : PortId
  window : WindowId
  identity : Identity
  exposed : List Domain
  /-- Host-chosen stable instance identifier (NAP-STORAGE §Instance Scope). -/
  inst : Nat
  /-- The NAP-INC endpoint identifier the shell's policy assigns to this window, if any
  (`Runtime.Config.endpointName`); otherwise `endpoint-<window>`. -/
  endpoint : Option String := none
  deriving DecidableEq, Repr

namespace Ctx

/-- The single derivation of an endpoint context from a shell binding. -/
def ofBinding (p : PortId) (b : Binding) (inst : Nat) (endpoint : Option String := none) : Ctx :=
  { port := p, window := b.window, identity := b.identity, exposed := b.exposed, inst, endpoint }

/-- NAP-INC endpoint identifier: opaque, unique per live endpoint, never reused in a
runtime session. NAP-INC: "Identifier encoding is runtime policy." The default is
`endpoint-<window>` (window ids are never reused, modelling decision 4); a shell may
name windows instead through `Runtime.Config.endpointName`, whose contract is to be
injective and never to produce a default-form name. -/
def endpointId (c : Ctx) : String := c.endpoint.getD ("endpoint-" ++ toString c.window)

/-- NAP-INTENT catalog identifier of the napplet behind this endpoint. -/
def catalogId (c : Ctx) : String := c.identity.catalogId

/-- NAP-STORAGE / NAP-RESOURCE / NAP-CONFIG scope context. -/
def storage (c : Ctx) : NapStorage.EndpointCtx := .ofIdentity c.identity c.inst

end Ctx

/-- What every component may read about the rest of the runtime. -/
structure World where
  now : Nat
  /-- Every bound endpoint. -/
  live : List Ctx
  /-- The shell user's pubkey, `""` when none (NAP-IDENTITY). -/
  user : String

namespace World

def bound (w : World) (p : PortId) : Prop := ∃ c ∈ w.live, c.port = p

def byPort? (w : World) (p : PortId) : Option Ctx := w.live.find? (·.port == p)

def byEndpointId? (w : World) (e : String) : Option Ctx := w.live.find? (·.endpointId == e)

end World

/-- A component's output. -/
inductive Eff where
  /-- Post this JSON message on a bound port. -/
  | send (to : PortId) (msg : Json)
  | call (tag : CallTag) (c : Call)
  | effect (e : Effect)
  deriving DecidableEq, Repr

/-- Outcome of decoding one wire message of a domain. -/
inductive Decoded (α : Type) where
  | ok (a : α)
  /-- A recognised type with a malformed payload. The listed replies (an error
  result, when the request carries a usable `id`) go back to the sender. -/
  | reject (replies : List Json)
  /-- Not a type this NAP defines: silently ignored (NIP-5D §Wire Format). -/
  | unknown
  deriving Repr

/-- The request's `id`, when it is a string. -/
def reqId? (j : Json) : Option String := j.getStr? "id"

/-- An error result for a malformed request: `{type: <resultType>, id, error}`.
Without a usable `id` there is nothing to correlate, so nothing is sent
(modelling decision 31). -/
def errorReply (resultType : String) (j : Json) (error : String) : List Json :=
  match reqId? j with
  | some id => [Json.msg resultType [("id", some (.str id)), ("error", some (.str error))]]
  | none => []

end Napplet
