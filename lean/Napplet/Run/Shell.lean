/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Shell

/-!
# NAP-SHELL runtime component

Upstream: `napplet/naps` `master`, `naps/NAP-SHELL.md` at `377bf939`.

Wire: `shell.ready` (napplet → runtime, no fields, no `id`) and
`shell.init {capabilities: {domains}, services}` (runtime → napplet, no `id`).

The runtime answers the first `shell.ready` on an endpoint with exactly one
`shell.init` describing that endpoint's own exposure and the host's services;
later `shell.ready` messages produce nothing. Extra members on `shell.ready` are
ignored (it "carries no identity or capability claims").
-/

namespace Napplet.Run.Shell

structure St where
  /-- Endpoints that already received `shell.init`. -/
  sent : List PortId

def St.init : St := ⟨[]⟩

inductive Req where
  | ready
  deriving DecidableEq, Repr

def decode (j : Json) : Decoded Req :=
  if j.getStr? "type" = some "shell.ready" then .ok .ready else .unknown

def encodeReq : Req → Json
  | .ready => Json.msg "shell.ready" []

def envJson (env : NapShell.ShellEnvironment) : Json :=
  Json.msg "shell.init"
    [("capabilities", some (.obj [("domains", Json.strs (env.capabilities.map Domain.name))])),
     ("services", some (Json.strs env.services))]

def environment (h : Host) (cx : Ctx) : NapShell.ShellEnvironment :=
  { capabilities := cx.exposed, services := h.services }

def handle (h : Host) (_w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .ready =>
    if cx.port ∈ s.sent then (s, [])
    else (⟨cx.port :: s.sent⟩, [.send cx.port (envJson (environment h cx))])

def drop (s : St) (p : PortId) : St × List Eff := (⟨s.sent.filter (· != p)⟩, [])

def mentions (s : St) (p : PortId) : Bool := s.sent.contains p

/-! ### Properties -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r; simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

/-- The first `shell.ready` yields exactly one `shell.init` with this endpoint's own
domains; a second yields nothing. -/
theorem init_exactly_once (h : Host) (w : World) (cx : Ctx) (s : St) (hs : cx.port ∉ s.sent) :
    (handle h w cx s .ready).2 = [.send cx.port (envJson (environment h cx))] ∧
    (handle h w cx (handle h w cx s .ready).1 .ready).2 = [] := by
  simp [handle, hs]

theorem init_only_own_domains (h : Host) (cx : Ctx) :
    (environment h cx).capabilities = cx.exposed := rfl

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp [drop, mentions] at h ⊢; exact h.1

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  cases r
  simp only [handle] at hm
  split at hm
  · exact .inl hm
  · simp [mentions] at hm ⊢
    rcases hm with rfl | hm
    · exact .inr ⟨cx, hcx, rfl⟩
    · exact .inl hm

#guard decode (Json.parse! "{ \"type\": \"shell.ready\" }") matches .ok .ready
#guard decode (Json.parse! "{ \"type\": \"shell.hello\" }") matches .unknown
#guard Json.same (envJson { capabilities := [.shell, .theme], services := [] })
  (Json.parse! "{ \"type\": \"shell.init\", \"capabilities\": { \"domains\": [\"shell\", \"theme\"] }, \"services\": [] }")

end Napplet.Run.Shell
