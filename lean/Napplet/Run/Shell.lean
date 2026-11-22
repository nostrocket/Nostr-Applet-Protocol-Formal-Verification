/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Shell

/-!
# NAP-SHELL runtime component

Upstream: `napplet/naps` `master`, `naps/NAP-SHELL.md` at `377bf939`, with PR #142
(`nap-shell-compatibility` at `b9b0b7e3`): `domains()` and `check(manifest)`.

Wire: `shell.ready` (napplet → runtime, no fields, no `id`) and
`shell.init {capabilities: {domains}, services}` (runtime → napplet, no `id`);
`shell.check {id, manifest}` (napplet → runtime) and
`shell.check.result {id, compatibility | error}` (runtime → napplet), where
`compatibility` is `{status, missingRequired, missingOptional}`.

`shell.check` answers each request with a text `id` with exactly one result on the
requesting endpoint. The manifest must be a NIP-01 event object whose signature the
host verifies (`Host.verifyEvent`) and which passes every NIP-5D manifest rule but the
artifact hash comparison (`checkManifestEvent`); otherwise `error: "invalid manifest"`.
The target identity takes the signed `x` value as its artifact hash, and its `R` and
`O` names are assessed (`NapShell.assess`) against `exposedFor` for that identity under
the shell's configuration (`Runtime.Config.shell`, the same policy load uses), with
`ShellConfig.undisclosed` as unknown. The result depends only on the configuration and
the manifest: not on the caller's exposure, grants, or whether `shell.init` was sent.
No host call or effect is made: nothing is fetched, installed, launched, prompted or
granted. A request without a text `id` is dropped (modelling decision 31).

The runtime answers the first `shell.ready` on an endpoint with exactly one
`shell.init` describing that endpoint's own exposure and the host's services;
later `shell.ready` messages produce nothing. Extra members on `shell.ready` are
ignored (it "carries no identity or capability claims").
-/

namespace Napplet.Run.Shell

structure St where
  /-- Endpoints that already received `shell.init`. -/
  sent : List PortId
  /-- The shell's load policy, read by `check`. -/
  cfg : ShellConfig

def St.init (cfg : ShellConfig := { supported := [], policy := fun _ => [] }) : St := ⟨[], cfg⟩

inductive Req where
  | ready
  | check (id : String) (manifest : Json)
  deriving DecidableEq, Repr

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some "shell.ready" => .ok .ready
  | some "shell.check" =>
    match reqId? j with
    | some id => .ok (.check id ((j.get? "manifest").getD .null))
    | none => .reject []
  | _ => .unknown

def encodeReq : Req → Json
  | .ready => Json.msg "shell.ready" []
  | .check id m => Json.msg "shell.check" [("id", some (.str id)), ("manifest", some m)]

/-! ### `shell.check` -/

/-- The parts of a NIP-01 event the manifest rules read. -/
def manifestOf (e : NostrEvent) : ManifestEvent :=
  { kind := e.kind, pubkey := e.pubkey, content := e.content, id := e.id,
    tags := e.tags.filterMap fun t => t.head?.map fun n => ⟨n, t.drop 1⟩ }

/-- Validate the target manifest without its artifact. The signature is checked over
the full event by the host; the remaining manifest rules by `checkManifestEvent`. -/
def target? (h : Host) (j : Json) : Option VerifiedManifest :=
  match NostrEvent.ofJson? j with
  | none => none
  | some e =>
    if h.verifyEvent e then
      match checkManifestEvent { h.crypto with verifySig := fun _ => true } (manifestOf e) with
      | .ok v => some v
      | .error _ => none
    else none

def check (h : Host) (cfg : ShellConfig) (j : Json) : Except String NapShell.Compatibility :=
  match target? h j with
  | none => .error "invalid manifest"
  | some v =>
    .ok (NapShell.assess (exposedFor cfg v.identity) (cfg.undisclosed v.identity) v.required v.optional)

def compatJson (c : NapShell.Compatibility) : Json :=
  .obj [("status", .str c.status.name), ("missingRequired", Json.strs c.missingRequired),
        ("missingOptional", Json.strs c.missingOptional)]

def checkResult (id : String) : Except String NapShell.Compatibility → Json
  | .ok c => Json.msg "shell.check.result" [("id", some (.str id)), ("compatibility", some (compatJson c))]
  | .error e => Json.msg "shell.check.result" [("id", some (.str id)), ("error", some (.str e))]

def envJson (env : NapShell.ShellEnvironment) : Json :=
  Json.msg "shell.init"
    [("capabilities", some (.obj [("domains", Json.strs (env.capabilities.map Domain.name))])),
     ("services", some (Json.strs env.services))]

def environment (h : Host) (cx : Ctx) : NapShell.ShellEnvironment :=
  { capabilities := cx.exposed, services := h.services }

def handle (h : Host) (_w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .ready =>
    if cx.port ∈ s.sent then (s, [])
    else ({ s with sent := cx.port :: s.sent }, [.send cx.port (envJson (environment h cx))])
  | .check id m => (s, [.send cx.port (checkResult id (check h s.cfg m))])

def onReply (_h : Host) (_w : World) (s : St) (_n : Nat) (_r : Reply) : St × List Eff := (s, [])

def onEvent (_h : Host) (_w : World) (s : St) (_e : HostEvent) : St × List Eff := (s, [])

def drop (s : St) (p : PortId) : St × List Eff := ({ s with sent := s.sent.filter (· != p) }, [])

def mentions (s : St) (p : PortId) : Bool := s.sent.contains p

/-! ### Properties -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]

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
  cases r with
  | check => exact .inl hm
  | ready =>
  simp only [handle] at hm
  split at hm
  · exact .inl hm
  · simp [mentions] at hm ⊢
    rcases hm with rfl | hm
    · exact .inr ⟨cx, hcx, rfl⟩
    · exact .inl hm

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := .inl hm

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := .inl hm

/-! ### `shell.check` properties (PR #142) -/

/-- "the runtime MUST reply to that endpoint with the same `id` and exactly one of
`compatibility` or `error`": one message, to the requester, nothing else (no host call,
no effect: nothing fetched, installed, launched, prompted or granted), state unchanged. -/
theorem check_one_reply (h : Host) (w : World) (cx : Ctx) (s : St) (id : String) (m : Json) :
    handle h w cx s (.check id m) = (s, [.send cx.port (checkResult id (check h s.cfg m))]) ∧
    (checkResult id (check h s.cfg m)).getStr? "id" = some id ∧
    (((checkResult id (check h s.cfg m)).get? "compatibility").isSome ≠
      ((checkResult id (check h s.cfg m)).get? "error").isSome) := by
  refine ⟨rfl, ?_⟩
  cases check h s.cfg m <;>
    simp [checkResult, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

/-- The assessment ignores the caller: its exposure, identity, grants and whether it
received `shell.init` ("independently of the caller's exposed domains"; "MUST work
without `shell.init`"; "MUST NOT reveal another napplet's existing grants"). -/
theorem check_caller_independent (h : Host) (w w' : World) (cx cx' : Ctx) (s s' : St) (id : String)
    (m : Json) (hc : s.cfg = s'.cfg) :
    (handle h w cx s (.check id m)).2.map (fun | .send _ j => some j | _ => none) =
    (handle h w' cx' s' (.check id m)).2.map (fun | .send _ j => some j | _ => none) := by
  simp [handle, hc]

/-- A manifest the host does not verify, or that breaks a manifest rule, is
`"invalid manifest"`. -/
theorem check_invalid (h : Host) (cfg : ShellConfig) (j : Json) (hv : target? h j = none) :
    check h cfg j = .error "invalid manifest" := by
  simp [check, hv]

/-- A valid manifest is assessed for the target identity under the load policy: the
assessed exposure is exactly what loading that identity would expose, and the identity's
artifact hash is the signed `x` value. -/
theorem check_valid (h : Host) (cfg : ShellConfig) (j : Json) (v : VerifiedManifest)
    (hv : target? h j = some v) :
    check h cfg j = .ok (NapShell.assess (exposedFor cfg v.identity) (cfg.undisclosed v.identity)
      v.required v.optional) ∧
    ∃ e, NostrEvent.ofJson? j = some e ∧ h.verifyEvent e = true ∧
      xValue? (manifestOf e) = some v.identity.artifactHash := by
  refine ⟨by simp [check, hv], ?_⟩
  unfold target? at hv
  split at hv
  · cases hv
  · rename_i e he
    split at hv
    · rename_i hve
      split at hv
      · rename_i v' hok
        cases hv
        exact ⟨e, he, hve, (checkManifestEvent_ok hok).2⟩
      · cases hv
    · cases hv

/-- Whatever bytes the load check would accept for this manifest, `check` sees the same
verified manifest, so it assesses the identity load would bind. -/
theorem check_agrees_with_load (h : Host) (j : Json) (e : NostrEvent) (bytes : Bytes)
    (v : VerifiedManifest) (he : NostrEvent.ofJson? j = some e) (hve : h.verifyEvent e = true)
    (hl : checkManifest h.crypto (manifestOf e) bytes = .ok v) : target? h j = some v := by
  have hsig := (checkManifest_ok hl).1
  have hl' : checkManifest { h.crypto with verifySig := fun _ => true } (manifestOf e) bytes = .ok v := by
    rw [checkManifest_sig_true hsig]; exact hl
  simp [target?, he, hve, checkManifestEvent_agrees hl']

#guard decode (Json.parse! "{ \"type\": \"shell.ready\" }") matches .ok .ready
#guard decode (Json.parse! "{ \"type\": \"shell.hello\" }") matches .unknown
#guard Json.same (envJson { capabilities := [.shell, .theme], services := [] })
  (Json.parse! "{ \"type\": \"shell.init\", \"capabilities\": { \"domains\": [\"shell\", \"theme\"] }, \"services\": [] }")

-- shell.check
#guard decode (Json.parse! "{ \"type\": \"shell.check\", \"id\": \"c1\", \"manifest\": {} }") matches .ok (.check "c1" _)
#guard decode (Json.parse! "{ \"type\": \"shell.check\", \"manifest\": {} }") matches .reject []
#guard decode (Json.parse! "{ \"type\": \"shell.check\", \"id\": \"c1\" }") matches .ok (.check "c1" .null)

private def hst (sig : Bool) : Host :=
  { crypto := { sha256 := fun _ => "", verifySig := fun _ => true }, verifyEvent := fun _ => sig,
    sniff := fun _ => "", rasterize := fun _ => none, looksCiphertext := fun _ => false,
    encryptedWith := fun _ => none, transform := id }
private def target (tags : String) : Json := Json.parse! ("{ \"id\": \"e1\", \"pubkey\": \"" ++
  String.ofList (List.replicate 64 'a') ++ "\", \"created_at\": 1, \"kind\": 35129, \"content\": \"Chess\", \"sig\": \"s\", \"tags\": [[\"d\", \"chess\"], [\"x\", \"" ++
  String.ofList (List.replicate 64 'b') ++ "\"]" ++ tags ++ "] }")
-- the shell implements relay but its policy gives this target only theme and storage
private def cfgT : ShellConfig :=
  { supported := [.relay, .theme, .storage], policy := fun _ => [.theme, .storage] }
private def ctx1 : Ctx :=
  { port := 1, window := 10, identity := { dTag := some "a", artifactHash := "h" },
    exposed := [.shell, .relay], inst := 0 }
private def w0 : World := { now := 0, live := [ctx1], user := "" }
private def sendsOne (es : List Eff) (exp : String) : Bool :=
  match es with
  | [.send 1 m] => Json.same m (Json.parse! exp)
  | _ => false

-- the upstream example: a target requiring `relay` (exposed to the caller, not to the target)
#guard sendsOne (handle (hst true) w0 ctx1 (St.init cfgT) (.check "c1" (target ", [\"R\", \"relay\"]"))).2
  "{ \"type\": \"shell.check.result\", \"id\": \"c1\", \"compatibility\": {
     \"status\": \"incompatible\", \"missingRequired\": [\"relay\"], \"missingOptional\": []
   } }"
#guard Json.same (checkResult "c1" (.ok ⟨.incompatible, ["relay"], []⟩)) (Json.parse! "{ \"type\": \"shell.check.result\", \"id\": \"c1\", \"compatibility\": {
     \"status\": \"incompatible\", \"missingRequired\": [\"relay\"], \"missingOptional\": []
   } }")
-- compatible; an unknown optional domain is listed once; required order kept
#guard sendsOne (handle (hst true) w0 ctx1 (St.init cfgT) (.check "c2"
    (target ", [\"R\", \"theme\"], [\"O\", \"chat\"], [\"O\", \"chat\"], [\"O\", \"storage\"]"))).2
  "{ \"type\": \"shell.check.result\", \"id\": \"c2\", \"compatibility\": { \"status\": \"compatible\", \"missingRequired\": [], \"missingOptional\": [\"chat\"] } }"
-- undisclosed availability is unknown, never incompatible
#guard sendsOne (handle (hst true) w0 ctx1 (St.init { cfgT with undisclosed := fun _ => [.relay] }) (.check "c3"
    (target ", [\"R\", \"relay\"]"))).2
  "{ \"type\": \"shell.check.result\", \"id\": \"c3\", \"compatibility\": { \"status\": \"unknown\", \"missingRequired\": [], \"missingOptional\": [] } }"
-- bad signature, malformed event, missing manifest, two `x` tags: "invalid manifest"
#guard sendsOne (handle (hst false) w0 ctx1 (St.init cfgT) (.check "c4" (target ""))).2
  "{ \"type\": \"shell.check.result\", \"id\": \"c4\", \"error\": \"invalid manifest\" }"
#guard sendsOne (handle (hst true) w0 ctx1 (St.init cfgT) (.check "c5" (Json.parse! "{ \"kind\": 35129 }"))).2
  "{ \"type\": \"shell.check.result\", \"id\": \"c5\", \"error\": \"invalid manifest\" }"
#guard sendsOne (handle (hst true) w0 ctx1 (St.init cfgT) (.check "c6" .null)).2
  "{ \"type\": \"shell.check.result\", \"id\": \"c6\", \"error\": \"invalid manifest\" }"
#guard sendsOne (handle (hst true) w0 ctx1 (St.init cfgT) (.check "c7" (target ", [\"x\", \"cc\"]"))).2
  "{ \"type\": \"shell.check.result\", \"id\": \"c7\", \"error\": \"invalid manifest\" }"
-- no shell.init needed, and the state is untouched
#guard (handle (hst true) w0 ctx1 (St.init cfgT) (.check "c1" (target ""))).1.sent == []

end Napplet.Run.Shell
