/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Identity

/-!
# NAP-IDENTITY runtime component

Upstream: `napplet/naps` `master`, `naps/NAP-IDENTITY.md` at `377bf939`.

Wire (napplet → shell, each `{id}` plus `listType` for `getList`):
`identity.getPublicKey`, `getRelays`, `getProfile`, `getFollows`, `getList`,
`getZaps`, `getMutes`, `getBlocked`, `getBadges`. Results are `<type>.result` with
`id` and one primary field: `pubkey`, `relays` (map url → `{read, write}`),
`profile` (object or `null`), `pubkeys`, `entries`, `zaps`, `badges`; all but
`getPublicKey` may add `error`, and then the primary field holds its default
(`{}`, `null` or `[]`). Push: `identity.changed {pubkey}` to every endpoint with
`identity` exposed when the user changes, `""` on sign-out.

`getPublicKey` is answered at once from the runtime's user (it MUST always
succeed and never carries `error`). Every other query is a host call
`Call.nap .identity "query" {query, listType?}` answered from the shell's cache
or relays; its reply `json` is an object holding the primary field and optionally
`error`. A primary field of the wrong JSON type is replaced by its default.
-/

namespace Napplet.Run.Identity

open NapIdentity

abbrev Req := IdentityReq

structure Pending where
  n : Nat
  port : PortId
  req : Req
  deriving DecidableEq, Repr

structure St where
  pending : List Pending
  next : Nat

def St.init : St := ⟨[], 0⟩

/-! ### Codec -/

def opName : Req → String
  | .getPublicKey _ => "getPublicKey" | .getRelays _ => "getRelays"
  | .getProfile _ => "getProfile" | .getFollows _ => "getFollows" | .getList _ _ => "getList"
  | .getZaps _ => "getZaps" | .getMutes _ => "getMutes" | .getBlocked _ => "getBlocked"
  | .getBadges _ => "getBadges"

def typeOf : Req → String
  | .getPublicKey _ => "identity.getPublicKey" | .getRelays _ => "identity.getRelays"
  | .getProfile _ => "identity.getProfile" | .getFollows _ => "identity.getFollows"
  | .getList _ _ => "identity.getList" | .getZaps _ => "identity.getZaps"
  | .getMutes _ => "identity.getMutes" | .getBlocked _ => "identity.getBlocked"
  | .getBadges _ => "identity.getBadges"

def requestTypes : List String :=
  ["identity.getPublicKey", "identity.getRelays", "identity.getProfile", "identity.getFollows",
   "identity.getList", "identity.getZaps", "identity.getMutes", "identity.getBlocked",
   "identity.getBadges"]

def ofType? (t id : String) (lt : Option String) : Option Req :=
  match t, lt with
  | "identity.getPublicKey", _ => some (.getPublicKey id)
  | "identity.getRelays", _ => some (.getRelays id)
  | "identity.getProfile", _ => some (.getProfile id)
  | "identity.getFollows", _ => some (.getFollows id)
  | "identity.getList", some l => some (.getList id l)
  | "identity.getZaps", _ => some (.getZaps id)
  | "identity.getMutes", _ => some (.getMutes id)
  | "identity.getBlocked", _ => some (.getBlocked id)
  | "identity.getBadges", _ => some (.getBadges id)
  | _, _ => none

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some t =>
    if t ∉ requestTypes then .unknown else
    match reqId? j with
    | none => .reject []
    | some id =>
      match ofType? t id (j.getStr? "listType") with
      | some r => .ok r
      | none => .reject (errorReply (resultType t) j "invalid request")
  | none => .unknown

def encodeReq (r : Req) : Json :=
  Json.msg (typeOf r)
    [("id", some (.str r.id)),
     ("listType", match r with | .getList _ l => some (.str l) | _ => none)]

/-- Primary result field and its default. -/
def primary : Req → String × Json
  | .getPublicKey _ => ("pubkey", .str "")
  | .getRelays _ => ("relays", .obj [])
  | .getProfile _ => ("profile", .null)
  | .getFollows _ | .getMutes _ | .getBlocked _ => ("pubkeys", .arr [])
  | .getList _ _ => ("entries", .arr [])
  | .getZaps _ => ("zaps", .arr [])
  | .getBadges _ => ("badges", .arr [])

/-- Does a host value have the primary field's JSON type? -/
def typeOk : Json → Json → Bool
  | .obj _, .obj _ => true
  | .null, .null => true
  | .null, .obj _ => true
  | .arr _, .arr _ => true
  | .str _, .str _ => true
  | _, _ => false

/-- Build `<type>.result` from the host's answer. -/
def resultJson (r : Req) (answer : Json) : Json :=
  let (f, d) := primary r
  let v := match answer.get? f with
    | some x => if typeOk d x then x else d
    | none => d
  Json.msg (resultType (typeOf r))
    [("id", some (.str r.id)), (f, some v), ("error", (answer.getStr? "error").map .str)]

def pubkeyResult (id pk : String) : Json :=
  Json.msg "identity.getPublicKey.result" [("id", some (.str id)), ("pubkey", some (.str pk))]

def changedJson (pk : String) : Json := Json.msg "identity.changed" [("pubkey", some (.str pk))]

/-! ### Component -/

def handle (_h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) : St × List Eff :=
  match r with
  | .getPublicKey id => (s, [.send cx.port (pubkeyResult id w.user)])
  | _ =>
    ({ pending := ⟨s.next, cx.port, r⟩ :: s.pending, next := s.next + 1 },
     [.call ⟨.identity, s.next⟩ (.nap .identity "query"
        (Json.mkObj [("query", some (.str (opName r))),
                     ("listType", match r with | .getList _ l => some (.str l) | _ => none)]))])

def onReply (_h : Host) (_w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.pending.find? (·.n == n) with
  | none => (s, [])
  | some p =>
    let answer := match rep with | .json j => j | _ => .obj [("error", .str "relay timeout")]
    ({ s with pending := s.pending.filter (·.n != n) }, [.send p.port (resultJson p.req answer)])

def onEvent (_h : Host) (w : World) (s : St) : HostEvent → St × List Eff
  | .userChanged pk =>
    (s, (onUserChange (w.live.map fun c => (c.port, c.exposed)) w.user pk).filterMap fun o =>
      match o with
      | .changed to k => some (.send to (changedJson k))
      | _ => none)
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with pending := s.pending.filter (·.port != p) }, [])

def mentions (s : St) (p : PortId) : Bool := s.pending.any (·.port == p)

/-! ### Properties -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r <;> simp [decode, encodeReq, typeOf, requestTypes, ofType?, Json.msg, Json.mkObj,
    Json.getStr?, Json.get?, Json.lookup, reqId?, IdentityReq.id]

/-- `identity.getPublicKey.result` never carries `error` and reports the runtime's user. -/
theorem getPublicKey_no_error (h : Host) (w : World) (cx : Ctx) (s : St) (id : String) :
    handle h w cx s (.getPublicKey id) = (s, [.send cx.port (pubkeyResult id w.user)]) ∧
    (pubkeyResult id w.user).get? "error" = none := by
  simp [handle, pubkeyResult, Json.msg, Json.mkObj, Json.get?, Json.lookup]

theorem resultJson_id (r : Req) (a : Json) : (resultJson r a).getStr? "id" = some r.id := by
  unfold resultJson
  generalize a.getStr? "error" = e
  generalize (match a.get? (primary r).1 with
    | some x => if typeOk (primary r).2 x = true then x else (primary r).2
    | none => (primary r).2) = v
  cases r <;> cases e <;> simp [primary, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

/-- A reply reaches only the endpoint that asked, with that request's `id`. -/
theorem reply_to_requester (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply)
    (p : PortId) (m : Json) (hm : Eff.send p m ∈ (onReply h w s n rep).2) :
    ∃ q ∈ s.pending, q.n = n ∧ q.port = p ∧ m.getStr? "id" = some q.req.id := by
  simp only [onReply] at hm
  split at hm
  · simp at hm
  · rename_i q hq
    simp only [List.mem_singleton, Eff.send.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    have := List.find?_some hq
    simp at this
    exact ⟨q, List.mem_of_find?_eq_some hq, this, rfl, resultJson_id _ _⟩

/-- A late reply (after teardown dropped the request) produces nothing. -/
theorem late_reply_dropped (h : Host) (w : World) (s : St) (p : PortId) (n : Nat) (rep : Reply)
    (hp : ∀ q ∈ s.pending, q.n = n → q.port = p) : (onReply h w (drop s p).1 n rep).2 = [] := by
  simp only [onReply, drop]
  split
  · rfl
  · rename_i q hq
    have hm := List.mem_of_find?_eq_some hq
    have hn := List.find?_some hq
    simp at hm hn
    exact absurd (hp q hm.1 hn) hm.2

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp [drop, mentions] at h ⊢
  obtain ⟨x, hx, -, hq⟩ := h
  exact ⟨x, hx, hq⟩

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  cases r <;> simp [handle, mentions] at hm ⊢ <;>
    first | exact .inl hm | (rcases hm with rfl | hm <;> first | exact .inr ⟨cx, hcx, rfl⟩ | exact .inl hm)

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  simp only [onReply] at hm
  split at hm
  · exact hm
  · simp [mentions] at hm ⊢
    obtain ⟨x, hx, hq⟩ := hm
    exact ⟨x, hx, hq.2⟩

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  cases e <;> simpa [onEvent] using hm

#guard decode (Json.parse! "{ \"type\": \"identity.getList\", \"id\": \"q6\", \"listType\": \"bookmarks\" }") matches .ok (.getList "q6" "bookmarks")
#guard decode (Json.parse! "{ \"type\": \"identity.sign\", \"id\": \"q6\" }") matches .unknown
#guard Json.same (resultJson (.getFollows "q10") (Json.parse! "{\"error\": \"relay timeout\"}"))
  (Json.parse! "{ \"type\": \"identity.getFollows.result\", \"id\": \"q10\", \"pubkeys\": [], \"error\": \"relay timeout\" }")

end Napplet.Run.Identity
