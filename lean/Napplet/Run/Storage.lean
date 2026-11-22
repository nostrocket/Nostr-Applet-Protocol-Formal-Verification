/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component

/-!
# NAP-STORAGE runtime component

Upstream: `napplet/naps` PR #3, `naps/NAP-STORAGE.md` at `4f4cf0ca`.

Wire (napplet → shell): `storage.get {id, key, scope?}`, `storage.set {id, key, value,
scope?}`, `storage.remove {id, key, scope?}`, `storage.keys {id, scope?}`.
Wire (shell → napplet): `storage.get.result {id, value}` (`value` is a string or
`null`), `storage.set.result {id}`, `storage.remove.result {id}`,
`storage.keys.result {id, keys}`. Any result MAY instead carry `error`, and then
no other result field.

Malformed requests (missing or non-string `key`/`value`, a `scope` other than
`"shared"`/`"instance"`) get `{type: <type>.result, id, error: "invalid request"}`
when `id` is a string (modelling decision 31). The scope comes from the binding,
never the request.

State: the store is persistent and keyed by scope, not by port, so teardown leaves
it in place (the napplet's data outlives its iframe).
-/

namespace Napplet.Run.Storage

open NapStorage

structure St where
  store : Store
  quota : Nat
  /-- The scopes with stored values, in first-write order (what `Persist.persist` reads). -/
  keys : List Scope := []

def St.init (quota : Nat := defaultQuota) : St := { store := fun _ => [], quota, keys := [] }

/-- Keep `keys` listing exactly the scopes with stored values. -/
def keyUpd (keys : List Scope) (sc : Scope) (kv : KV) : List Scope :=
  if kv.isEmpty then keys.erase sc else if keys.contains sc then keys else keys ++ [sc]

abbrev Req := StorageReq

/-! ### Codec -/

def requestTypes : List String := ["storage.get", "storage.set", "storage.remove", "storage.keys"]

def selOf? (j : Json) : Option ScopeSel :=
  match j.get? "scope" with
  | none => some .shared
  | some (.str "shared") => some .shared
  | some (.str "instance") => some .inst
  | some _ => none

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some t =>
    if t ∉ requestTypes then .unknown else
    let bad := Decoded.reject (errorReply (resultType t) j "invalid request")
    match reqId? j, selOf? j with
    | some id, some sel =>
      if t = "storage.keys" then .ok (.keys id sel) else
      match j.getStr? "key" with
      | none => bad
      | some k =>
        if t = "storage.get" then .ok (.get id k sel)
        else if t = "storage.remove" then .ok (.remove id k sel)
        else match j.getStr? "value" with
          | some v => .ok (.set id k v sel)
          | none => bad
    | _, _ => bad
  | none => .unknown

def selJson : ScopeSel → Option Json
  | .shared => none
  | .inst => some (.str "instance")

/-- The request as the napplet-side binding sends it (`scope` omitted when shared). -/
def encodeReq : Req → Json
  | .get id k sel => Json.msg "storage.get" [("id", some (.str id)), ("key", some (.str k)), ("scope", selJson sel)]
  | .set id k v sel => Json.msg "storage.set"
      [("id", some (.str id)), ("key", some (.str k)), ("value", some (.str v)), ("scope", selJson sel)]
  | .remove id k sel => Json.msg "storage.remove" [("id", some (.str id)), ("key", some (.str k)), ("scope", selJson sel)]
  | .keys id sel => Json.msg "storage.keys" [("id", some (.str id)), ("scope", selJson sel)]

def typeOf : Req → String
  | .get .. => "storage.get" | .set .. => "storage.set"
  | .remove .. => "storage.remove" | .keys .. => "storage.keys"

/-- The result envelope for a request and its handler result. -/
def encodeResult (r : Req) (res : StorageResult) : Json :=
  let t := resultType (typeOf r)
  match res.error with
  | some e => Json.msg t [("id", some (.str res.id)), ("error", some (.str e))]
  | none =>
    match res.payload with
    | .value v => Json.msg t [("id", some (.str res.id)), ("value", some (v.elim .null .str))]
    | .keys ks => Json.msg t [("id", some (.str res.id)), ("keys", some (Json.strs ks))]
    | .empty => Json.msg t [("id", some (.str res.id))]

/-! ### Component -/

def handle (_h : Host) (_w : World) (cx : Ctx) (s : St) (r : Req) : St × List Eff :=
  let (store', res) := NapStorage.handle s.quota s.store cx.storage r
  let sc := scopeFor cx.storage r.sel
  ({ s with store := store', keys := keyUpd s.keys sc (store' sc) }, [.send cx.port (encodeResult r res)])

def onReply (_h : Host) (_w : World) (s : St) (_n : Nat) (_r : Reply) : St × List Eff := (s, [])

def onEvent (_h : Host) (_w : World) (s : St) (_e : HostEvent) : St × List Eff := (s, [])

def drop (s : St) (_p : PortId) : St × List Eff := (s, [])

def mentions (_s : St) (_p : PortId) : Bool := false

/-! ### Properties -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r with
  | get id k sel => cases sel <;> simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj,
      Json.getStr?, Json.get?, Json.lookup, reqId?, selOf?, selJson]
  | set id k v sel => cases sel <;> simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj,
      Json.getStr?, Json.get?, Json.lookup, reqId?, selOf?, selJson]
  | remove id k sel => cases sel <;> simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj,
      Json.getStr?, Json.get?, Json.lookup, reqId?, selOf?, selJson]
  | keys id sel => cases sel <;> simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj,
      Json.getStr?, Json.get?, Json.lookup, reqId?, selOf?, selJson]

/-- Every reply goes back to the requesting endpoint and carries the request `id`. -/
theorem handle_reply (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    (handle h w cx s r).2 = [.send cx.port (encodeResult r (NapStorage.handle s.quota s.store cx.storage r).2)] ∧
    (NapStorage.handle s.quota s.store cx.storage r).2.id = r.id :=
  ⟨rfl, NapStorage.handle_same_id _ _ _ _⟩

/-- A request touches only the scope derived from the endpoint's verified binding. -/
theorem handle_isolated (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) {sc : Scope}
    (hsc : sc ≠ scopeFor cx.storage r.sel) : (handle h w cx s r).1.store sc = s.store sc :=
  NapStorage.handle_isolated _ _ _ _ hsc

/-- The per-scope quota is preserved. -/
theorem handle_quota (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req)
    (hq : ∀ sc, usage (s.store sc) ≤ s.quota) :
    ∀ sc, usage ((handle h w cx s r).1.store sc) ≤ (handle h w cx s r).1.quota :=
  NapStorage.quota_preserved _ r hq

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := rfl

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by simp [drop, mentions] at h

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by simp [mentions] at hm

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  simp [mentions] at hm

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  simp [mentions] at hm

/-! ### Vectors (upstream examples) -/

#guard decode (Json.parse! "{ \"type\": \"storage.get\", \"id\": \"a1\", \"key\": \"theme\" }") matches .ok (.get "a1" "theme" .shared)
#guard decode (Json.parse! "{ \"type\": \"storage.set\", \"id\": \"b2\", \"key\": \"theme\", \"value\": \"light\", \"scope\": \"instance\" }") matches .ok (.set "b2" "theme" "light" .inst)
#guard decode (Json.parse! "{ \"type\": \"storage.clear\", \"id\": \"x\" }") matches .unknown
#guard match decode (Json.parse! "{ \"type\": \"storage.get\", \"id\": \"a9\" }") with
  | .reject [m] => Json.same m (Json.parse! "{\"type\":\"storage.get.result\",\"id\":\"a9\",\"error\":\"invalid request\"}")
  | _ => false
#guard decode (Json.parse! "{ \"type\": \"storage.get\", \"key\": \"k\" }") matches .reject []

end Napplet.Run.Storage
