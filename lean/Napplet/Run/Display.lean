/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Display

/-!
# NAP-DISPLAY runtime component

Upstream: `napplet/naps` PR #97, `naps/NAP-DISPLAY.md` at `2c2e1b5c` (draft).

Wire (napplet → shell): `display.list {id}`, `display.push {id, displayId, pixels}`
where a pixel is `{x, y, bytes: [r, g, b]}`.
Wire (shell → napplet): `display.list.result {id, displays, error?}` with
`displays` a list of `{id, width, height, type}` (`type` one of `lcd`, `eink`,
`led-matrix`, `other`), and `display.push.result {id, error?}`. Errors:
`not-found`, `unavailable`, `denied`, `invalid-pixel`, `too-large`.

`display.list` is answered from the runtime's device list, filtered by the
per-napplet policy (`NapDisplay.list`). `display.push` validates the whole batch
(`NapDisplay.push`) before anything happens; a valid batch updates the runtime's
logical framebuffer and is handed to the host as one `Effect.nap .display "push"`,
in arrival order. A failed push changes nothing and emits no effect.

Malformed requests: a `display.push` whose `pixels` is not a list of
`{x, y, bytes}` objects with non-negative integer coordinates and integer bytes
gets `display.push.result {id, error: "invalid-pixel"}` (the NAP's error for bad
pixels); a missing or non-string `displayId` gets `error: "invalid request"`.
Out-of-range coordinates and byte values above 255 decode and are rejected by the
batch check with `invalid-pixel`. Without a string `id` nothing is sent.

State: the device list, the offline set and the logical framebuffer are runtime
state, not per-endpoint state (`mentions` is always `false`).
-/

/-! ## Host operations

* **Configuration** (`Cfg`, not a call): `devices`, the displays the host has
  discovered at start-up, each `{id, width, height, type}` with positive
  geometry. The host MUST keep each `id` stable for the same physical display
  across listings and restarts and MUST NOT reuse it for another display; it
  SHOULD be opaque (not a hardware serial). `permitted identity displayId`, the
  per-napplet policy (default: deny everything, as upstream recommends explicit
  per-napplet permission). `maxBatch`, the largest accepted batch (default 4096
  pixels).
* `HostEvent.nap .display "devices" {displays: [{id, width, height, type, available?}]}`:
  the host's current device list after a connection change. It replaces the
  runtime's list. Entries that are not well formed (missing field, unknown
  `type`, zero width or height) are skipped. `available: false` keeps the
  display listed but makes pushes to it fail with `unavailable`.
* `Effect.nap .display "push" {displayId, pixels: [{x, y, bytes: [r, g, b]}]}`:
  an accepted batch, already validated (display exists, permitted, non-empty, at
  most `maxBatch` pixels, every coordinate in range and distinct, every byte in
  `0..255`). The host maps logical sRGB to the device (it MAY rotate, reorder scan
  lines, quantize, dither, adjust brightness or coalesce refreshes) and MUST apply
  batches for the same display in the order the effects are emitted. It never
  receives driver commands from a napplet.
-/

namespace Napplet.Run.Display

open NapDisplay

/-- Host-discovered devices and per-napplet policy. -/
structure Cfg where
  devices : List DisplayDevice := []
  permitted : Identity → String → Bool := fun _ _ => false
  maxBatch : Nat := 4096

structure St where
  cfg : Cfg
  devices : List DisplayDevice
  /-- Displays the host reports as listed but currently unavailable. -/
  offline : List String
  /-- Logical framebuffer: the last accepted colour of every pixel. -/
  fb : Framebuffer

def St.init (cfg : Cfg := {}) : St :=
  { cfg, devices := cfg.devices, offline := [], fb := fun _ _ => [0, 0, 0] }

inductive Req where
  | list (id : String)
  | push (id displayId : String) (pixels : List Pixel)
  deriving DecidableEq, Repr

/-! ### JSON -/

def typeName : DisplayType → String
  | .lcd => "lcd" | .eink => "eink" | .ledMatrix => "led-matrix" | .other => "other"

def typeOf? : String → Option DisplayType
  | "lcd" => some .lcd | "eink" => some .eink | "led-matrix" => some .ledMatrix
  | "other" => some .other | _ => none

def deviceJson (d : DisplayDevice) : Json :=
  .obj [("id", .str d.id), ("width", Json.nat d.width), ("height", Json.nat d.height),
        ("type", .str (typeName d.type))]

def deviceOf? (j : Json) : Option DisplayDevice := do
  let id ← j.getStr? "id"
  let w ← (j.get? "width").bind Json.asNat?
  let h ← (j.get? "height").bind Json.asNat?
  let t ← (j.getStr? "type").bind typeOf?
  if w = 0 ∨ h = 0 then none else some ⟨id, w, h, t⟩

def natsJson (bs : List Nat) : Json := .arr (bs.map Json.nat)

def natsOf? (j : Json) : Option (List Nat) := j.asArr?.bind (·.mapM Json.asNat?)

def pixelJson (p : Pixel) : Json :=
  .obj [("x", Json.nat p.x), ("y", Json.nat p.y), ("bytes", natsJson p.bytes)]

def pixelOf? (j : Json) : Option Pixel := do
  some ⟨← (j.get? "x").bind Json.asNat?, ← (j.get? "y").bind Json.asNat?,
        ← (j.get? "bytes").bind natsOf?⟩

def pixelsJson (ps : List Pixel) : Json := .arr (ps.map pixelJson)

def pixelsOf? (j : Json) : Option (List Pixel) := j.asArr?.bind (·.mapM pixelOf?)

theorem natsOf?_natsJson (bs : List Nat) : natsOf? (natsJson bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [natsOf?, natsJson, Json.asArr?, Option.bind_some, List.map_cons,
      List.mapM_cons] at ih ⊢
    simp [ih]

theorem pixelOf?_pixelJson (p : Pixel) : pixelOf? (pixelJson p) = some p := by
  obtain ⟨x, y, bs⟩ := p
  simp [pixelOf?, pixelJson, Json.get?, Json.lookup, natsOf?_natsJson]

theorem pixelsOf?_pixelsJson (ps : List Pixel) : pixelsOf? (pixelsJson ps) = some ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pixelsOf?, pixelsJson, Json.asArr?, Option.bind_some, List.map_cons,
      List.mapM_cons] at ih ⊢
    simp [ih, pixelOf?_pixelJson]

/-! ### Codec -/

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some "display.list" =>
    match reqId? j with
    | some id => .ok (.list id)
    | none => .reject []
  | some "display.push" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match j.getStr? "displayId" with
      | none => .reject (errorReply "display.push.result" j "invalid request")
      | some did =>
        match (j.get? "pixels").bind pixelsOf? with
        | some ps => .ok (.push id did ps)
        | none => .reject (errorReply "display.push.result" j "invalid-pixel")
  | _ => .unknown

def encodeReq : Req → Json
  | .list id => Json.msg "display.list" [("id", some (.str id))]
  | .push id did ps => Json.msg "display.push"
      [("id", some (.str id)), ("displayId", some (.str did)), ("pixels", some (pixelsJson ps))]

def listResult (id : String) (ds : List DisplayDevice) : Json :=
  Json.msg "display.list.result" [("id", some (.str id)), ("displays", some (.arr (ds.map deviceJson)))]

def pushResult (id : String) (err : Option String) : Json :=
  Json.msg "display.push.result" [("id", some (.str id)), ("error", err.map .str)]

def pushArgs (did : String) (ps : List Pixel) : Json :=
  .obj [("displayId", .str did), ("pixels", pixelsJson ps)]

/-! ### Component -/

/-- The NAP model's environment for one endpoint. -/
def env (s : St) (cx : Ctx) : DisplayEnv :=
  { devices := s.devices, permitted := fun _ d => s.cfg.permitted cx.identity d,
    maxBatch := s.cfg.maxBatch }

def handle (_h : Host) (_w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .list id => (s, [.send cx.port (listResult id (NapDisplay.list (env s cx) cx.port))])
  | .push id did ps =>
    if s.devices.any (·.id == did) && s.offline.contains did then
      (s, [.send cx.port (pushResult id (some "unavailable"))])
    else
      match NapDisplay.push (env s cx) s.fb cx.port did ps with
      | (_, some e) => (s, [.send cx.port (pushResult id (some e))])
      | (fb', none) =>
        ({ s with fb := fb' },
         [.effect (.nap .display "push" (pushArgs did ps)), .send cx.port (pushResult id none)])

def onReply (_h : Host) (_w : World) (s : St) (_n : Nat) (_r : Reply) : St × List Eff := (s, [])

/-- One entry of the host's device report: the device and whether it is available. -/
def entryOf? (j : Json) : Option (DisplayDevice × Bool) :=
  (deviceOf? j).map fun d => (d, ((j.get? "available").bind Json.asBool?).getD true)

def onEvent (_h : Host) (_w : World) (s : St) : HostEvent → St × List Eff
  | .nap .display "devices" args =>
    let entries := (((args.get? "displays").bind Json.asArr?).getD []).filterMap entryOf?
    ({ s with devices := entries.map (·.1), offline := (entries.filter (!·.2)).map (·.1.id) }, [])
  | _ => (s, [])

def drop (s : St) (_p : PortId) : St × List Eff := (s, [])

def mentions (_s : St) (_p : PortId) : Bool := false

/-! ### Properties -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r <;> simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup,
    reqId?, pixelsOf?_pixelsJson]

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := rfl

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := h

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (_hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by simp [mentions] at hm

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  simp [mentions] at hm

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  simp [mentions] at hm

/-- `display.list` answers the requester only, with displays the runtime knows and
the napplet's policy permits (`NapDisplay.list_permitted`). -/
theorem list_permitted (h : Host) (w : World) (cx : Ctx) (s : St) (id : String) :
    ∃ ds, handle h w cx s (.list id) = (s, [.send cx.port (listResult id ds)]) ∧
      ∀ d ∈ ds, d ∈ s.devices ∧ s.cfg.permitted cx.identity d.id = true :=
  ⟨_, rfl, fun _ hd => NapDisplay.list_permitted hd⟩

/-- Every request gets exactly one result, to the requester, with its `id`. -/
theorem push_one_result (h : Host) (w : World) (cx : Ctx) (s : St) (id did : String)
    (ps : List Pixel) :
    ∃ e, ((handle h w cx s (.push id did ps)).2.filter fun x => match x with
      | .send .. => true | _ => false) = [.send cx.port (pushResult id e)] := by
  simp only [handle]
  split
  · exact ⟨_, rfl⟩
  · split <;> exact ⟨_, rfl⟩

/-- A push that is not handed to the hardware changes nothing (atomicity). -/
theorem push_atomic (h : Host) (w : World) (cx : Ctx) (s : St) (id did : String) (ps : List Pixel)
    (hn : ∀ a, Eff.effect (.nap .display "push" a) ∉ (handle h w cx s (.push id did ps)).2) :
    (handle h w cx s (.push id did ps)).1 = s := by
  by_cases hoff : (s.devices.any (·.id == did) && s.offline.contains did) = true
  · simp only [handle, hoff, ↓reduceIte]
  · rcases hpush : NapDisplay.push (env s cx) s.fb cx.port did ps with ⟨fb', _ | e⟩
    · exact absurd (by simp only [handle, hoff, hpush, Bool.false_eq_true, ↓reduceIte]; simp) (hn (pushArgs did ps))
    · simp only [handle, hoff, hpush, Bool.false_eq_true, ↓reduceIte]

/-- A batch reaches the hardware only if the display exists and is available, the
napplet may write it, and every pixel is valid; it then sets exactly the listed
pixels of the logical framebuffer and nothing else (`NapDisplay.push_applies`). -/
theorem push_applies (h : Host) (w : World) (cx : Ctx) (s : St) (id did : String)
    (ps : List Pixel) (a : Json)
    (he : Eff.effect (.nap .display "push" a) ∈ (handle h w cx s (.push id did ps)).2) :
    a = pushArgs did ps ∧ did ∉ s.offline ∧
    (∀ p ∈ ps, (handle h w cx s (.push id did ps)).1.fb did (p.x, p.y) = p.bytes) ∧
    (∀ xy, xy ∉ ps.map (fun p => (p.x, p.y)) →
      (handle h w cx s (.push id did ps)).1.fb did xy = s.fb did xy) ∧
    (∀ d', d' ≠ did → (handle h w cx s (.push id did ps)).1.fb d' = s.fb d') ∧
    ∃ d, d ∈ s.devices ∧ d.id = did ∧ s.cfg.permitted cx.identity did = true ∧
      ∀ p ∈ ps, pixelOk d p = true := by
  by_cases hoff : (s.devices.any (·.id == did) && s.offline.contains did) = true
  · simp only [handle, hoff, ↓reduceIte] at he; simp at he
  · rcases hpush : NapDisplay.push (env s cx) s.fb cx.port did ps with ⟨fb', _ | e⟩
    · simp only [handle, hoff, hpush, Bool.false_eq_true, ↓reduceIte] at he ⊢
      simp only [List.mem_cons, Eff.effect.injEq, Effect.nap.injEq, true_and, reduceCtorEq,
        List.mem_nil_iff, or_false] at he
      have hp := NapDisplay.push_applies (env := env s cx) (fb := s.fb) (sender := cx.port)
        (did := did) (ps := ps) (by rw [hpush])
      rw [hpush] at hp
      obtain ⟨h1, h2, h3, d, hd, hid, hperm, hok⟩ := hp
      have hdev : s.devices.any (·.id == did) = true := by
        simp only [List.any_eq_true, beq_iff_eq]; exact ⟨d, hd, hid⟩
      simp only [hdev, Bool.true_and, List.contains_iff_mem] at hoff
      exact ⟨he, hoff, h1, h2, h3, d, hd, hid, hperm, hok⟩
    · simp only [handle, hoff, hpush, Bool.false_eq_true, ↓reduceIte] at he; simp at he

/-! ### Vectors (upstream examples) -/

def sampleCfg : Cfg :=
  { devices := [⟨"desk", 800, 480, .eink⟩, ⟨"badge", 32, 8, .ledMatrix⟩],
    permitted := fun _ _ => true }

def sampleIdentity : Identity := { dTag := some "app", artifactHash := "h" }

def sampleCtx : Ctx :=
  { port := 7, window := 1, identity := sampleIdentity, exposed := [.display], inst := 0 }

def sampleWorld : World := { now := 0, live := [sampleCtx], user := "" }

def sampleHost : Host :=
  { crypto := { sha256 := fun _ => "", verifySig := fun _ => false }, verifyEvent := fun _ => false,
    sniff := fun _ => "application/octet-stream", rasterize := fun _ => none,
    looksCiphertext := fun _ => false, encryptedWith := fun _ => none, transform := id }

def listReq : Json := Json.parse! "{ \"type\": \"display.list\", \"id\": \"d1\" }"
def listRes : Json := Json.parse! "{ \"type\": \"display.list.result\", \"id\": \"d1\", \"displays\": [
     { \"id\": \"desk\", \"width\": 800, \"height\": 480, \"type\": \"eink\" },
     { \"id\": \"badge\", \"width\": 32, \"height\": 8, \"type\": \"led-matrix\" }
   ] }"
def pushReq : Json := Json.parse! "{ \"type\": \"display.push\", \"id\": \"d2\", \"displayId\": \"badge\", \"pixels\": [
     { \"x\": 0, \"y\": 0, \"bytes\": [255, 0, 0] },
     { \"x\": 1, \"y\": 0, \"bytes\": [0, 32, 255] }
   ] }"
def pushRes : Json := Json.parse! "{ \"type\": \"display.push.result\", \"id\": \"d2\" }"

def runOn (j : Json) : List Eff :=
  match decode j with
  | .ok r => (handle sampleHost sampleWorld sampleCtx (St.init sampleCfg) r).2
  | .reject rs => rs.map (.send sampleCtx.port)
  | .unknown => []

def sentJson : List Eff → List Json
  | [] => []
  | .send _ m :: es => m :: sentJson es
  | _ :: es => sentJson es

#guard decode listReq matches .ok (.list "d1")
#guard decode pushReq matches .ok (.push "d2" "badge" [⟨0, 0, [255, 0, 0]⟩, ⟨1, 0, [0, 32, 255]⟩])
#guard match sentJson (runOn listReq) with | [m] => Json.same m listRes | _ => false
#guard match sentJson (runOn pushReq) with | [m] => Json.same m pushRes | _ => false
#guard (runOn pushReq).length == 2
#guard decode (Json.parse! "{ \"type\": \"display.clear\", \"id\": \"x\" }") matches .unknown
#guard match runOn (Json.parse! "{ \"type\": \"display.push\", \"id\": \"d3\", \"displayId\": \"badge\", \"pixels\": [{ \"x\": 0, \"y\": 0, \"bytes\": [1, 2, 3] }, { \"x\": 0, \"y\": 0, \"bytes\": [1, 2, 3] }] }") with
  | [.send _ m] => Json.same m (Json.parse! "{ \"type\": \"display.push.result\", \"id\": \"d3\", \"error\": \"invalid-pixel\" }")
  | _ => false
#guard match runOn (Json.parse! "{ \"type\": \"display.push\", \"id\": \"d4\", \"displayId\": \"wall\", \"pixels\": [{ \"x\": 0, \"y\": 0, \"bytes\": [1, 2, 3] }] }") with
  | [.send _ m] => Json.same m (Json.parse! "{ \"type\": \"display.push.result\", \"id\": \"d4\", \"error\": \"not-found\" }")
  | _ => false
#guard match runOn (Json.parse! "{ \"type\": \"display.push\", \"id\": \"d5\", \"displayId\": \"badge\", \"pixels\": [{ \"x\": -1, \"y\": 0, \"bytes\": [1, 2, 3] }] }") with
  | [.send _ m] => Json.same m (Json.parse! "{ \"type\": \"display.push.result\", \"id\": \"d5\", \"error\": \"invalid-pixel\" }")
  | _ => false
#guard match (handle sampleHost sampleWorld sampleCtx (St.init {}) (.list "d1")).2 with
  | [.send _ m] => Json.same m (Json.parse! "{ \"type\": \"display.list.result\", \"id\": \"d1\", \"displays\": [] }")
  | _ => false
-- The host reports `badge` disconnected: it stays listed, pushes fail with `unavailable`.
def offlineSt : St := (onEvent sampleHost sampleWorld (St.init sampleCfg) (.nap .display "devices"
  (Json.parse! "{ \"displays\": [{ \"id\": \"badge\", \"width\": 32, \"height\": 8, \"type\": \"led-matrix\", \"available\": false }, { \"id\": \"bad\", \"width\": 0, \"height\": 8, \"type\": \"lcd\" }] }"))).1
#guard offlineSt.devices.length == 1 && offlineSt.offline == ["badge"]
#guard match (handle sampleHost sampleWorld sampleCtx offlineSt (.push "d6" "badge" [⟨0, 0, [1, 2, 3]⟩])).2 with
  | [.send _ m] => Json.same m (Json.parse! "{ \"type\": \"display.push.result\", \"id\": \"d6\", \"error\": \"unavailable\" }")
  | _ => false

end Napplet.Run.Display
