import Napplet.Basic

/-!
# NAP-DISPLAY (`display`, PR napplet/naps#97 branch `nap-display`, EXPERIMENTAL)

Runtime-controlled pixel displays.

Results:
* `list_permitted`: a napplet lists only displays its policy permits.
* `push_atomic`: an invalid batch (empty, out of bounds, duplicate coordinate, bad
  RGB, too large, not permitted) changes nothing.
* `push_applies`: a valid batch sets exactly the listed pixels and leaves all other
  pixels and all other displays unchanged.
-/

namespace Napplet.NapDisplay

inductive DisplayType where
  | lcd | eink | ledMatrix | other
  deriving DecidableEq, Repr

structure DisplayDevice where
  id : String
  width : Nat
  height : Nat
  type : DisplayType
  deriving DecidableEq, Repr

structure Pixel where
  x : Nat
  y : Nat
  bytes : List Nat
  deriving DecidableEq, Repr

abbrev RGB := List Nat
abbrev Framebuffer := String → Nat × Nat → RGB

structure DisplayEnv where
  devices : List DisplayDevice
  permitted : Endpoint → String → Bool
  maxBatch : Nat

def pixelOk (d : DisplayDevice) (p : Pixel) : Bool :=
  p.x < d.width && p.y < d.height && p.bytes.length == 3 && p.bytes.all (· ≤ 255)

def batchOk (env : DisplayEnv) (d : DisplayDevice) (ps : List Pixel) : Option String :=
  if ps.isEmpty then some "invalid-pixel"
  else if ps.length > env.maxBatch then some "too-large"
  else if ps.all (pixelOk d) = false then some "invalid-pixel"
  else if decide (ps.map (fun p => (p.x, p.y))).Nodup = false then some "invalid-pixel"
  else none

/-- `display.list`: only permitted displays. -/
def list (env : DisplayEnv) (sender : Endpoint) : List DisplayDevice :=
  env.devices.filter fun d => env.permitted sender d.id

theorem list_permitted {env : DisplayEnv} {sender : Endpoint} {d : DisplayDevice}
    (h : d ∈ list env sender) : d ∈ env.devices ∧ env.permitted sender d.id = true := by
  simpa [list] using h

def applyPixels (fb : Framebuffer) (dev : String) (ps : List Pixel) : Framebuffer :=
  ps.foldl (fun f p => upd f dev (upd (f dev) (p.x, p.y) p.bytes)) fb

/-- `display.push`: validate the whole batch, then apply all of it. -/
def push (env : DisplayEnv) (fb : Framebuffer) (sender : Endpoint) (displayId : String)
    (ps : List Pixel) : Framebuffer × Option String :=
  match env.devices.find? (·.id == displayId) with
  | none => (fb, some "not-found")
  | some d =>
    if env.permitted sender displayId = false then (fb, some "denied")
    else match batchOk env d ps with
      | some e => (fb, some e)
      | none => (applyPixels fb displayId ps, none)

theorem push_atomic {env : DisplayEnv} {fb : Framebuffer} {sender : Endpoint} {did : String}
    {ps : List Pixel} (h : (push env fb sender did ps).2.isSome) :
    (push env fb sender did ps).1 = fb := by
  unfold push at h ⊢
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i hb; simp_all

theorem applyPixels_other_display (fb : Framebuffer) (dev dev' : String) (ps : List Pixel)
    (h : dev' ≠ dev) : applyPixels fb dev ps dev' = fb dev' := by
  induction ps generalizing fb with
  | nil => rfl
  | cons p ps ih =>
    simp only [applyPixels, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [upd, h]

theorem applyPixels_untouched (fb : Framebuffer) (dev : String) (ps : List Pixel)
    (xy : Nat × Nat) (h : xy ∉ ps.map (fun p => (p.x, p.y))) :
    applyPixels fb dev ps dev xy = fb dev xy := by
  induction ps generalizing fb with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [applyPixels, List.foldl_cons] at ih ⊢
    rw [ih _ h.2]
    have : xy ≠ (p.x, p.y) := h.1
    simp [upd, this]

theorem applyPixels_cons (fb : Framebuffer) (dev : String) (q : Pixel) (qs : List Pixel) :
    applyPixels fb dev (q :: qs) =
      applyPixels (upd fb dev (upd (fb dev) (q.x, q.y) q.bytes)) dev qs := rfl

theorem applyPixels_set (fb : Framebuffer) (dev : String) (ps : List Pixel)
    (hnd : (ps.map (fun p => (p.x, p.y))).Nodup) {p : Pixel} (hp : p ∈ ps) :
    applyPixels fb dev ps dev (p.x, p.y) = p.bytes := by
  induction ps generalizing fb with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [applyPixels_cons]
    rcases List.mem_cons.mp hp with rfl | hq
    · rw [applyPixels_untouched _ _ _ _ hnd.1]
      simp [upd]
    · exact ih _ hnd.2 hq

/-- A valid batch sets exactly its pixels, and touches nothing else. -/
theorem push_applies {env : DisplayEnv} {fb : Framebuffer} {sender : Endpoint} {did : String}
    {ps : List Pixel} (h : (push env fb sender did ps).2 = none) :
    (∀ p ∈ ps, (push env fb sender did ps).1 did (p.x, p.y) = p.bytes) ∧
    (∀ xy, xy ∉ ps.map (fun p => (p.x, p.y)) → (push env fb sender did ps).1 did xy = fb did xy) ∧
    (∀ d', d' ≠ did → (push env fb sender did ps).1 d' = fb d') ∧
    ∃ d, d ∈ env.devices ∧ d.id = did ∧ env.permitted sender did = true ∧
      ∀ p ∈ ps, pixelOk d p = true := by
  unfold push at h ⊢
  split at h
  · simp at h
  · rename_i d hd
    split at h
    · simp at h
    · rename_i hperm
      split at h
      · simp at h
      · rename_i hb
        simp only [hperm]
        unfold batchOk at hb
        split at hb
        · simp at hb
        · split at hb
          · simp at hb
          · split at hb
            · simp at hb
            · rename_i hall
              split at hb
              · simp at hb
              · rename_i hnd
                simp only [decide_eq_false_iff_not, Classical.not_not] at hnd
                simp only [List.all_eq_true, Bool.not_eq_false] at hall
                have hid := List.find?_some hd
                simp only [beq_iff_eq] at hid
                refine ⟨fun p hp => applyPixels_set _ _ _ hnd hp,
                  fun xy hxy => applyPixels_untouched _ _ _ _ hxy,
                  fun d' hd' => applyPixels_other_display _ _ _ _ hd',
                  d, List.mem_of_find?_eq_some hd, hid, by simp_all, ?_⟩
                intro p hp
                simp [hall p hp]

end Napplet.NapDisplay
