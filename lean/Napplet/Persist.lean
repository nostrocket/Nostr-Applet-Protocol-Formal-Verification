/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Refine
import Napplet.Codec

/-!
# Persistence and restore

`Persisted` is everything durable in the runtime state (`Host.lean` §Persistence). The
audit of `Run/*.lean` finds these fields and no others:

| Field | Component | Keyed by |
|---|---|---|
| `storage` | NAP-STORAGE `St.store` | scope (manifest key, artifact hash, instance) |
| `schemas` | NAP-CONFIG `St.schemas` (raw schema and version) | scope |
| `values` | NAP-CONFIG `St.values` | scope |
| `intentDefaults` | NAP-INTENT `St.defaults` | archetype |
| `linkRules` | NAP-LINK `St.rules` | manifest key |
| `uploadConsent` | NAP-UPLOAD `St.consented` | manifest key |
| `valueAllowances` | NAP-VALUE `St.allowances` (remaining balance) | catalog id, rail |
| `cvmAllowances` | NAP-CVM `St.allowances` (remaining balance) | catalog id, server, method |

Everything else is per session: anything keyed by a port or window, pending host calls,
subscriptions, counters (identifiers are unique per runtime session), the theme and the
user (the host re-sends them), the display device list and framebuffer, and the intent
catalog (host events).

All maps are finite association lists. `persist` and `restore` work on the finite
representation `RtState'`; `RtState.restore` is the same restore on the model's state.
The model's function-typed store cannot be enumerated, so persisting goes through
`RtState'` (`persist_abs` relates the two).

Main results:
* `persist_restore`: `persist (restore cfg names p) = p` for well-formed `p`;
* `decPersisted_enc`: the JSON codec round-trips;
* `restore_clean`: restore revives no port, window, binding, grant or per-endpoint state;
* `Inv.restore`, `Restored.inv`: a restored state satisfies the composed invariant, and
  so does every state reached from it; `Restored.teardown_clears`, `Restored.shell_inv`,
  `Restored.ctx_verified`, `Restored.port_closed_teardown` and
  `Restored.second_hello_teardown` are the headline safety theorems for them;
* `Quota.restore`, `Quota.step`: the NAP-STORAGE per-scope quota holds after restore and
  every step;
* `Reachable'.restore_abs`: `step'` from a restored finite state refines `Runtime.step`.
-/

namespace Napplet.Persist

open _root_.Napplet.Runtime NapStorage Refine

/-! ## The durable record -/

structure Persisted where
  storage : List (Scope × KV)
  /-- Registered schema per scope: the raw schema JSON and its version. -/
  schemas : List (Scope × Json × Option Nat)
  values : List (Scope × Json)
  intentDefaults : List (String × String)
  linkRules : List Run.Link.Rule
  uploadConsent : List ManifestKey
  valueAllowances : List Run.Value.Allowance
  cvmAllowances : List Run.Cvm.Allowance
  deriving DecidableEq, Repr

def Persisted.empty : Persisted := ⟨[], [], [], [], [], [], [], []⟩

/-- Read the durable fields of a finite state. -/
def persist (s : RtState') : Persisted where
  storage := s.storage.store.entries
  schemas := s.config.schemas.entries.filterMap fun e => e.2.map fun r => (e.1, r.raw, r.version)
  values := s.config.values.entries.filterMap fun e => e.2.map (e.1, ·)
  intentDefaults := s.intent.defaults
  linkRules := s.link.rules
  uploadConsent := s.upload.consented
  valueAllowances := s.value.allowances
  cvmAllowances := s.cvm.allowances

/-- The registered schemas a record restores to (entries that do not register are
dropped; `Persisted.WF` rules them out). -/
def regEntries (p : Persisted) : List (Scope × Option Run.Config.Reg) :=
  p.schemas.filterMap fun e =>
    match Run.Config.register e.2.1 e.2.2 none with
    | .ok r => some (e.1, some r)
    | .error _ => none

/-- A fresh session with the durable fields of `p`. -/
def restore (cfg : Config) (names : FMap WindowId (Option String)) (p : Persisted) : RtState' :=
  let i := init' cfg names
  { i with
    storage := { i.storage with store := ⟨[], p.storage⟩ }
    config := { i.config with schemas := ⟨none, regEntries p⟩,
                              values := ⟨none, p.values.map fun e => (e.1, some e.2)⟩ }
    intent := { i.intent with defaults := p.intentDefaults }
    link := { i.link with rules := p.linkRules }
    upload := { i.upload with consented := p.uploadConsent }
    value := { i.value with allowances := p.valueAllowances }
    cvm := { i.cvm with allowances := p.cvmAllowances } }

/-- The same restore on the model's state. -/
def _root_.Napplet.Runtime.RtState.restore (cfg : Config) (p : Persisted) : RtState :=
  let i := RtState.init cfg
  { i with
    storage := { i.storage with store := FMap.get ⟨[], p.storage⟩ }
    config := { i.config with schemas := FMap.get ⟨none, regEntries p⟩,
                              values := FMap.get ⟨none, p.values.map fun e => (e.1, some e.2)⟩ }
    intent := { i.intent with defaults := p.intentDefaults }
    link := { i.link with rules := p.linkRules }
    upload := { i.upload with consented := p.uploadConsent }
    value := { i.value with allowances := p.valueAllowances }
    cvm := { i.cvm with allowances := p.cvmAllowances } }

theorem abs_restore (cfg : Config) (names : FMap WindowId (Option String))
    (hn : names.get = cfg.endpointName) (p : Persisted) :
    abs (restore cfg names p) = RtState.restore cfg p := by
  simp only [restore, RtState.restore, ← abs_init' cfg names hn]
  rfl

/-! ## Well-formed records -/

/-- A record the host may restore: distinct keys, no empty store entries, every store
entry within the configured quota, and every schema registers to its stored version. -/
structure Persisted.WF (cfg : Config) (p : Persisted) : Prop where
  storage_nodup : (p.storage.map Prod.fst).Nodup
  storage_ne : ∀ e ∈ p.storage, e.2 ≠ []
  storage_quota : ∀ e ∈ p.storage, usage e.2 ≤ cfg.storageQuota
  schemas_nodup : (p.schemas.map Prod.fst).Nodup
  schemas_reg : ∀ e ∈ p.schemas, ∃ r, Run.Config.register e.2.1 e.2.2 none = .ok r ∧ r.version = e.2.2
  values_nodup : (p.values.map Prod.fst).Nodup

/-- `WF` as a check the host runs on a record it loads. -/
def Persisted.check (cfg : Config) (p : Persisted) : Bool :=
  decide (p.storage.map Prod.fst).Nodup && p.storage.all (fun e => !e.2.isEmpty) &&
  p.storage.all (fun e => decide (usage e.2 ≤ cfg.storageQuota)) &&
  decide (p.schemas.map Prod.fst).Nodup &&
  p.schemas.all (fun e => match Run.Config.register e.2.1 e.2.2 none with
    | .ok r => decide (r.version = e.2.2) | .error _ => false) &&
  decide (p.values.map Prod.fst).Nodup

theorem Persisted.check_wf {cfg : Config} {p : Persisted} (h : p.check cfg = true) : p.WF cfg := by
  simp only [Persisted.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, fun e he => ?_, h3, h4, fun e he => ?_, h6⟩
  · have := h2 e he
    intro hn; rw [hn] at this; simp at this
  · have := h5 e he
    split at this
    · rename_i r hr; exact ⟨r, hr, by simpa using this⟩
    · cases this

theorem register_raw {j : Json} {v : Option Nat} {prior : Option Run.Config.Reg} {r : Run.Config.Reg}
    (h : Run.Config.register j v prior = .ok r) : r.raw = j := by
  unfold Run.Config.register at h
  cases h1 : Run.Config.rootCheck j with
  | error e => simp [h1] at h
  | ok sv =>
    simp only [h1] at h
    cases h2 : Run.Config.decodeNode 6 true j with
    | error e => simp [h2] at h
    | ok sch =>
      simp only [h2] at h
      cases h3 : Run.Config.checkTree sch with
      | error e => simp [h3] at h
      | ok t =>
        simp only [h3] at h
        cases t with
        | obj ps req d sec =>
          simp only at h
          generalize prior.bind (fun x => x.version) = a at h
          generalize v.or sv = b at h
          cases a <;> cases b <;> (try simp only at h) <;> (try split at h) <;> (try split at h) <;>
            first | (cases h; rfl) | (cases h) | (simp at h)
        | _ => cases h

theorem schemas_restore (p : Persisted) (hw : ∀ e ∈ p.schemas, ∃ r,
    Run.Config.register e.2.1 e.2.2 none = .ok r ∧ r.version = e.2.2) :
    (regEntries p).filterMap (fun e => e.2.map fun r => (e.1, r.raw, r.version)) = p.schemas := by
  obtain ⟨st, sc, va, id, li, up, vl, cv⟩ := p
  simp only [regEntries]
  induction sc with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨r, hr, hv⟩ := hw e (by simp)
    simp only [List.filterMap_cons, hr, Option.map_some, register_raw hr, hv]
    rw [ih (fun e' he' => hw e' (List.mem_cons_of_mem _ he'))]

theorem values_restore (l : List (Scope × Json)) :
    (l.map fun e => (e.1, some e.2)).filterMap (fun e => e.2.map (e.1, ·)) = l := by
  induction l with
  | nil => rfl
  | cons e l ih => simp only [List.map_cons, List.filterMap_cons, Option.map_some, ih]

/-- Restoring then persisting gives the record back. -/
theorem persist_restore (cfg : Config) (names : FMap WindowId (Option String)) (p : Persisted)
    (hw : p.WF cfg) : persist (restore cfg names p) = p := by
  simp only [persist, restore]
  rw [schemas_restore p hw.schemas_reg, values_restore]

/-! ## Restore revives nothing -/

/-- A restored state has no frame, binding, grant, bound port or instance id, and no
component holds per-endpoint state. -/
theorem restore_clean (cfg : Config) (p : Persisted) :
    (RtState.restore cfg p).shell = ShellState.init ∧ (RtState.restore cfg p).ports = [] ∧
    (∀ w, (RtState.restore cfg p).inst w = 0) ∧ ∀ q, mentions (RtState.restore cfg p) q = false := by
  refine ⟨rfl, rfl, fun _ => rfl, fun q => ?_⟩
  simp [mentions, mentionsList, RtState.restore, RtState.init, Run.Shell.St.init, Run.Shell.mentions,
    Run.Theme.St.init, Run.Theme.mentions, Run.Identity.St.init, Run.Identity.mentions,
    Run.Storage.mentions, Run.Inc.St.init, Run.Inc.mentions, Run.Intent.St.init,
    Run.Intent.mentions, Run.Notify.St.init, Run.Notify.mentions, Run.Notify.ports,
    Run.Display.St.init, Run.Display.mentions, Run.Keys.St.init, Run.Keys.mentions,
    Run.Relay.St.init, Run.Relay.mentions, Run.Outbox.St.init, Run.Outbox.mentions,
    Run.Media.St.init, Run.Media.mentions, Run.Config.St.init, Run.Config.mentions,
    Run.Resource.St.init, Run.Resource.mentions, Run.Upload.St.init, Run.Upload.mentions,
    Run.Link.St.init, Run.Link.mentions, Run.Value.St.init, Run.Value.mentions,
    Run.Cvm.St.init, Run.Cvm.mentions, Run.Pow.St.init, Run.Pow.mentions]

/-! ## The invariant after restore -/

theorem Inv.restore (h : Host) (cfg : Config) (p : Persisted) : Runtime.Inv h cfg (RtState.restore cfg p) where
  shell := Napplet.Inv.init _ _
  ports := by simp [RtState.restore, RtState.init, ShellState.init]
  clean q _ := (restore_clean cfg p).2.2.2 q

/-- States reached from a restored state. -/
inductive Restored (h : Host) (cfg : Config) (p : Persisted) : RtState → Prop where
  | restore : Restored h cfg p (RtState.restore cfg p)
  | step {s : RtState} (i : Input) : Restored h cfg p s → Restored h cfg p (Runtime.step h cfg s i).1

theorem Restored.inv {h : Host} {cfg : Config} {p : Persisted} {s : RtState}
    (hr : Restored h cfg p s) : Runtime.Inv h cfg s := by
  induction hr with
  | restore => exact Inv.restore h cfg p
  | step i _ ih => exact ih.step i

theorem MemInv.restore (cfg : Config) (p : Persisted) : MemInv (RtState.restore cfg p) where
  inst _ h := absurd rfl h
  ports_bound _ h := by simp [RtState.restore, RtState.init] at h
  ports_nodup := List.nodup_nil

theorem Restored.memInv {h : Host} {cfg : Config} {p : Persisted} {s : RtState}
    (hr : Restored h cfg p s) : MemInv s := by
  induction hr with
  | restore => exact MemInv.restore cfg p
  | step i _ ih => exact ih.step i

/-! ### The headline safety theorems after restore -/

section restored
variable {h : Host} {cfg : Config} {p : Persisted} {s : RtState}

theorem Restored.teardown_clears (hr : Restored h cfg p s) {q : PortId}
    (hb : s.shell.bindings q = none) : mentions s q = false :=
  hr.inv.clean q hb

theorem Restored.shell_inv (hr : Restored h cfg p s) : Napplet.Inv h.crypto cfg.shell s.shell :=
  hr.inv.shell

theorem Restored.ctx_verified (hr : Restored h cfg p s) {q : PortId} {cx : Ctx}
    (hc : ctxOf s q = some cx) :
    Verified h.crypto cx.identity ∧ cx.exposed = exposedFor cfg.shell cx.identity ∧ cx.port = q := by
  simp only [ctxOf, Option.map_eq_some_iff] at hc
  obtain ⟨b, hb, rfl⟩ := hc
  obtain ⟨ld, hf⟩ := hr.shell_inv.bind_frame q b hb
  exact ⟨(hr.shell_inv.frame_verified _ _ _ _ _ hf).1, (hr.shell_inv.frame_verified _ _ _ _ _ hf).2, rfl⟩

theorem Restored.port_closed_teardown (hr : Restored h cfg p s) {q : PortId} {b : Binding}
    (hb : s.shell.bindings q = some b) :
    let r := Runtime.step h cfg s (.portClosed q)
    r.1.shell.bindings q = none ∧ r.1.shell.grants q = [] ∧
    r.1.shell.frames b.window = some .removed ∧ Runtime.Output.closePort q ∈ r.2 ∧
    mentions r.1 q = false := by
  have hr' := Restored.step (.portClosed q) hr
  obtain ⟨ld, hf⟩ := hr.shell_inv.bind_frame q b hb
  have hsh : (Runtime.step h cfg s (.portClosed q)).1.shell =
      (Napplet.step h.crypto cfg.shell s.shell (.portClosed q)).1 := by
    simp only [Runtime.step, browserStep]
    rw [flushStep_shell]
    exact (dropPorts_shell _ _).1
  have hout : Runtime.Output.closePort q ∈ (Runtime.step h cfg s (.portClosed q)).2 := by
    simp [Runtime.step, browserStep, Napplet.step, hb, revoke, hf, ofShell]
  have hn : (Runtime.step h cfg s (.portClosed q)).1.shell.bindings q = none := by
    rw [hsh]; simp [Napplet.step, hb, revoke, hf]
  refine ⟨hn, ?_, ?_, hout, hr'.teardown_clears hn⟩
  · rw [hsh]; simp [Napplet.step, hb, revoke, hf]
  · rw [hsh]; simp [Napplet.step, hb, revoke, hf]

theorem Restored.second_hello_teardown (hr : Restored h cfg p s) {w : WindowId} {id : Identity}
    {ex : List Domain} {q : PortId} {ld : Bool}
    (hf : s.shell.frames w = some (.live id ex (some q) ld)) (ports : List PortId) :
    let r := Runtime.step h cfg s (.hello w ports)
    r.1.shell.bindings q = none ∧ r.1.shell.frames w = some .removed ∧
    Runtime.Output.closePort q ∈ r.2 ∧ Runtime.Output.removeFrame w ∈ r.2 ∧ mentions r.1 q = false := by
  have hr' := Restored.step (.hello w ports) hr
  have hsh : (Runtime.step h cfg s (.hello w ports)).1.shell =
      (Napplet.step h.crypto cfg.shell s.shell (.hello w ports)).1 := by
    simp only [Runtime.step, browserStep]
    rw [flushStep_shell]
    exact (dropPorts_shell _ _).1
  have hn : (Runtime.step h cfg s (.hello w ports)).1.shell.bindings q = none := by
    rw [hsh]; exact (revoke_second_hello hf).2.1
  refine ⟨hn, by rw [hsh]; exact (revoke_second_hello hf).1, ?_, ?_, hr'.teardown_clears hn⟩
  · simp [Runtime.step, browserStep, (revoke_second_hello (c := h.crypto) (cfg := cfg.shell) (ports := ports) hf).2.2.2, ofShell]
  · simp [Runtime.step, browserStep, (revoke_second_hello (c := h.crypto) (cfg := cfg.shell) (ports := ports) hf).2.2.2, ofShell]

end restored

/-! ### The storage quota -/

/-- NAP-STORAGE: every scope's usage is within the quota. -/
def Quota (s : RtState) : Prop := ∀ sc, usage (s.storage.store sc) ≤ s.storage.quota

theorem Quota.init (cfg : Config) : Quota (RtState.init cfg) := by
  intro sc; simp [RtState.init, Run.Storage.St.init, usage]

theorem Quota.restore {cfg : Config} {p : Persisted} (hw : p.WF cfg) : Quota (RtState.restore cfg p) := by
  intro sc
  simp only [RtState.restore, RtState.init, Run.Storage.St.init, FMap.get]
  cases ha : alookup p.storage sc with
  | none => simp [usage]
  | some kv => exact hw.storage_quota _ (alookup_mem ha)

theorem napStep_storage_quota (h : Host) (w : World) (cx : Ctx) (s : RtState) (j : Json) (d : Domain)
    (hq : Quota s) : Quota (napStep h w cx s j d).1 := by
  cases d <;> simp only [napStep, lift] <;> split <;> try exact hq
  rename_i r _
  exact Run.Storage.handle_quota h w cx s.storage r hq

theorem Quota.step {h : Host} {cfg : Config} {s : RtState} (hq : Quota s) (i : Input) :
    Quota (Runtime.step h cfg s i).1 := by
  cases hi : i.event? with
  | some e =>
    obtain ⟨S0, -, -, e3, -, -, -, -, -, hstep, -, -⟩ := step_browser h cfg s i e hi
    rw [hstep]
    obtain ⟨-, -, -, b4, -⟩ := browserStep_spec h cfg S0 e
    intro sc; rw [b4, e3]; exact hq sc
  | none =>
    cases i with
    | message q j =>
      simp only [Runtime.step]
      split
      · exact hq
      · split
        · split
          · exact napStep_storage_quota _ _ _ _ _ _ hq
          · exact hq
        · exact hq
    | reply tag r =>
      have := (replyStep_fields h s tag r).2.2.2.1
      have hqt : (replyStep h s tag r).1.storage.quota = s.storage.quota := by
        simp only [replyStep]; split <;> simp [Run.Storage.onReply]
      intro sc; simp only [Runtime.step]; rw [this, hqt]; exact hq sc
    | event e =>
      have := (eventStep_fields h s e).2.2.2.1
      intro sc; simp only [Runtime.step]; rw [this]; exact hq sc
    | tick n => exact hq
    | _ => simp [Input.event?] at hi

theorem Restored.quota {h : Host} {cfg : Config} {p : Persisted} (hw : p.WF cfg) {s : RtState}
    (hr : Restored h cfg p s) : Quota s := by
  induction hr with
  | restore => exact Quota.restore hw
  | step i _ ih => exact ih.step i

theorem Reachable.quota {h : Host} {cfg : Config} {s : RtState} (hr : Runtime.Reachable h cfg s) :
    Quota s := by
  induction hr with
  | init => exact Quota.init cfg
  | step i _ ih => exact ih.step i

/-! ## The finite representation after restore -/

theorem regEntries_sublist (l : List (Scope × Json × Option Nat)) :
    ((l.filterMap fun e => match Run.Config.register e.2.1 e.2.2 none with
      | .ok r => some (e.1, some r) | .error _ => none).map Prod.fst).Sublist (l.map Prod.fst) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons e l ih =>
    cases hr : Run.Config.register e.2.1 e.2.2 none with
    | ok r => simp only [List.filterMap_cons, hr, List.map_cons]; exact ih.cons_cons _
    | error er => simp only [List.filterMap_cons, hr, List.map_cons]; exact ih.cons _

theorem WF.restore (cfg : Config) (names : FMap WindowId (Option String)) (p : Persisted)
    (hw : p.WF cfg) : Refine.WF (restore cfg names p) := by
  have hi := WF.init' cfg names
  refine { hi with store_dflt := rfl, store_wf := ⟨hw.storage_nodup, ?_⟩, schemas_dflt := rfl, schemas_wf := ⟨?_, ?_⟩, values_dflt := rfl, values_wf := ⟨?_, ?_⟩ }
  · intro e he
    have := hw.storage_ne e he
    cases hv : e.2 with
    | nil => exact absurd hv this
    | cons _ _ => simp [keepNe, hv]
  · exact List.Nodup.sublist (regEntries_sublist p.schemas) hw.schemas_nodup
  · intro e he
    change e ∈ regEntries p at he
    simp only [regEntries, List.mem_filterMap] at he
    obtain ⟨e', -, he'⟩ := he
    split at he'
    · cases he'; rfl
    · cases he'
  · show ((p.values.map fun e => (e.1, some e.2)).map Prod.fst).Nodup
    rw [List.map_map]
    exact hw.values_nodup
  · intro e he
    change e ∈ p.values.map (fun e => (e.1, some e.2)) at he
    simp only [List.mem_map] at he
    obtain ⟨e', -, rfl⟩ := he
    rfl

/-- States `step'` reaches from a restored finite state. -/
inductive Reachable'' (h : Host) (cfg : Config) (names : FMap WindowId (Option String))
    (p : Persisted) : RtState' → Prop where
  | restore : Reachable'' h cfg names p (restore cfg names p)
  | step {s : RtState'} (i : Input) : Reachable'' h cfg names p s →
      Reachable'' h cfg names p (step' h cfg s i).1

/-- `step'` from a restored finite state refines `Runtime.step` from `RtState.restore`, so
every `Restored` theorem applies to it. -/
theorem Reachable''.abs {h : Host} {cfg : Config} {names : FMap WindowId (Option String)}
    {p : Persisted} (hn : names.get = cfg.endpointName) (hw : p.WF cfg) {s : RtState'}
    (hr : Reachable'' h cfg names p s) : Refine.WF s ∧ Restored h cfg p (Refine.abs s) := by
  induction hr with
  | restore => exact ⟨WF.restore cfg names p hw, abs_restore cfg names hn p ▸ .restore⟩
  | step i _ ih =>
    refine ⟨ih.1.step' i, ?_⟩
    rw [abs_step' ih.1]
    exact .step i ih.2

/-! ## JSON codec -/

section codec
open Codec

def encKey : ManifestKey → Json
  | .named p d => .obj [("t", .str "named"), ("publisher", .str p), ("d", .str d)]
  | .root p => .obj [("t", .str "root"), ("publisher", .str p)]
  | .snapshot e => .obj [("t", .str "snapshot"), ("eventId", .str e)]

def decKey (j : Json) : Except String ManifestKey := do
  let t ← field j "t" >>= decStr
  match t with
  | "named" => do
    let p ← field j "publisher" >>= decStr
    let d ← field j "d" >>= decStr
    pure (.named p d)
  | "root" => do let p ← field j "publisher" >>= decStr; pure (.root p)
  | "snapshot" => do let e ← field j "eventId" >>= decStr; pure (.snapshot e)
  | _ => .error ("unknown manifest key " ++ t)

@[simp] theorem decKey_enc (k : ManifestKey) : decKey (encKey k) = .ok k := by
  cases k <;> simp [decKey, encKey, field, Json.get?, Json.lookup] <;> rfl

def encScope (sc : Scope) : Json :=
  Json.mkObj [("key", some (encKey sc.key)), ("hash", some (.str sc.artifactHash)),
    ("inst", sc.inst.map Json.nat)]

def decScope (j : Json) : Except String Scope := do
  let k ← field j "key" >>= decKey
  let h ← field j "hash" >>= decStr
  let i ← optField j "inst" decNat
  pure ⟨k, h, i⟩

@[simp] theorem decScope_enc (sc : Scope) : decScope (encScope sc) = .ok sc := by
  obtain ⟨k, h, i⟩ := sc
  cases i <;> simp [decScope, encScope, field, optField, Json.mkObj, Json.get?, Json.lookup] <;> rfl

def encKV (kv : KV) : Json := encList (encPair .str .str) kv
def decKV : Dec KV := decList (decPair decStr decStr)

@[simp] theorem decKV_enc (kv : KV) : decKV (encKV kv) = .ok kv :=
  decList_enc kv (fun p _ => decPair_enc p rfl rfl)

def encTarget : Run.Link.Target → Json
  | .napplet => .obj [("t", .str "napplet")]
  | .host h => .obj [("t", .str "host"), ("host", .str h)]
  | .url u => .obj [("t", .str "url"), ("url", .str u)]

def decTarget (j : Json) : Except String Run.Link.Target := do
  let t ← field j "t" >>= decStr
  match t with
  | "napplet" => pure .napplet
  | "host" => do let h ← field j "host" >>= decStr; pure (.host h)
  | "url" => do let u ← field j "url" >>= decStr; pure (.url u)
  | _ => .error ("unknown link target " ++ t)

@[simp] theorem decTarget_enc (t : Run.Link.Target) : decTarget (encTarget t) = .ok t := by
  cases t <;> simp [decTarget, encTarget, field, Json.get?, Json.lookup] <;> rfl

def encRule (r : Run.Link.Rule) : Json :=
  .obj [("napplet", encKey r.napplet), ("target", encTarget r.target), ("allow", .bool r.allow)]

def decRule (j : Json) : Except String Run.Link.Rule := do
  let n ← field j "napplet" >>= decKey
  let t ← field j "target" >>= decTarget
  let a ← field j "allow" >>= decBool
  pure ⟨n, t, a⟩

@[simp] theorem decRule_enc (r : Run.Link.Rule) : decRule (encRule r) = .ok r := by
  simp [decRule, encRule, field, Json.get?, Json.lookup] <;> rfl

def encVA (a : Run.Value.Allowance) : Json :=
  .obj [("napplet", .str a.napplet), ("rail", .str a.rail), ("maxPerTransfer", .nat a.maxPerTransfer),
    ("remaining", .nat a.remaining)]

def decVA (j : Json) : Except String Run.Value.Allowance := do
  let n ← field j "napplet" >>= decStr
  let r ← field j "rail" >>= decStr
  let m ← field j "maxPerTransfer" >>= decNat
  let rem ← field j "remaining" >>= decNat
  pure ⟨n, r, m, rem⟩

@[simp] theorem decVA_enc (a : Run.Value.Allowance) : decVA (encVA a) = .ok a := by
  simp [decVA, encVA, field, Json.get?, Json.lookup] <;> rfl

def encCA (a : Run.Cvm.Allowance) : Json :=
  .obj [("napplet", .str a.napplet), ("server", .str a.server), ("method", .str a.method),
    ("payMethod", .str a.payMethod), ("remaining", .nat a.remaining)]

def decCA (j : Json) : Except String Run.Cvm.Allowance := do
  let n ← field j "napplet" >>= decStr
  let sv ← field j "server" >>= decStr
  let m ← field j "method" >>= decStr
  let pm ← field j "payMethod" >>= decStr
  let rem ← field j "remaining" >>= decNat
  pure ⟨n, sv, m, pm, rem⟩

@[simp] theorem decCA_enc (a : Run.Cvm.Allowance) : decCA (encCA a) = .ok a := by
  simp [decCA, encCA, field, Json.get?, Json.lookup] <;> rfl

def encSchemaEntry (e : Scope × Json × Option Nat) : Json :=
  Json.mkObj [("scope", some (encScope e.1)), ("schema", some e.2.1), ("version", e.2.2.map Json.nat)]

def decSchemaEntry (j : Json) : Except String (Scope × Json × Option Nat) := do
  let sc ← field j "scope" >>= decScope
  let sch ← field j "schema"
  let v ← optField j "version" decNat
  pure (sc, sch, v)

@[simp] theorem decSchemaEntry_enc (e : Scope × Json × Option Nat) :
    decSchemaEntry (encSchemaEntry e) = .ok e := by
  obtain ⟨sc, sch, v⟩ := e
  cases v <;> simp [decSchemaEntry, encSchemaEntry, field, optField, Json.mkObj, Json.get?, Json.lookup] <;> rfl

/-- The record as JSON: one member per durable field. -/
def encPersisted (p : Persisted) : Json :=
  .obj [("storage", encList (encPair encScope encKV) p.storage),
    ("schemas", encList encSchemaEntry p.schemas),
    ("values", encList (encPair encScope id) p.values),
    ("intentDefaults", encList (encPair .str .str) p.intentDefaults),
    ("linkRules", encList encRule p.linkRules),
    ("uploadConsent", encList encKey p.uploadConsent),
    ("valueAllowances", encList encVA p.valueAllowances),
    ("cvmAllowances", encList encCA p.cvmAllowances)]

def decPersisted (j : Json) : Except String Persisted := do
  let st ← field j "storage" >>= decList (decPair decScope decKV)
  let sc ← field j "schemas" >>= decList decSchemaEntry
  let va ← field j "values" >>= decList (decPair decScope decJson)
  let id ← field j "intentDefaults" >>= decList (decPair decStr decStr)
  let li ← field j "linkRules" >>= decList decRule
  let up ← field j "uploadConsent" >>= decList decKey
  let vl ← field j "valueAllowances" >>= decList decVA
  let cv ← field j "cvmAllowances" >>= decList decCA
  pure ⟨st, sc, va, id, li, up, vl, cv⟩

@[simp] theorem decPersisted_enc (p : Persisted) : decPersisted (encPersisted p) = .ok p := by
  obtain ⟨st, sc, va, idf, li, up, vl, cv⟩ := p
  have h1 := decList_enc (d := decPair decScope decKV) (e := encPair encScope encKV) st
    (fun p _ => decPair_enc p (decScope_enc _) (decKV_enc _))
  have h2 := decList_enc (d := decSchemaEntry) (e := encSchemaEntry) sc (fun _ _ => decSchemaEntry_enc _)
  have h3 := decList_enc (d := decPair decScope decJson) (e := encPair encScope id) va
    (fun p _ => decPair_enc p (decScope_enc _) rfl)
  have h4 := decList_enc (d := decPair decStr decStr) (e := encPair .str .str) idf
    (fun p _ => decPair_enc p rfl rfl)
  have h5 := decList_enc (d := decRule) (e := encRule) li (fun _ _ => decRule_enc _)
  have h6 := decList_enc (d := decKey) (e := encKey) up (fun _ _ => decKey_enc _)
  have h7 := decList_enc (d := decVA) (e := encVA) vl (fun _ _ => decVA_enc _)
  have h8 := decList_enc (d := decCA) (e := encCA) cv (fun _ _ => decCA_enc _)
  simp [decPersisted, encPersisted, field, Json.get?, Json.lookup, h1, h2, h3, h4, h5, h6, h7, h8]

end codec

end Napplet.Persist
