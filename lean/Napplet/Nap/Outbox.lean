import Napplet.Basic

/-!
# NAP-OUTBOX (`outbox`, PR napplet/naps#32 branch `nap-outbox`)

Outbox-aware (NIP-65) relay routing. Relay-list resolution, signing and signature
verification are opaque functions in `OutboxEnv`.

Results:
* `publish_single_event`: at most one signed event per `outbox.publish`.
* `publish_signed_by_shell`, `publish_requires_write`.
* `plan_nodup`: fanout relays are deduplicated.
* `plan_allowed`: every fanout relay passed relay policy, so napplet-supplied
  `options.relays` cannot force a private or disallowed host.
* `plan_includes_outbox`: the user's write relays are included unless `toOutbox`
  is false.
* `plan_includes_inboxes`, `missing_inbox_reported`: every `toInboxes` author's
  allowed read relays are included; an author with no resolvable list is reported,
  never silently replaced by fallback relays (`fallback_not_for_inboxes`).
* `query_nodup`, `query_verified`, `query_sound`: results are deduplicated by id and
  signature-checked.
* `getEvent_matches`: `getEvent` only returns the requested, verified event.
-/

namespace Napplet.NapOutbox

abbrev RelayUrl := String

structure Template where
  kind : Nat
  content : String
  deriving DecidableEq, Repr

structure NostrEvent where
  id : String
  pubkey : Pubkey
  kind : Nat
  content : String
  sig : String
  deriving DecidableEq, Repr

structure OutboxEnv where
  /-- User's NIP-65 write relays (empty if unavailable). -/
  userWrite : List RelayUrl
  /-- NIP-65 read relays for an author, if resolvable. -/
  readRelays : Pubkey → Option (List RelayUrl)
  /-- Configured fallback relays. -/
  fallback : List RelayUrl
  /-- Relay policy: valid, allowed, not a private host. -/
  allowed : RelayUrl → Bool
  sign : Template → NostrEvent
  verify : NostrEvent → Bool

structure PublishOptions where
  relays : List RelayUrl := []
  toOutbox : Bool := true
  toInboxes : List Pubkey := []
  deriving DecidableEq, Repr

/-! ### Deduplication -/

def dedup : List RelayUrl → List RelayUrl
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup {a : RelayUrl} {l : List RelayUrl} : a ∈ dedup l ↔ a ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons x xs ih =>
    simp only [dedup]
    split
    · rename_i hx
      constructor
      · intro h; exact List.mem_cons_of_mem _ (ih.mp h)
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact hx
        · exact ih.mpr h
    · simp [ih]

theorem dedup_nodup (l : List RelayUrl) : (dedup l).Nodup := by
  induction l with
  | nil => simp [dedup]
  | cons x xs ih =>
    simp only [dedup]
    split
    · exact ih
    · rename_i hx
      exact List.nodup_cons.mpr ⟨hx, ih⟩

/-! ### Publish fanout -/

/-- The user's own write set: NIP-65 write relays, or fallback when unavailable. -/
def ownSet (env : OutboxEnv) (o : PublishOptions) : List RelayUrl :=
  if o.toOutbox then (if env.userWrite = [] then env.fallback else env.userWrite) else []

/-- Read relays of every `toInboxes` author that resolved. No fallback here. -/
def inboxSet (env : OutboxEnv) (o : PublishOptions) : List RelayUrl :=
  o.toInboxes.flatMap fun a => (env.readRelays a).getD []

/-- Authors whose read relays could not be resolved. -/
def missingInboxes (env : OutboxEnv) (o : PublishOptions) : List Pubkey :=
  o.toInboxes.filter fun a => (env.readRelays a).isNone

def plan (env : OutboxEnv) (o : PublishOptions) : List RelayUrl :=
  dedup ((ownSet env o ++ inboxSet env o ++ o.relays).filter env.allowed)

structure PublishResult where
  ok : Bool
  event : Option NostrEvent
  relays : List RelayUrl
  missing : List Pubkey
  error : Option String
  deriving DecidableEq, Repr

inductive OutboxOut where
  | broadcast (ev : NostrEvent) (relays : List RelayUrl)
  | publishResult (to : Endpoint) (id : String) (r : PublishResult)
  deriving DecidableEq, Repr

def publish (env : OutboxEnv) (canWrite : Bool) (sender : Endpoint) (id : String)
    (t : Template) (o : PublishOptions) : List OutboxOut :=
  if canWrite = false then [.publishResult sender id ⟨false, none, [], [], some "publish denied"⟩]
  else
    let ev := env.sign t
    let rs := plan env o
    let miss := missingInboxes env o
    [.broadcast ev rs,
     .publishResult sender id
       ⟨true, some ev, rs, miss, if miss = [] then none else some "relay list unavailable"⟩]

def isBroadcast : OutboxOut → Bool
  | .broadcast .. => true
  | _ => false

theorem publish_single_event (env : OutboxEnv) (w : Bool) (sender : Endpoint) (id : String)
    (t : Template) (o : PublishOptions) :
    ((publish env w sender id t o).filter isBroadcast).length ≤ 1 := by
  unfold publish
  split <;> simp [List.filter_cons, isBroadcast]

theorem publish_broadcast {env : OutboxEnv} {w : Bool} {sender : Endpoint} {id : String}
    {t : Template} {o : PublishOptions} {ev : NostrEvent} {rs : List RelayUrl}
    (h : OutboxOut.broadcast ev rs ∈ publish env w sender id t o) :
    w = true ∧ ev = env.sign t ∧ rs = plan env o := by
  unfold publish at h
  split at h
  · simp at h
  · rename_i hw
    simp at h
    exact ⟨by simpa using hw, h.1, h.2⟩

theorem publish_signed_by_shell {env : OutboxEnv} {w : Bool} {sender : Endpoint} {id : String}
    {t : Template} {o : PublishOptions} {ev : NostrEvent} {rs : List RelayUrl}
    (h : OutboxOut.broadcast ev rs ∈ publish env w sender id t o) : ev = env.sign t :=
  (publish_broadcast h).2.1

theorem publish_requires_write {env : OutboxEnv} {sender : Endpoint} {id : String}
    {t : Template} {o : PublishOptions} {ev : NostrEvent} {rs : List RelayUrl}
    (h : OutboxOut.broadcast ev rs ∈ publish env false sender id t o) : False := by
  have := (publish_broadcast h).1
  simp at this

theorem plan_nodup (env : OutboxEnv) (o : PublishOptions) : (plan env o).Nodup :=
  dedup_nodup _

theorem mem_plan {env : OutboxEnv} {o : PublishOptions} {r : RelayUrl} :
    r ∈ plan env o ↔ (r ∈ ownSet env o ∨ r ∈ inboxSet env o ∨ r ∈ o.relays) ∧
      env.allowed r = true := by
  simp [plan, mem_dedup, or_and_right]

/-- Every fanout relay passed policy; napplet-supplied relays cannot bypass it. -/
theorem plan_allowed {env : OutboxEnv} {o : PublishOptions} {r : RelayUrl}
    (h : r ∈ plan env o) : env.allowed r = true :=
  (mem_plan.mp h).2

theorem plan_includes_outbox {env : OutboxEnv} {o : PublishOptions} {r : RelayUrl}
    (ht : o.toOutbox = true) (hw : r ∈ env.userWrite) (ha : env.allowed r = true) :
    r ∈ plan env o := by
  refine mem_plan.mpr ⟨.inl ?_, ha⟩
  have hne : env.userWrite ≠ [] := List.ne_nil_of_mem hw
  simp [ownSet, ht, hne, hw]

theorem plan_includes_inboxes {env : OutboxEnv} {o : PublishOptions} {a : Pubkey}
    {rs : List RelayUrl} {r : RelayUrl} (hi : a ∈ o.toInboxes) (hr : env.readRelays a = some rs)
    (hm : r ∈ rs) (ha : env.allowed r = true) : r ∈ plan env o := by
  refine mem_plan.mpr ⟨.inr (.inl ?_), ha⟩
  simp only [inboxSet, List.mem_flatMap]
  exact ⟨a, hi, by simp [hr, hm]⟩

theorem missing_inbox_reported {env : OutboxEnv} {o : PublishOptions} {a : Pubkey}
    (hi : a ∈ o.toInboxes) (hr : env.readRelays a = none) : a ∈ missingInboxes env o := by
  simp [missingInboxes, hi, hr]

/-- Fallback relays never stand in for an inbox: with `toOutbox` off, every fanout
relay is a resolved inbox relay or one the napplet named (and policy allowed). -/
theorem fallback_not_for_inboxes {env : OutboxEnv} {o : PublishOptions} {r : RelayUrl}
    (ht : o.toOutbox = false) (h : r ∈ plan env o) : r ∈ inboxSet env o ∨ r ∈ o.relays := by
  have := (mem_plan.mp h).1
  simpa [ownSet, ht] using this

/-! ### Queries -/

/-- Keep one event per id. -/
def dedupById : List NostrEvent → List NostrEvent
  | [] => []
  | e :: es => if (dedupById es).any (·.id == e.id) then dedupById es else e :: dedupById es

theorem mem_dedupById {e : NostrEvent} {l : List NostrEvent} (h : e ∈ dedupById l) : e ∈ l := by
  induction l with
  | nil => simp [dedupById] at h
  | cons x xs ih =>
    simp only [dedupById] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

theorem dedupById_nodup (l : List NostrEvent) : ((dedupById l).map (·.id)).Nodup := by
  induction l with
  | nil => simp [dedupById]
  | cons x xs ih =>
    simp only [dedupById]
    split
    · exact ih
    · rename_i hx
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at hx
      simp only [List.mem_map, not_exists, not_and]
      intro e he heq
      exact hx e he heq

/-- `outbox.query` result: verified, deduplicated by event id. -/
def queryResult (env : OutboxEnv) (fetched : List NostrEvent) : List NostrEvent :=
  dedupById (fetched.filter env.verify)

theorem query_nodup (env : OutboxEnv) (fetched : List NostrEvent) :
    ((queryResult env fetched).map (·.id)).Nodup :=
  dedupById_nodup _

theorem query_sound {env : OutboxEnv} {fetched : List NostrEvent} {e : NostrEvent}
    (h : e ∈ queryResult env fetched) : e ∈ fetched ∧ env.verify e = true := by
  have := mem_dedupById h
  simpa using this

theorem query_verified {env : OutboxEnv} {fetched : List NostrEvent} {e : NostrEvent}
    (h : e ∈ queryResult env fetched) : env.verify e = true :=
  (query_sound h).2

/-- `outbox.getEvent`: only the requested id, and only if its signature verifies. -/
def getEvent (env : OutboxEnv) (wanted : String) (fetched : List NostrEvent) :
    Option NostrEvent :=
  fetched.find? fun e => e.id == wanted && env.verify e

theorem getEvent_matches {env : OutboxEnv} {wanted : String} {fetched : List NostrEvent}
    {e : NostrEvent} (h : getEvent env wanted fetched = some e) :
    e.id = wanted ∧ env.verify e = true ∧ e ∈ fetched := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hp.1, hp.2, List.mem_of_find?_eq_some h⟩

end Napplet.NapOutbox
