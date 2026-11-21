import Napplet.Basic

/-!
# NAP-RELAY (`relay`, PR napplet/naps#2 branch `nub-relay`)

Relay proxy. Signing, encryption and decryption are shell-side opaque functions in
`RelayEnv`; the napplet's request type carries no key material.

Results:
* `broadcast_signed_by_shell`: every event the shell broadcasts is the shell's own
  signature over a napplet template (NIP-5D: napplets never sign).
* `no_napplet_ciphertext_broadcast`: the shell never signs or broadcasts content a
  napplet supplied as ciphertext (NIP-5D §Security 7).
* `publish_requires_write`, `subscribe_requires_read`.
* `delivery_plaintext`: encrypted events reach napplets only decrypted; undecryptable
  ones are not delivered at all.
* `delivery_only_matching_subscribers`.
* `close_stops_delivery`, `close_only_own`: a napplet can only close its own
  subscriptions, and a closed subscription gets nothing further.
* `sidecar_default_off`, `sidecar_opt_out`: pre-resolved sidecar resources never
  appear unless enabled, and never for an opted-out endpoint.
* `publish_same_id`.
-/

namespace Napplet.NapRelay

structure Template where
  kind : Nat
  content : String
  tags : List (List String)
  deriving DecidableEq, Repr

structure NostrEvent where
  id : String
  pubkey : Pubkey
  kind : Nat
  content : String
  tags : List (List String)
  sig : String
  deriving DecidableEq, Repr

abbrev SubId := String
/-- Filters are opaque; matching is supplied by the environment. -/
abbrev Filter := String

inductive Encryption where
  | nip44
  | nip04
  deriving DecidableEq, Repr

/-- Shell-side capabilities. The user's keys live behind these functions. -/
structure RelayEnv where
  sign : Template → NostrEvent
  encrypt : Encryption → Pubkey → String → String
  /-- Is this incoming event encrypted to the user (NIP-04, NIP-44)? -/
  isEncrypted : NostrEvent → Bool
  decrypt : NostrEvent → Option String
  /-- Heuristic: does napplet-supplied content look like ciphertext? -/
  looksCiphertext : String → Bool
  filterMatch : List Filter → NostrEvent → Bool
  /-- Pre-resolvable resource URLs for an event (sidecar). -/
  resources : NostrEvent → List String

structure Acl where
  canRead : Endpoint → Bool
  canWrite : Endpoint → Bool

structure Cfg where
  /-- Sidecar pre-resolution. MUST NOT be enabled by default. -/
  sidecar : Bool := false
  optOut : Endpoint → Bool := fun _ => false

inductive RelayReq where
  | subscribe (id : String) (subId : SubId) (filters : List Filter)
  | close (id : String) (subId : SubId)
  | publish (id : String) (t : Template)
  | publishEncrypted (id : String) (t : Template) (recipient : Pubkey) (enc : Encryption)
  deriving DecidableEq, Repr

structure Delivered where
  event : NostrEvent
  sidecarResources : List String
  deriving DecidableEq, Repr

inductive RelayOut where
  | event (to : Endpoint) (subId : SubId) (r : Delivered)
  | eose (to : Endpoint) (subId : SubId)
  | closed (to : Endpoint) (subId : SubId) (reason : Option String)
  | publishResult (to : Endpoint) (id : String) (ok : Bool) (ev : Option NostrEvent)
      (error : Option String)
  /-- Shell sends a signed event to its relay pool. -/
  | broadcast (ev : NostrEvent)
  deriving DecidableEq, Repr

structure RelayState where
  subs : List (Endpoint × SubId × List Filter)

def ownedBy (sender : Endpoint) (sid : SubId) (x : Endpoint × SubId × List Filter) : Bool :=
  x.1 == sender && x.2.1 == sid

/-- Shared publish path: ACL, ciphertext check, shell signing. -/
def signAndSend (env : RelayEnv) (acl : Acl) (sender : Endpoint) (id : String)
    (plaintext : String) (t : Template) : List RelayOut :=
  if acl.canWrite sender = false then [.publishResult sender id false none (some "policy denied")]
  else if env.looksCiphertext plaintext then
    [.publishResult sender id false none (some "blocked: ciphertext from napplet")]
  else
    let ev := env.sign t
    [.broadcast ev, .publishResult sender id true (some ev) none]

def handle (env : RelayEnv) (acl : Acl) (s : RelayState) (sender : Endpoint) :
    RelayReq → RelayState × List RelayOut
  | .subscribe _ sid fs =>
    if acl.canRead sender then
      ({ subs := (sender, sid, fs) :: s.subs.filter (fun x => !ownedBy sender sid x) }, [])
    else (s, [.closed sender sid (some "policy denied")])
  | .close _ sid =>
    ({ subs := s.subs.filter (fun x => !ownedBy sender sid x) }, [.closed sender sid none])
  | .publish id t => (s, signAndSend env acl sender id t.content t)
  | .publishEncrypted id t r enc =>
    (s, signAndSend env acl sender id t.content
      { t with content := env.encrypt enc r t.content })

/-- An event arrives from the relay pool. -/
def onPoolEvent (env : RelayEnv) (cfg : Cfg) (s : RelayState) (ev : NostrEvent) :
    List RelayOut :=
  let view : Option NostrEvent :=
    if env.isEncrypted ev then (env.decrypt ev).map fun pt => { ev with content := pt }
    else some ev
  match view with
  | none => []
  | some v =>
    s.subs.filterMap fun x =>
      if env.filterMatch x.2.2 ev then
        some (.event x.1 x.2.1
          ⟨v, if cfg.sidecar && !cfg.optOut x.1 then env.resources ev else []⟩)
      else none

/-! ### Publishing -/

theorem signAndSend_broadcast {env : RelayEnv} {acl : Acl} {sender : Endpoint} {id pt : String}
    {t : Template} {ev : NostrEvent} (h : RelayOut.broadcast ev ∈ signAndSend env acl sender id pt t) :
    ev = env.sign t ∧ acl.canWrite sender = true ∧ env.looksCiphertext pt = false := by
  unfold signAndSend at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp at h
      rename_i hw hc
      exact ⟨h, by simpa using hw, by simpa using hc⟩

/-- Every broadcast event is a shell signature over a template derived from the
napplet's request; napplets never sign. -/
theorem broadcast_signed_by_shell {env : RelayEnv} {acl : Acl} {s : RelayState}
    {sender : Endpoint} {r : RelayReq} {ev : NostrEvent}
    (h : RelayOut.broadcast ev ∈ (handle env acl s sender r).2) : ∃ t, ev = env.sign t := by
  cases r with
  | subscribe => simp only [handle] at h; split at h <;> simp at h
  | close => simp [handle] at h
  | publish id t => exact ⟨_, (signAndSend_broadcast h).1⟩
  | publishEncrypted id t rc enc => exact ⟨_, (signAndSend_broadcast h).1⟩

/-- The shell never signs or broadcasts ciphertext a napplet handed it. For
`publishEncrypted` the napplet supplies plaintext and the shell encrypts. -/
theorem no_napplet_ciphertext_broadcast {env : RelayEnv} {acl : Acl} {s : RelayState}
    {sender : Endpoint} {id : String} {t : Template} {ev : NostrEvent}
    (h : RelayOut.broadcast ev ∈ (handle env acl s sender (.publish id t)).2) :
    env.looksCiphertext t.content = false :=
  (signAndSend_broadcast h).2.2

theorem publishEncrypted_shell_encrypts {env : RelayEnv} {acl : Acl} {s : RelayState}
    {sender : Endpoint} {id : String} {t : Template} {rc : Pubkey} {enc : Encryption}
    {ev : NostrEvent}
    (h : RelayOut.broadcast ev ∈ (handle env acl s sender (.publishEncrypted id t rc enc)).2) :
    ev = env.sign { t with content := env.encrypt enc rc t.content } ∧
    env.looksCiphertext t.content = false := by
  have := signAndSend_broadcast h
  exact ⟨this.1, this.2.2⟩

theorem publish_requires_write {env : RelayEnv} {acl : Acl} {s : RelayState}
    {sender : Endpoint} {r : RelayReq} {ev : NostrEvent}
    (h : RelayOut.broadcast ev ∈ (handle env acl s sender r).2) : acl.canWrite sender = true := by
  cases r with
  | subscribe => simp only [handle] at h; split at h <;> simp at h
  | close => simp [handle] at h
  | publish => exact (signAndSend_broadcast h).2.1
  | publishEncrypted => exact (signAndSend_broadcast h).2.1

/-- Publish results carry the request `id` and go back to the sender. -/
theorem publish_same_id {env : RelayEnv} {acl : Acl} {sender : Endpoint} {id pt : String}
    {t : Template} :
    ∃ ok ev e, RelayOut.publishResult sender id ok ev e ∈ signAndSend env acl sender id pt t := by
  unfold signAndSend
  split
  · exact ⟨false, none, some "policy denied", by simp⟩
  · split
    · exact ⟨false, none, some "blocked: ciphertext from napplet", by simp⟩
    · exact ⟨true, some (env.sign t), none, by simp⟩

/-! ### Subscriptions and delivery -/

theorem subscribe_requires_read {env : RelayEnv} {acl : Acl} {s : RelayState}
    {sender : Endpoint} {id : String} {sid : SubId} {fs : List Filter}
    (h : acl.canRead sender = false) :
    handle env acl s sender (.subscribe id sid fs) = (s, [.closed sender sid (some "policy denied")]) := by
  simp [handle, h]

theorem onPoolEvent_mem {env : RelayEnv} {cfg : Cfg} {s : RelayState} {ev : NostrEvent}
    {to : Endpoint} {sid : SubId} {d : Delivered}
    (h : RelayOut.event to sid d ∈ onPoolEvent env cfg s ev) :
    ∃ fs, (to, sid, fs) ∈ s.subs ∧ env.filterMatch fs ev = true ∧
      (if env.isEncrypted ev then (env.decrypt ev).map (fun pt => { ev with content := pt })
       else some ev) = some d.event ∧
      d.sidecarResources = (if cfg.sidecar && !cfg.optOut to then env.resources ev else []) := by
  unfold onPoolEvent at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i v hv
    simp only [List.mem_filterMap] at h
    obtain ⟨⟨to', sid', fs⟩, hm, hx⟩ := h
    simp only at hx
    split at hx
    · rename_i hmatch
      simp only [Option.some.injEq, RelayOut.event.injEq] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact ⟨fs, hm, hmatch, hv, rfl⟩
    · simp at hx

/-- Only matching subscribers receive an event. -/
theorem delivery_only_matching_subscribers {env : RelayEnv} {cfg : Cfg} {s : RelayState}
    {ev : NostrEvent} {to : Endpoint} {sid : SubId} {d : Delivered}
    (h : RelayOut.event to sid d ∈ onPoolEvent env cfg s ev) :
    ∃ fs, (to, sid, fs) ∈ s.subs ∧ env.filterMatch fs ev = true := by
  obtain ⟨fs, hm, hmat, -⟩ := onPoolEvent_mem h
  exact ⟨fs, hm, hmat⟩

/-- Napplets receive plaintext: an encrypted event is delivered only with its
decrypted content, and an undecryptable one is not delivered. -/
theorem delivery_plaintext {env : RelayEnv} {cfg : Cfg} {s : RelayState} {ev : NostrEvent}
    {to : Endpoint} {sid : SubId} {d : Delivered} (he : env.isEncrypted ev = true)
    (h : RelayOut.event to sid d ∈ onPoolEvent env cfg s ev) :
    ∃ pt, env.decrypt ev = some pt ∧ d.event.content = pt := by
  obtain ⟨-, -, -, hv, -⟩ := onPoolEvent_mem h
  simp only [he, ↓reduceIte, Option.map_eq_some_iff] at hv
  obtain ⟨pt, hpt, hd⟩ := hv
  exact ⟨pt, hpt, by rw [← hd]⟩

theorem undecryptable_not_delivered {env : RelayEnv} {cfg : Cfg} {s : RelayState}
    {ev : NostrEvent} (he : env.isEncrypted ev = true) (hd : env.decrypt ev = none) :
    onPoolEvent env cfg s ev = [] := by
  simp [onPoolEvent, he, hd]

/-- Sidecar pre-resolution is off by default. -/
theorem sidecar_default_off {env : RelayEnv} {s : RelayState} {ev : NostrEvent}
    {to : Endpoint} {sid : SubId} {d : Delivered}
    (h : RelayOut.event to sid d ∈ onPoolEvent env {} s ev) : d.sidecarResources = [] := by
  obtain ⟨-, -, -, -, hs⟩ := onPoolEvent_mem h
  simpa using hs

theorem sidecar_opt_out {env : RelayEnv} {cfg : Cfg} {s : RelayState} {ev : NostrEvent}
    {to : Endpoint} {sid : SubId} {d : Delivered} (ho : cfg.optOut to = true)
    (h : RelayOut.event to sid d ∈ onPoolEvent env cfg s ev) : d.sidecarResources = [] := by
  obtain ⟨-, -, -, -, hs⟩ := onPoolEvent_mem h
  simpa [ho] using hs

/-- After a napplet closes `sid`, it receives nothing further on it. -/
theorem close_stops_delivery {env : RelayEnv} {acl : Acl} {cfg : Cfg} {s : RelayState}
    {sender : Endpoint} {id : String} {sid : SubId} {ev : NostrEvent} {d : Delivered} :
    RelayOut.event sender sid d ∉
      onPoolEvent env cfg (handle env acl s sender (.close id sid)).1 ev := by
  intro h
  obtain ⟨fs, hm, -⟩ := delivery_only_matching_subscribers h
  simp [handle, ownedBy] at hm

/-- Closing only removes the caller's own subscription. -/
theorem close_only_own {env : RelayEnv} {acl : Acl} {s : RelayState} {sender : Endpoint}
    {id : String} {sid : SubId} {x : Endpoint × SubId × List Filter} (hx : x ∈ s.subs)
    (hother : x.1 ≠ sender) : x ∈ (handle env acl s sender (.close id sid)).1.subs := by
  simp [handle, ownedBy, hx, hother]

end Napplet.NapRelay
