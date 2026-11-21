/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Pow

/-!
# NAP-POW runtime component

Upstream: `napplet/naps` PR #39, `naps/NAP-POW.md` at `d85b4252`.

Wire (napplet → shell): `pow.mine` and `pow.mineAndPublish` `{id, jobId, template,
target, options?}`, `pow.queue {id}`, `pow.job {id, jobId}`, `pow.hashrate {id}`,
`pow.cancel {id, jobId}`, `pow.pause {id, jobId?}`, `pow.resume {id, jobId?}`.
Wire (shell → napplet): `<type>.result` for each, and the pushes (no `id`)
`pow.state {jobId, state, position?}`, `pow.progress {jobId, progress}`,
`pow.done {jobId, result}`, `pow.error {jobId, error}`.

The shell owns the queue. A job is accepted or rejected synchronously
(`NapPow.submit`: fresh per-endpoint `jobId`, `target ≤` the cap, room in the
queue). Jobs start in submission order (FIFO; `priority` is reported but not used
for ordering, which upstream permits) while fewer than `Cfg.maxConcurrent` jobs are
mining and the miner is not paused. At the moment a job starts the shell stamps
the user's pubkey and `created_at` (template `created_at`, else the clock) and
asks the host to search for a nonce (`Call.nap .pow "mine"`). The host's nonce
is checked in the shell: the NIP-01 id of the committed event (template tags with
any `nonce` tag replaced by `["nonce", n, target]`, `NapPow.withNonce`) is
computed with `Host.crypto.sha256` over the NIP-01 serialisation, and its
leading zero bits (`leadingZeroBits`, defined here over the hex id) must reach
the target; otherwise the job fails with `"timeout"`, as in `NapPow.run`.

`mineAndPublish` then asks for publish consent (`Call.prompt .pow "publish"`,
unless `Cfg.publishConsent` is off), refuses content that looks like ciphertext
(NIP-5D §Security 7), signs the committed event through `Call.sign`, checks that
the signer kept every committed field, and publishes with `Call.publish ev none`
(the shell's own relay selection; no napplet relays).

Per-endpoint state: every job (with its outstanding host call). Teardown cancels
each job's call (`Effect.cancel`) and, when it freed a mining slot while jobs
are queued, asks the host for a `wake` reply so the queue moves on.
-/

/-! ## Host operations

| Operation | Args (JSON) | Reply | Contract |
|---|---|---|---|
| `Call.nap .pow "mine" a` | `a` = `{pubkey, created_at, kind, content, tags, target, workers, timeoutMs?, commitCreatedAt}`; `tags` are the template's tags (any `nonce` tag is replaced by the miner) | `json {nonce: tstr, hashes: uint, elapsedMs: uint, created_at?: uint}` or `json {error: tstr}` | NIP-13: find a nonce `n` such that the NIP-01 id of `{pubkey, created_at, kind, content, tags'}` with `tags' = tags` minus `nonce` tags `++ [["nonce", n, toString target]]` has at least `target` leading zero bits, using at most `workers` workers. With `commitCreatedAt = false` the miner MAY advance `created_at` and then reports the value it used in `created_at`; otherwise `created_at` is fixed. `timeoutMs` bounds mining time only; on expiry reply `{error: "timeout"}`. Progress is reported with the `progress` event below, throttled to a few per second. |
| `Effect.nap .pow "pause" {call}` | `call` = the tag number `n` of the `mine` call | — | Suspend that search, keeping its best nonce and hash counters. |
| `Effect.nap .pow "resume" {call}` | as above | — | Continue a suspended search. |
| `HostEvent.nap .pow "progress" a` | `a` = `{call, bestPow, bestNonce?, hashes, hashRate, workers: [{workerId, bestPow, hashes, hashRate}], elapsedMs}` | — | Progress of the `mine` call `call` (numbers as NAP-POW `PowProgress`; `hashRate` any JSON number). |
| `Call.nap .pow "wake" {}` | `{}` | `json {}` | Reply promptly; lets the queue advance after a teardown freed a mining slot. |
| `Call.prompt .pow "publish" d` | `d` = `{jobId, event}` (the committed unsigned event with its id) | `decision` | Same publish consent as NAP-OUTBOX `publish`. Anything but `decision true _` refuses (`"publish denied"`). |
| `Call.sign ev` | the committed event | `signed` | Core contract. The shell rejects (`"publish denied"`) a signed event whose committed fields differ. |
| `Call.publish ev none` | the signed event | `published acks` | Core contract; the host selects relays outbox-aware (user's NIP-65 write relays plus the inbox relays of tagged recipients), as NAP-OUTBOX `publish`. |
| `Effect.cancel ⟨.pow, n⟩` | — | — | Core contract; on `pow.cancel` and on teardown. |

`Host.crypto.sha256` (FIPS 180-4) is applied to the UTF-8 bytes of the NIP-01
serialisation `[0, pubkey, created_at, kind, tags, content]` printed by
`Json.render` (`JSON.stringify` escaping, as NIP-01 prescribes).
-/

namespace Napplet.Run.Pow

open NapPow

/-! ### NIP-01 id and NIP-13 difficulty -/

def serialize (e : UnsignedEvent) : String :=
  Json.render (.arr [.nat 0, .str e.pubkey, .nat e.createdAt, .nat e.kind, Json.tags e.tags,
    .str e.content])

def nip01Id (h : Host) (e : UnsignedEvent) : String := h.crypto.sha256 (serialize e).toUTF8.toList

/-- Leading zero bits of a nibble value `v < 16`. -/
def nibbleZeros (v : Nat) : Nat :=
  if v ≥ 8 then 0 else if v ≥ 4 then 1 else if v ≥ 2 then 2 else if v ≥ 1 then 3 else 4

/-- NIP-13 difficulty: leading zero bits of a hex id (stops at the first non-hex
character). -/
def zerosOf : List Char → Nat
  | [] => 0
  | c :: cs =>
    match Json.hexVal? c with
    | some 0 => 4 + zerosOf cs
    | some v => nibbleZeros v
    | none => 0

def leadingZeroBits (hex : String) : Nat := zerosOf hex.toList

#guard leadingZeroBits "000007ab" = 21
#guard leadingZeroBits "000000def" = 24
#guard leadingZeroBits "f000" = 0
#guard leadingZeroBits "0000" = 16

/-! ### Wire types -/

def asNum? : Json → Option Num
  | .num n => some n
  | _ => none

def asInt? : Json → Option Int
  | .num n => n.toInt?
  | _ => none

theorem normalize_go_toInt (fuel : Nat) : ∀ (m e : Int), 0 ≤ e →
    (Num.normalize.go m e fuel).toInt? = some (m * 10 ^ e.toNat) := by
  induction fuel with
  | zero => intro m e he; simp [Num.normalize.go, Num.toInt?, he]
  | succ f ih =>
    intro m e he
    simp only [Num.normalize.go]
    split
    · rename_i h0; subst h0; simp [Num.toInt?]
    · split
      · rename_i _ hm
        rw [ih (m / 10) (e + 1) (by omega)]
        congr 1
        have h1 : (e + 1).toNat = e.toNat + 1 := by omega
        rw [h1, Int.pow_succ]
        have h2 : m / 10 * 10 = m := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hm)
        calc m / 10 * (10 ^ e.toNat * 10) = m / 10 * 10 * 10 ^ e.toNat := by
              rw [Int.mul_comm (10 ^ e.toNat) 10, Int.mul_assoc]
          _ = m * 10 ^ e.toNat := by rw [h2]
      · simp [Num.toInt?, he]

@[simp] theorem asInt?_int (i : Int) : asInt? (Json.int i) = some i := by
  simp only [asInt?, Json.int, Num.ofInt, Num.normalize]
  rw [normalize_go_toInt _ _ _ (by decide)]
  simp

/-- `PowOptions`. -/
structure Opts where
  workers : Option Nat := none
  priority : Option Int := none
  timeoutMs : Option Nat := none
  commitCreatedAt : Option Bool := none
  deriving DecidableEq, Repr

inductive Req where
  | submit (mode : Mode) (id jobId : String) (t : Template) (target : Nat) (o : Opts)
  | queue (id : String)
  | job (id jobId : String)
  | hashrate (id : String)
  | cancel (id jobId : String)
  | pause (id : String) (jobId : Option String)
  | resume (id : String) (jobId : Option String)
  deriving DecidableEq, Repr

/-! ### Codec -/

def optF {α : Type} (j : Json) (k : String) (f : Json → Option α) : Option (Option α) :=
  match j.get? k with
  | none => some none
  | some v => (f v).map some

/-- NAP-POW `EventTemplate`: `kind` and `content` required. -/
def templateOf? (j : Json) : Option Template := do
  let kind ← (j.get? "kind").bind Json.asNat?
  let content ← j.getStr? "content"
  let tags ← optF j "tags" Json.asTags?
  let createdAt ← optF j "created_at" Json.asNat?
  some ⟨kind, content, tags.getD [], createdAt⟩

def templateJson (t : Template) : Json :=
  Json.mkObj [("kind", some (.nat t.kind)), ("content", some (.str t.content)),
    ("tags", some (Json.tags t.tags)), ("created_at", t.createdAt.map Json.nat)]

def optsOf? (j : Json) : Option Opts :=
  match j.get? "options" with
  | none => some {}
  | some o => do
    guard o.isObj
    some ⟨← optF o "workers" Json.asNat?, ← optF o "priority" asInt?,
      ← optF o "timeoutMs" Json.asNat?, ← optF o "commitCreatedAt" Json.asBool?⟩

def optsJson (o : Opts) : Option Json :=
  if o = {} then none
  else some (Json.mkObj [("workers", o.workers.map Json.nat), ("priority", o.priority.map Json.int),
    ("timeoutMs", o.timeoutMs.map Json.nat), ("commitCreatedAt", o.commitCreatedAt.map .bool)])

def modeName : Mode → String
  | .mine => "mine"
  | .mineAndPublish => "mineAndPublish"

def submitType : Mode → String
  | .mine => "pow.mine"
  | .mineAndPublish => "pow.mineAndPublish"

/-- A rejected submission: `{id, jobId?, accepted: false, state: "error", error}`. -/
def rejectJson (type id : String) (jobId : Option String) (e : String) : Json :=
  Json.msg type [("id", some (.str id)), ("jobId", jobId.map .str), ("accepted", some (.bool false)),
    ("state", some (.str "error")), ("error", some (.str e))]

def decodeSubmit (mode : Mode) (j : Json) : Decoded Req :=
  match reqId? j with
  | none => .reject []
  | some id =>
    let rt := resultType (submitType mode)
    match j.getStr? "jobId" with
    | none => .reject [rejectJson rt id none "invalid request"]
    | some jobId =>
      match (j.get? "template").bind templateOf? with
      | none => .reject [rejectJson rt id (some jobId) "invalid template"]
      | some t =>
        match (j.get? "target").bind Json.asNat? with
        | none => .reject [rejectJson rt id (some jobId) "invalid target"]
        | some target =>
          match optsOf? j with
          | none => .reject [rejectJson rt id (some jobId) "invalid request"]
          | some o => .ok (.submit mode id jobId t target o)

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | none => .unknown
  | some t =>
    if t = "pow.mine" then decodeSubmit .mine j
    else if t = "pow.mineAndPublish" then decodeSubmit .mineAndPublish j
    else if t = "pow.queue" ∨ t = "pow.hashrate" then
      match reqId? j with
      | none => .reject []
      | some id => .ok (if t = "pow.queue" then .queue id else .hashrate id)
    else if t = "pow.job" ∨ t = "pow.cancel" then
      match reqId? j with
      | none => .reject []
      | some id =>
        match j.getStr? "jobId" with
        | some jid => .ok (if t = "pow.job" then .job id jid else .cancel id jid)
        | none => .reject (if t = "pow.job" then errorReply "pow.job.result" j "invalid request"
            else [Json.msg "pow.cancel.result" [("id", some (.str id)), ("cancelled", some (.bool false)),
              ("error", some (.str "invalid request"))]])
    else if t = "pow.pause" ∨ t = "pow.resume" then
      match reqId? j with
      | none => .reject []
      | some id =>
        match optF j "jobId" Json.asStr? with
        | some jid => .ok (if t = "pow.pause" then .pause id jid else .resume id jid)
        | none => .reject (errorReply (resultType t) j "invalid request")
    else .unknown

def encodeReq : Req → Json
  | .submit m id jobId t target o => Json.msg (submitType m)
      [("id", some (.str id)), ("jobId", some (.str jobId)), ("template", some (templateJson t)),
       ("target", some (.nat target)), ("options", optsJson o)]
  | .queue id => Json.msg "pow.queue" [("id", some (.str id))]
  | .job id jid => Json.msg "pow.job" [("id", some (.str id)), ("jobId", some (.str jid))]
  | .hashrate id => Json.msg "pow.hashrate" [("id", some (.str id))]
  | .cancel id jid => Json.msg "pow.cancel" [("id", some (.str id)), ("jobId", some (.str jid))]
  | .pause id jid => Json.msg "pow.pause" [("id", some (.str id)), ("jobId", jid.map .str)]
  | .resume id jid => Json.msg "pow.resume" [("id", some (.str id)), ("jobId", jid.map .str)]

/-! ### State -/

structure WorkerStat where
  workerId : Nat
  bestPow : Nat
  hashes : Nat
  hashRate : Num
  deriving DecidableEq, Repr

structure Progress where
  bestPow : Nat := 0
  bestNonce : Option String := none
  hashes : Nat := 0
  hashRate : Num := Num.ofNat 0
  workers : List WorkerStat := []
  elapsedMs : Nat := 0
  deriving DecidableEq, Repr

/-- A committed event whose nonce the shell has checked. -/
structure Mined where
  ev : UnsignedEvent
  id : String
  nonce : String
  pow : Nat
  hashes : Nat
  elapsedMs : Nat
  deriving DecidableEq, Repr

inductive Phase where
  /-- Waiting for a slot; `some n` when a suspended `mine` call `n` exists. -/
  | queued (call : Option Nat)
  | mining (call : Nat)
  | paused (call : Option Nat)
  | consent (call : Nat) (m : Mined)
  | signing (call : Nat) (m : Mined)
  | publishing (call : Nat) (m : Mined) (ev : NostrEvent)
  deriving DecidableEq, Repr

def Phase.call? : Phase → Option Nat
  | .queued c | .paused c => c
  | .mining c | .consent c _ | .signing c _ | .publishing c _ _ => some c

def Phase.name : Phase → String
  | .queued _ => "queued"
  | .paused _ => "paused"
  | _ => "mining"

structure Job where
  key : Nat
  port : PortId
  jobId : String
  mode : Mode
  template : Template
  target : Nat
  workers : Nat
  priority : Int
  timeoutMs : Option Nat
  commit : Bool
  /-- `(pubkey, created_at)` committed when mining started. -/
  stamp : Option (String × Nat)
  progress : Progress
  phase : Phase
  deriving DecidableEq, Repr

structure Cfg where
  /-- Highest accepted `target` (NAP-POW: the shell MUST cap it). -/
  maxTarget : Nat := 32
  /-- Jobs held at once, all napplets together. -/
  maxJobs : Nat := 32
  /-- Jobs mined at once. -/
  maxConcurrent : Nat := 1
  /-- Worker cap per job. -/
  maxWorkers : Nat := 4
  /-- Ask the user before `mineAndPublish` signs. -/
  publishConsent : Bool := true

structure St where
  cfg : Cfg
  jobs : List Job
  next : Nat
  minerPaused : Bool

def St.init (cfg : Cfg := {}) : St := ⟨cfg, [], 0, false⟩

/-! ### Messages -/

def stateJson (j : Job) (st : String) (pos : Option Nat) : Json :=
  Json.msg "pow.state" [("jobId", some (.str j.jobId)), ("state", some (.str st)), ("position", pos.map Json.nat)]

def workerJson (w : WorkerStat) : Json :=
  .obj [("workerId", .nat w.workerId), ("bestPow", .nat w.bestPow), ("hashes", .nat w.hashes),
        ("hashRate", .num w.hashRate)]

def progressJson (j : Job) : Json :=
  Json.mkObj [("jobId", some (.str j.jobId)), ("target", some (.nat j.target)),
    ("state", some (.str j.phase.name)), ("bestPow", some (.nat j.progress.bestPow)),
    ("bestNonce", j.progress.bestNonce.map .str), ("hashes", some (.nat j.progress.hashes)),
    ("hashRate", some (.num (if j.phase.name = "paused" then Num.ofNat 0 else j.progress.hashRate))),
    ("workers", some (.arr (j.progress.workers.map workerJson))), ("elapsedMs", some (.nat j.progress.elapsedMs))]

def unsignedJson (id : String) (e : UnsignedEvent) : Json :=
  .obj [("id", .str id), ("pubkey", .str e.pubkey), ("created_at", .nat e.createdAt),
        ("kind", .nat e.kind), ("tags", Json.tags e.tags), ("content", .str e.content)]

def doneJson (j : Job) (m : Mined) (ev : Json) (published : Option Json) (err : Option String) : Json :=
  Json.msg "pow.done" [("jobId", some (.str j.jobId)), ("result", some (Json.mkObj
    [("jobId", some (.str j.jobId)), ("ok", some (.bool err.isNone)), ("event", some ev),
     ("pow", some (.nat m.pow)), ("nonce", some (.str m.nonce)), ("hashes", some (.nat m.hashes)),
     ("elapsedMs", some (.nat m.elapsedMs)), ("published", published), ("error", err.map .str)]))]

def errorJson (j : Job) (e : String) : Json :=
  Json.msg "pow.error" [("jobId", some (.str j.jobId)), ("error", some (.str e))]

/-! ### Job bookkeeping -/

/-- Update one job; its key and port never change. -/
def updJob (s : St) (k : Nat) (f : Job → Job) : St :=
  { s with jobs := s.jobs.map fun j => if j.key = k then { f j with key := j.key, port := j.port } else j }

def rmJob (s : St) (k : Nat) : St := { s with jobs := s.jobs.filter (·.key != k) }

def isMining (j : Job) : Bool := match j.phase with | .mining _ => true | _ => false
def isQueued (j : Job) : Bool := match j.phase with | .queued _ => true | _ => false

def position (s : St) (k : Nat) : Nat := ((s.jobs.filter isQueued).map (·.key)).idxOf k

def canStart (s : St) : Bool := !s.minerPaused && decide ((s.jobs.filter isMining).length < s.cfg.maxConcurrent)

def stampOf (w : World) (j : Job) : String × Nat := (w.user, j.template.createdAt.getD w.now)

/-- The committed event before the nonce search. -/
def committed (j : Job) (st : String × Nat) : UnsignedEvent :=
  { pubkey := st.1, createdAt := st.2, kind := j.template.kind,
    tags := j.template.tags.filter (fun t => t.head? != some "nonce"), content := j.template.content }

def mineArgs (j : Job) (st : String × Nat) : Json :=
  Json.mkObj [("pubkey", some (.str st.1)), ("created_at", some (.nat st.2)),
    ("kind", some (.nat j.template.kind)), ("content", some (.str j.template.content)),
    ("tags", some (Json.tags j.template.tags)), ("target", some (.nat j.target)),
    ("workers", some (.nat j.workers)), ("timeoutMs", j.timeoutMs.map Json.nat),
    ("commitCreatedAt", some (.bool j.commit))]

/-- Start a job's search (or resume its suspended one). `announce` pushes `pow.state`. -/
def start (s : St) (w : World) (j : Job) (announce : Bool) : St × List Eff :=
  let note := if announce then [Eff.send j.port (stateJson j "mining" none)] else []
  match j.phase with
  | .queued (some n) =>
    (updJob s j.key fun x => { x with phase := .mining n },
     .effect (.nap .pow "resume" (.obj [("call", .nat n)])) :: note)
  | _ =>
    let st := (j.stamp.getD (stampOf w j))
    ({ updJob s j.key (fun x => { x with phase := .mining s.next, stamp := some st }) with next := s.next + 1 },
     .call ⟨.pow, s.next⟩ (.nap .pow "mine" (mineArgs j st)) :: note)

/-- Start queued jobs in order while there is room. -/
def schedule (w : World) : Nat → St → St × List Eff
  | 0, s => (s, [])
  | k + 1, s =>
    if canStart s then
      match s.jobs.find? isQueued with
      | none => (s, [])
      | some j =>
        let (s1, e1) := start s w j true
        let (s2, e2) := schedule w k s1
        (s2, e1 ++ e2)
    else (s, [])

def sched (w : World) (s : St) (effs : List Eff) : St × List Eff :=
  let (s', e) := schedule w s.jobs.length s
  (s', effs ++ e)

/-- The shell's check of a host nonce (NIP-13), with the committed fields. -/
def checkMined (h : Host) (j : Job) (st : String × Nat) (nonce : String) (hashes elapsed : Nat) :
    Option Mined :=
  let ev : UnsignedEvent := { committed j st with tags := withNonce j.template.tags nonce j.target }
  let id := nip01Id h ev
  let pow := leadingZeroBits id
  if pow ≥ j.target then some ⟨ev, id, nonce, pow, hashes, elapsed⟩ else none

/-- A signed event keeps every committed field. -/
def keeps (m : Mined) (e : NostrEvent) : Bool :=
  e.pubkey == m.ev.pubkey && e.createdAt == m.ev.createdAt && e.kind == m.ev.kind &&
    e.tags == m.ev.tags && e.content == m.ev.content

/-- End a job: remove it, push its last state and result, and let the queue move. -/
def endJob (s : St) (w : World) (j : Job) (state : String) (msg : Json) : St × List Eff :=
  sched w (rmJob s j.key) [.send j.port (stateJson j state none), .send j.port msg]

def progressOf? (a : Json) : Option Progress := do
  let bestPow ← (a.get? "bestPow").bind Json.asNat?
  let bestNonce ← optF a "bestNonce" Json.asStr?
  let hashes ← (a.get? "hashes").bind Json.asNat?
  let hashRate ← (a.get? "hashRate").bind asNum?
  let ws ← (a.get? "workers").bind Json.asArr?
  let workers ← ws.mapM fun w => do
    some ⟨← (w.get? "workerId").bind Json.asNat?, ← (w.get? "bestPow").bind Json.asNat?,
      ← (w.get? "hashes").bind Json.asNat?, ← (w.get? "hashRate").bind asNum?⟩
  let elapsedMs ← (a.get? "elapsedMs").bind Json.asNat?
  some { bestPow, bestNonce, hashes, hashRate, workers, elapsedMs }

/-! ### Component -/

def ownJob? (s : St) (p : PortId) (jobId : String) : Option Job :=
  s.jobs.find? fun j => j.port == p && j.jobId == jobId

def numAdd (a b : Num) : Num :=
  let e := min a.exp b.exp
  Num.normalize ⟨a.mant * 10 ^ (a.exp - e).toNat + b.mant * 10 ^ (b.exp - e).toNat, e⟩

def summaryJson (s : St) (j : Job) : Json :=
  Json.mkObj [("jobId", some (.str j.jobId)), ("target", some (.nat j.target)),
    ("state", some (.str j.phase.name)), ("priority", some (Json.int j.priority)),
    ("position", if isQueued j then some (.nat (position s j.key)) else none),
    ("bestPow", some (.nat j.progress.bestPow)),
    ("hashRate", some (.num (if isMining j then j.progress.hashRate else Num.ofNat 0))),
    ("kind", some (.nat j.template.kind)), ("mode", some (.str (modeName j.mode)))]

def hashrateJson (js : List Job) : Json :=
  .obj [("hashRate", .num (js.foldl (fun a j => numAdd a j.progress.hashRate) (Num.ofNat 0))),
        ("workers", .nat (js.foldl (fun a j => a + j.workers) 0)),
        ("perWorker", .arr (js.flatMap fun j => j.progress.workers.map fun w =>
            .obj [("workerId", .nat w.workerId), ("hashRate", .num w.hashRate)])),
        ("byJob", .arr (js.map fun j => .obj [("jobId", .str j.jobId), ("hashRate", .num j.progress.hashRate)]))]

def toNapJob (j : Job) : NapPow.Job := ⟨j.port, j.jobId, j.target, j.template, j.mode⟩

def pauseOne (s : St) (j : Job) : St × List Eff :=
  match j.phase with
  | .mining n => (updJob s j.key fun x => { x with phase := .paused (some n) },
      [.effect (.nap .pow "pause" (.obj [("call", .nat n)])), .send j.port (stateJson j "paused" none)])
  | .queued c => (updJob s j.key fun x => { x with phase := .paused c }, [.send j.port (stateJson j "paused" none)])
  | _ => (s, [])

def resumeOne (s : St) (j : Job) : St × List Eff :=
  match j.phase with
  | .paused c =>
    let s1 := updJob s j.key fun x => { x with phase := .queued c }
    (s1, [.send j.port (stateJson j "queued" (some (position s1 j.key)))])
  | _ => (s, [])

def foldJobs (f : St → Job → St × List Eff) (s : St) : List Job → St × List Eff
  | [] => (s, [])
  | j :: js =>
    let (s1, e1) := f s j
    let (s2, e2) := foldJobs f s1 js
    (s2, e1 ++ e2)

def handle (_h : Host) (w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .submit mode id jobId t target o =>
    let rt := resultType (submitType mode)
    match NapPow.submit ⟨s.cfg.maxTarget, s.cfg.maxJobs⟩ (s.jobs.map toNapJob) cx.port id jobId t target mode with
    | (_, [.mineResult _ _ _ true _]) =>
      let j : Job :=
        { key := s.next, port := cx.port, jobId, mode, template := t, target,
          workers := max 1 (min s.cfg.maxWorkers (o.workers.getD 1)), priority := o.priority.getD 0,
          timeoutMs := o.timeoutMs, commit := o.commitCreatedAt.getD true, stamp := none,
          progress := {}, phase := .queued none }
      let s1 : St := { s with jobs := s.jobs ++ [j], next := s.next + 1 }
      if canStart s then
        let (s2, e) := start s1 w j false
        (s2, .send cx.port (Json.msg rt [("id", some (.str id)), ("jobId", some (.str jobId)),
          ("accepted", some (.bool true)), ("state", some (.str "mining"))]) :: e)
      else
        (s1, [.send cx.port (Json.msg rt [("id", some (.str id)), ("jobId", some (.str jobId)),
          ("accepted", some (.bool true)), ("state", some (.str "queued")),
          ("position", some (.nat (position s1 j.key)))])])
    | (_, outs) =>
      let e := match outs with
        | [.mineResult _ _ _ _ (some e)] => e
        | _ => "policy denied"
      (s, [.send cx.port (rejectJson rt id (some jobId) e)])
  | .queue id =>
    (s, [.send cx.port (Json.msg "pow.queue.result" [("id", some (.str id)),
      ("jobs", some (.arr ((s.jobs.filter (·.port == cx.port)).map (summaryJson s))))])])
  | .job id jobId =>
    match ownJob? s cx.port jobId with
    | some j => (s, [.send cx.port (Json.msg "pow.job.result" [("id", some (.str id)), ("progress", some (progressJson j))])])
    | none => (s, [.send cx.port (errorReply "pow.job.result" (.obj [("id", .str id)]) "unknown jobId" |>.headD .null)])
  | .hashrate id =>
    (s, [.send cx.port (Json.msg "pow.hashrate.result" [("id", some (.str id)),
      ("hashrate", some (hashrateJson (s.jobs.filter fun j => j.port == cx.port && isMining j)))])])
  | .cancel id jobId =>
    match ownJob? s cx.port jobId with
    | none => (s, [.send cx.port (Json.msg "pow.cancel.result" [("id", some (.str id)), ("jobId", some (.str jobId)),
        ("cancelled", some (.bool false)), ("error", some (.str "unknown jobId"))])])
    | some j =>
      sched w (rmJob s j.key)
        ((match j.phase.call? with | some n => [.effect (.cancel ⟨.pow, n⟩)] | none => []) ++
         [.send cx.port (stateJson j "cancelled" none), .send cx.port (errorJson j "cancelled"),
          .send cx.port (Json.msg "pow.cancel.result" [("id", some (.str id)), ("jobId", some (.str jobId)),
            ("cancelled", some (.bool true))])])
  | .pause id none =>
    let (s1, e) := foldJobs pauseOne { s with minerPaused := true } (s.jobs.filter isMining)
    (s1, e ++ [.send cx.port (Json.msg "pow.pause.result" [("id", some (.str id))])])
  | .pause id (some jobId) =>
    match ownJob? s cx.port jobId with
    | none => (s, [.send cx.port (Json.msg "pow.pause.result" [("id", some (.str id)), ("jobId", some (.str jobId)),
        ("error", some (.str "unknown jobId"))])])
    | some j =>
      let (s1, e) := pauseOne s j
      sched w s1 (e ++ [.send cx.port (Json.msg "pow.pause.result" [("id", some (.str id)), ("jobId", some (.str jobId))])])
  | .resume id none =>
    let (s1, e) := foldJobs resumeOne { s with minerPaused := false } (s.jobs.filter fun j => j.phase.name == "paused")
    sched w s1 (e ++ [.send cx.port (Json.msg "pow.resume.result" [("id", some (.str id))])])
  | .resume id (some jobId) =>
    match ownJob? s cx.port jobId with
    | none => (s, [.send cx.port (Json.msg "pow.resume.result" [("id", some (.str id)), ("jobId", some (.str jobId)),
        ("error", some (.str "unknown jobId"))])])
    | some j =>
      let (s1, e) := resumeOne s j
      sched w s1 (e ++ [.send cx.port (Json.msg "pow.resume.result" [("id", some (.str id)), ("jobId", some (.str jobId))])])

/-- What a `pow.done` result must satisfy (NIP-13 and the committed fields). -/
def minedOK (h : Host) (j : Job) (m : Mined) : Bool :=
  m.id == nip01Id h m.ev && m.pow == leadingZeroBits m.id && decide (j.target ≤ m.pow) &&
    m.ev.tags == withNonce j.template.tags m.nonce j.target && m.ev.kind == j.template.kind &&
    m.ev.content == j.template.content

/-- Report a finished job; the result is re-checked so no `pow.done` ever carries
an id below the target (NAP-POW: "MUST NOT return a result whose id has fewer than
`target` leading zero bits"). -/
def finishDone (h : Host) (s : St) (w : World) (j : Job) (m : Mined) (ev : Json) (pub : Option Json)
    (err : Option String) : St × List Eff :=
  if minedOK h j m then endJob s w j "done" (doneJson j m ev pub err)
  else endJob s w j "error" (errorJson j "timeout")

/-- Mining finished with a checked nonce. -/
def mined (h : Host) (w : World) (s : St) (j : Job) (m : Mined) : St × List Eff :=
  match j.mode with
  | .mine => finishDone h s w j m (unsignedJson m.id m.ev) none none
  | .mineAndPublish =>
    if h.looksCiphertext m.ev.content then
      finishDone h s w j m (unsignedJson m.id m.ev) none (some "publish denied")
    else if s.cfg.publishConsent then
      sched w ({ updJob s j.key (fun x => { x with phase := .consent s.next m }) with next := s.next + 1 })
        [.call ⟨.pow, s.next⟩ (.prompt .pow "publish"
          (.obj [("jobId", .str j.jobId), ("event", unsignedJson m.id m.ev)]))]
    else
      sched w ({ updJob s j.key (fun x => { x with phase := .signing s.next m }) with next := s.next + 1 })
        [.call ⟨.pow, s.next⟩ (.sign m.ev)]

def onReply (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.jobs.find? (fun j => j.phase.call? == some n) with
  | none => sched w s []
  | some j =>
    match j.phase, rep with
    | .mining _, .json a | .paused (some _), .json a | .queued (some _), .json a =>
      let st0 := j.stamp.getD (stampOf w j)
      let st := if j.commit then st0 else (st0.1, ((a.get? "created_at").bind Json.asNat?).getD st0.2)
      match a.getStr? "nonce" with
      | none => endJob s w j "error" (errorJson j ((a.getStr? "error").getD "timeout"))
      | some nonce =>
        match checkMined h j st nonce (((a.get? "hashes").bind Json.asNat?).getD 0)
            (((a.get? "elapsedMs").bind Json.asNat?).getD 0) with
        | none => endJob s w j "error" (errorJson j "timeout")
        | some m => mined h w s j m
    | .mining _, _ | .paused _, _ | .queued _, _ => endJob s w j "error" (errorJson j "timeout")
    | .consent _ m, .decision true _ =>
      ({ updJob s j.key (fun x => { x with phase := .signing s.next m }) with next := s.next + 1 },
       [.call ⟨.pow, s.next⟩ (.sign m.ev)])
    | .consent _ m, _ =>
      finishDone h s w j m (unsignedJson m.id m.ev) none (some "publish denied")
    | .signing _ m, .signed (some e) =>
      if keeps m e then
        ({ updJob s j.key (fun x => { x with phase := .publishing s.next m e }) with next := s.next + 1 },
         [.call ⟨.pow, s.next⟩ (.publish e none)])
      else finishDone h s w j m (unsignedJson m.id m.ev) none (some "publish denied")
    | .signing _ m, _ =>
      finishDone h s w j m (unsignedJson m.id m.ev) none (some "publish denied")
    | .publishing _ m e, .published acks =>
      let pub := Json.obj [("eventId", .str e.id), ("relays", .obj (acks.map fun (r, ok) => (r, .bool ok)))]
      finishDone h s w j m e.toJson (some pub)
        (if acks.any (·.2) then none else some "publish failed")
    | .publishing _ m e, _ =>
      finishDone h s w j m e.toJson none (some "publish failed")

def onEvent (_h : Host) (w : World) (s : St) : HostEvent → St × List Eff
  | .nap .pow "progress" a =>
    match (a.get? "call").bind Json.asNat?, progressOf? a with
    | some n, some pr =>
      match s.jobs.find? (fun j => j.phase.call? == some n && (isMining j || j.phase.name == "paused")) with
      | some j =>
        let j' := { j with progress := pr }
        (updJob s j.key (fun x => { x with progress := pr }),
         [.send j.port (Json.msg "pow.progress" [("jobId", some (.str j.jobId)), ("progress", some (progressJson j'))])])
      | none => (s, [])
    | _, _ => (s, [])
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  let gone := s.jobs.filter (·.port == p)
  let s1 : St := { s with jobs := s.jobs.filter (·.port != p) }
  let cancels := gone.filterMap fun j => j.phase.call?.map fun n => Eff.effect (.cancel ⟨.pow, n⟩)
  if gone.any isMining && s1.jobs.any isQueued then
    ({ s1 with next := s.next + 1 }, cancels ++ [.call ⟨.pow, s.next⟩ (.nap .pow "wake" (.obj []))])
  else (s1, cancels)

def mentions (s : St) (p : PortId) : Bool := s.jobs.any (·.port == p)

/-! ### Codec properties -/

theorem templateOf?_templateJson (t : Template) : templateOf? (templateJson t) = some t := by
  obtain ⟨k, c, ts, ca⟩ := t
  cases ca <;> simp [templateOf?, templateJson, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, optF]

theorem optsOf?_optsJson (j : Json) (o : Opts) (hj : j.get? "options" = optsJson o) :
    optsOf? j = some o := by
  unfold optsOf?
  rw [hj]
  by_cases h0 : o = {}
  · simp [optsJson, h0]
  · obtain ⟨a, b, c, d⟩ := o
    simp only [optsJson, h0, ↓reduceIte]
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [Json.mkObj, Json.get?, Json.lookup, optF, Json.isObj, guard]

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r with
  | submit m id jobId t target o =>
    have ht := templateOf?_templateJson t
    have ho : optsOf? (encodeReq (.submit m id jobId t target o)) = some o := by
      apply optsOf?_optsJson
      cases m <;> cases hx : optsJson o <;> simp [encodeReq, submitType, Json.msg, Json.mkObj, Json.get?, Json.lookup, hx]
    cases m <;> simp only [encodeReq, submitType] at ho ⊢ <;>
      simp only [decode, decodeSubmit, reqId?] <;>
      cases hx : optsJson o <;>
      simp [Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, ht, ho, hx] <;>
      simp [hx, Json.msg, Json.mkObj] at ho <;> simp [ho]
  | queue id => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]
  | job id jid => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]
  | hashrate id => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]
  | cancel id jid => simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]
  | pause id jid => cases jid <;>
      simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?, optF]
  | resume id jid => cases jid <;>
      simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?, optF]

/-! ### Teardown and `mentions` -/

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp only [drop]
  split <;> simp [mentions, List.any_filter]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp only [drop] at h
  split at h <;>
  · simp only [mentions, List.any_eq_true, List.mem_filter] at h ⊢
    obtain ⟨x, hx, hq⟩ := h
    exact ⟨x, hx.1, hq⟩

/-- `s'` mentions only ports `s` mentions. -/
def Sub (s s' : St) : Prop := ∀ q, mentions s' q = true → mentions s q = true

theorem Sub.refl (s : St) : Sub s s := fun _ h => h
theorem Sub.trans {a b c : St} (h1 : Sub a b) (h2 : Sub b c) : Sub a c := fun q h => h1 q (h2 q h)

theorem sub_of_jobs {s s' : St} (h : s'.jobs = s.jobs) : Sub s s' := by
  intro q hq; simpa [mentions, h] using hq

theorem sub_updJob (s : St) (k : Nat) (f : Job → Job) : Sub s (updJob s k f) := by
  intro q hq
  simp only [mentions, updJob, List.any_map, List.any_eq_true, Function.comp] at hq ⊢
  obtain ⟨x, hx, hq⟩ := hq
  refine ⟨x, hx, ?_⟩
  split at hq <;> simpa using hq

theorem sub_rmJob (s : St) (k : Nat) : Sub s (rmJob s k) := by
  intro q hq
  simp only [mentions, rmJob, List.any_eq_true, List.mem_filter] at hq ⊢
  obtain ⟨x, hx, hq⟩ := hq
  exact ⟨x, hx.1, hq⟩

theorem sub_next {s s' : St} (k : Nat) (h : Sub s s') : Sub s { s' with next := k } := h

theorem sub_start (s : St) (w : World) (j : Job) (a : Bool) : Sub s (start s w j a).1 := by
  unfold start
  dsimp only
  split
  · exact sub_updJob _ _ _
  · exact sub_next _ (sub_updJob _ _ _)

theorem sub_schedule (w : World) : ∀ (k : Nat) (s : St), Sub s (schedule w k s).1
  | 0, s => Sub.refl s
  | k + 1, s => by
    simp only [schedule]
    split
    · split
      · exact Sub.refl s
      · exact Sub.trans (sub_start _ _ _ _) (sub_schedule w k _)
    · exact Sub.refl s

theorem sub_sched (w : World) (s : St) (e : List Eff) : Sub s (sched w s e).1 :=
  sub_schedule w _ s

theorem sub_endJob (s : St) (w : World) (j : Job) (st : String) (m : Json) : Sub s (endJob s w j st m).1 :=
  Sub.trans (sub_rmJob _ _) (sub_sched _ _ _)

theorem sub_finishDone (h : Host) (s : St) (w : World) (j : Job) (m : Mined) (ev : Json)
    (pub : Option Json) (err : Option String) : Sub s (finishDone h s w j m ev pub err).1 := by
  unfold finishDone; split <;> exact sub_endJob _ _ _ _ _

theorem sub_pauseOne (s : St) (j : Job) : Sub s (pauseOne s j).1 := by
  unfold pauseOne; split
  · exact sub_updJob _ _ _
  · exact sub_updJob _ _ _
  · exact Sub.refl _

theorem sub_resumeOne (s : St) (j : Job) : Sub s (resumeOne s j).1 := by
  unfold resumeOne; split
  · exact sub_updJob _ _ _
  · exact Sub.refl _

theorem sub_foldJobs (f : St → Job → St × List Eff) (hf : ∀ s j, Sub s (f s j).1) :
    ∀ (js : List Job) (s : St), Sub s (foldJobs f s js).1
  | [], s => Sub.refl s
  | j :: js, s => Sub.trans (hf s j) (sub_foldJobs f hf js _)

theorem sub_mined (h : Host) (w : World) (s : St) (j : Job) (m : Mined) : Sub s (mined h w s j m).1 := by
  unfold mined
  split
  · exact sub_finishDone _ _ _ _ _ _ _ _
  · split
    · exact sub_finishDone _ _ _ _ _ _ _ _
    · split
      · exact Sub.trans (sub_next _ (sub_updJob _ _ _)) (sub_sched _ _ _)
      · exact Sub.trans (sub_next _ (sub_updJob _ _ _)) (sub_sched _ _ _)

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  have key : mentions (handle h w cx s r).1 q = true → mentions s q = true ∨ q = cx.port := by
    cases r with
    | submit m id jobId t target o =>
      simp only [handle]
      split
      · rename_i j
        intro hq
        -- the new job is the only new port
        have hadd : ∀ (j : Job), j.port = cx.port → ∀ s2 : St, Sub { s with jobs := s.jobs ++ [j], next := s.next + 1 } s2 →
            mentions s2 q = true → mentions s q = true ∨ q = cx.port := by
          intro j hj s2 hs2 hq2
          have := hs2 q hq2
          simp only [mentions, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
            Bool.or_eq_true, beq_iff_eq] at this
          rcases this with h1 | h1
          · exact .inl h1
          · exact .inr (h1 ▸ hj)
        split at hq
        · exact hadd _ rfl _ (sub_start _ _ _ _) hq
        · exact hadd _ rfl _ (Sub.refl _) hq
      · intro hq; exact .inl hq
    | queue id => intro hq; exact .inl hq
    | job id jid => simp only [handle]; split <;> (intro hq; exact .inl hq)
    | hashrate id => intro hq; exact .inl hq
    | cancel id jid =>
      simp only [handle]; split
      · intro hq; exact .inl hq
      · intro hq; exact .inl (Sub.trans (sub_rmJob _ _) (sub_sched _ _ _) q hq)
    | pause id jid =>
      cases jid with
      | none =>
        simp only [handle]; intro hq
        exact .inl (Sub.trans (sub_of_jobs (s' := { s with minerPaused := true }) rfl)
          (sub_foldJobs _ sub_pauseOne _ _) q hq)
      | some jid =>
        simp only [handle]; split
        · intro hq; exact .inl hq
        · intro hq; exact .inl (Sub.trans (sub_pauseOne _ _) (sub_sched _ _ _) q hq)
    | resume id jid =>
      cases jid with
      | none =>
        simp only [handle]; intro hq
        exact .inl (Sub.trans (sub_of_jobs (s' := { s with minerPaused := false }) rfl)
          (Sub.trans (sub_foldJobs _ sub_resumeOne _ _) (sub_sched _ _ _)) q hq)
      | some jid =>
        simp only [handle]; split
        · intro hq; exact .inl hq
        · intro hq; exact .inl (Sub.trans (sub_resumeOne _ _) (sub_sched _ _ _) q hq)
  rcases key hm with h1 | h1
  · exact .inl h1
  · exact .inr ⟨cx, hcx, h1.symm⟩

theorem sub_onReply (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) : Sub s (onReply h w s n rep).1 := by
  unfold onReply
  split
  · exact sub_sched _ _ _
  · split
    all_goals first
      | exact sub_endJob _ _ _ _ _
      | exact sub_finishDone _ _ _ _ _ _ _ _
      | exact Sub.trans (sub_next _ (sub_updJob _ _ _)) (Sub.refl _)
      | (dsimp only; split
         · exact sub_endJob _ _ _ _ _
         · split
           · exact sub_endJob _ _ _ _ _
           · exact sub_mined _ _ _ _ _)
      | (split
         · exact sub_next _ (sub_updJob _ _ _)
         · exact sub_finishDone _ _ _ _ _ _ _ _)

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q :=
  .inl (sub_onReply h w s n rep q hm)

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  revert hm
  unfold onEvent
  split
  · split
    · split
      · exact sub_updJob _ _ _ q
      · exact id
    · exact id
  · exact id

/-! ### NAP-POW properties, lifted -/

/-- The shell's nonce check: an accepted result meets the target on the NIP-01 id
of exactly the committed event, with one `nonce` tag committing to the target and
every other template tag kept (`NapPow.mine_done`). -/
theorem checkMined_sound {h : Host} {j : Job} {st : String × Nat} {n : String} {a b : Nat} {m : Mined}
    (hm : checkMined h j st n a b = some m) :
    minedOK h j m = true ∧ m.ev.pubkey = st.1 ∧ m.ev.createdAt = st.2 ∧
    (m.ev.tags.filter (fun t => t.head? == some "nonce")).length = 1 ∧
    (∀ t ∈ j.template.tags, t.head? ≠ some "nonce" → t ∈ m.ev.tags) := by
  unfold checkMined at hm
  dsimp only at hm
  split at hm
  · rename_i hp
    simp only [Option.some.injEq] at hm
    subst hm
    refine ⟨?_, rfl, rfl, ?_, ?_⟩
    · simp [minedOK, committed]; exact decide_eq_true (by simpa [committed] using hp)
    · simp [withNonce, List.filter_append, List.filter_filter]
    · intro t ht hn; simp [withNonce, ht, hn]
  · simp at hm

theorem stateJson_type (j : Job) (st : String) (pos : Option Nat) :
    (stateJson j st pos).getStr? "type" = some "pow.state" := by
  cases pos <;> simp [stateJson, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

theorem errorJson_type (j : Job) (e : String) : (errorJson j e).getStr? "type" = some "pow.error" := by
  simp [errorJson, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup]

theorem start_effs (s : St) (w : World) (j : Job) (a : Bool) (e : Eff) (he : e ∈ (start s w j a).2) :
    (∃ p m, e = .send p m ∧ m.getStr? "type" = some "pow.state") ∨
    (∃ t x, e = .call t (.nap .pow "mine" x)) ∨ ∃ x, e = .effect x := by
  unfold start at he
  dsimp only at he
  split at he <;>
  · simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · split at he
      · simp only [List.mem_singleton] at he; subst he; exact .inl ⟨_, _, rfl, stateJson_type _ _ _⟩
      · simp at he

theorem schedule_effs (w : World) : ∀ (k : Nat) (s : St) (e : Eff), e ∈ (schedule w k s).2 →
    (∃ p m, e = .send p m ∧ m.getStr? "type" = some "pow.state") ∨
    (∃ t x, e = .call t (.nap .pow "mine" x)) ∨ ∃ x, e = .effect x
  | 0, s, e, he => by simp [schedule] at he
  | k + 1, s, e, he => by
    simp only [schedule] at he
    split at he
    · split at he
      · simp at he
      · simp only [List.mem_append] at he
        rcases he with he | he
        · exact start_effs _ _ _ _ _ he
        · exact schedule_effs w k _ e he
    · simp at he

theorem sched_effs (w : World) (s : St) (es : List Eff) (e : Eff) (he : e ∈ (sched w s es).2) :
    e ∈ es ∨ (∃ p m, e = .send p m ∧ m.getStr? "type" = some "pow.state") ∨
    (∃ t x, e = .call t (.nap .pow "mine" x)) ∨ ∃ x, e = .effect x := by
  simp only [sched, List.mem_append] at he
  rcases he with he | he
  · exact .inl he
  · exact .inr (schedule_effs w _ s e he)

/-- What a `pow.done` push may be. -/
def DoneOK (h : Host) (s : St) (p : PortId) (msg : Json) : Prop :=
  ∃ j ∈ s.jobs, ∃ m ev pub err, p = j.port ∧ msg = doneJson j m ev pub err ∧ minedOK h j m = true

def NotDone (e : Eff) : Prop := ∀ p m, e = .send p m → m.getStr? "type" ≠ some "pow.done"

theorem notDone_sched_extra {w : World} {s : St} {es : List Eff} {e : Eff} (he : e ∈ (sched w s es).2)
    (hn : e ∉ es) : NotDone e := by
  rcases sched_effs w s es e he with h1 | ⟨p, m, rfl, ht⟩ | ⟨t, x, rfl⟩ | ⟨x, rfl⟩
  · exact absurd h1 hn
  · intro p' m' h; cases h; rw [ht]; simp
  · intro p' m' h; cases h
  · intro p' m' h; cases h

theorem endJob_effs {s : St} {w : World} {j : Job} {st : String} {msg : Json} {e : Eff}
    (he : e ∈ (endJob s w j st msg).2) : e = .send j.port msg ∨ NotDone e := by
  unfold endJob at he
  by_cases hin : e ∈ [Eff.send j.port (stateJson j st none), Eff.send j.port msg]
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · right; intro p m h; cases h; rw [stateJson_type]; simp
    · exact .inl rfl
  · exact .inr (notDone_sched_extra he hin)

theorem finishDone_effs {h : Host} {s : St} {w : World} {j : Job} {m : Mined} {ev : Json}
    {pub : Option Json} {err : Option String} {e : Eff} (hj : j ∈ s.jobs)
    (he : e ∈ (finishDone h s w j m ev pub err).2) :
    NotDone e ∨ ∃ p msg, e = .send p msg ∧ DoneOK h s p msg := by
  unfold finishDone at he
  split at he
  · rename_i hok
    rcases endJob_effs he with rfl | h1
    · exact .inr ⟨_, _, rfl, j, hj, m, ev, pub, err, rfl, rfl, hok⟩
    · exact .inl h1
  · rcases endJob_effs he with rfl | h1
    · left; intro p m h; cases h; rw [errorJson_type]; simp
    · exact .inl h1

/-- Every `pow.done` the shell pushes is for a job of this state, goes to that job's
endpoint, and carries a result whose id meets the target with the committed fields
(`NapPow.mine_done`, `NapPow.pushes_to_owner`). -/
theorem onReply_done_ok (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (p : PortId)
    (msg : Json) (he : Eff.send p msg ∈ (onReply h w s n rep).2)
    (ht : msg.getStr? "type" = some "pow.done") : DoneOK h s p msg := by
  have key : ∀ e ∈ (onReply h w s n rep).2, NotDone e ∨ ∃ p msg, e = .send p msg ∧ DoneOK h s p msg := by
    intro e he
    unfold onReply at he
    split at he
    · exact .inl (notDone_sched_extra he (by simp))
    · rename_i j hj
      have hjm : j ∈ s.jobs := List.mem_of_find?_eq_some hj
      have nd_end : ∀ {st msg}, msg.getStr? "type" ≠ some "pow.done" → e ∈ (endJob s w j st msg).2 →
          NotDone e ∨ ∃ p msg, e = .send p msg ∧ DoneOK h s p msg := by
        intro st msg hmsg he
        rcases endJob_effs he with rfl | h1
        · left; intro p m h; cases h; exact hmsg
        · exact .inl h1
      have nd_call : ∀ {t c}, e ∈ [Eff.call t c] → NotDone e := by
        intro t c he; simp at he; subst he; intro p m h; cases h
      have hmined : ∀ m, e ∈ (mined h w s j m).2 → NotDone e ∨ ∃ p msg, e = .send p msg ∧ DoneOK h s p msg := by
        intro m he
        unfold mined at he
        split at he
        · exact finishDone_effs hjm he
        · split at he
          · exact finishDone_effs hjm he
          · split at he
            all_goals
              by_cases hin : e ∈ [Eff.call ⟨.pow, s.next⟩ (.prompt .pow "publish"
                  (.obj [("jobId", .str j.jobId), ("event", unsignedJson m.id m.ev)]))] ∨
                  e ∈ [Eff.call ⟨.pow, s.next⟩ (.sign m.ev)]
              · left; rcases hin with hin | hin <;> exact nd_call hin
              · exact .inl (notDone_sched_extra he (by simp_all))
      split at he
      all_goals first
        | exact finishDone_effs hjm he
        | exact .inl (nd_call he)
        | exact nd_end (by rw [errorJson_type]; simp) he
        | (dsimp only at he
           split at he
           · exact nd_end (by rw [errorJson_type]; simp) he
           · split at he
             · exact nd_end (by rw [errorJson_type]; simp) he
             · exact hmined _ he)
        | (split at he
           · exact .inl (nd_call he)
           · exact finishDone_effs hjm he)
  rcases key _ he with h1 | ⟨p', m', heq, hd⟩
  · exact absurd ht (h1 p msg rfl)
  · cases heq; exact hd

/-- `mineAndPublish` publishes only the signed form of a checked mined event whose
committed fields the signer kept, on the shell's own relays (no napplet relays). -/
theorem onReply_publish_verbatim (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (t : CallTag)
    (e : NostrEvent) (r : Option (List String)) (he : Eff.call t (.publish e r) ∈ (onReply h w s n rep).2) :
    r = none ∧ rep = .signed (some e) ∧ ∃ j ∈ s.jobs, ∃ c m, j.phase = .signing c m ∧ keeps m e = true := by
  have nosched : ∀ {s' es}, Eff.call t (.publish e r) ∈ (sched w s' es).2 → Eff.call t (.publish e r) ∈ es := by
    intro s' es hs
    rcases sched_effs w s' es _ hs with h1 | ⟨_, _, h2, _⟩ | ⟨_, _, h2⟩ | ⟨_, h2⟩
    · exact h1
    all_goals cases h2
  have noend : ∀ {j st msg}, Eff.call t (.publish e r) ∉ (endJob s w j st msg).2 := by
    intro j st msg hs
    have := nosched hs
    simp at this
  have nofin : ∀ {j m ev pub err}, Eff.call t (.publish e r) ∉ (finishDone h s w j m ev pub err).2 := by
    intro j m ev pub err hs
    unfold finishDone at hs
    split at hs <;> exact noend hs
  unfold onReply at he
  split at he
  · have := nosched he; simp at this
  · rename_i j hj
    have hjm : j ∈ s.jobs := List.mem_of_find?_eq_some hj
    split at he
    all_goals first
      | exact absurd he nofin
      | exact absurd he noend
      | (simp at he; done)
      | (dsimp only at he
         split at he
         · exact absurd he noend
         · split at he
           · exact absurd he noend
           · unfold mined at he
             split at he
             · exact absurd he nofin
             · split at he
               · exact absurd he nofin
               · split at he <;> (have := nosched he; simp at this))
      | (rename_i c m e' hph
         split at he
         · rename_i hk
           simp at he
           obtain ⟨-, rfl, rfl⟩ := he
           exact ⟨rfl, rfl, j, hjm, c, m, hph, hk⟩
         · exact absurd he nofin)

/-- A job is accepted only with a fresh `jobId` for this endpoint, a target within
the cap and room in the queue (`NapPow.submit_accepted`). -/
theorem handle_submit_accepted (h : Host) (w : World) (cx : Ctx) (s : St) (m : Mode)
    (id jobId : String) (t : Template) (target : Nat) (o : Opts)
    (hlen : s.jobs.length < (handle h w cx s (.submit m id jobId t target o)).1.jobs.length) :
    (∀ j ∈ s.jobs, j.port = cx.port → j.jobId ≠ jobId) ∧ target ≤ s.cfg.maxTarget ∧
      s.jobs.length < s.cfg.maxJobs := by
  have hout : ∃ b e, (NapPow.submit ⟨s.cfg.maxTarget, s.cfg.maxJobs⟩ (s.jobs.map toNapJob) cx.port id
      jobId t target m).2 = [.mineResult cx.port id jobId b e] := by
    unfold NapPow.submit
    split
    · exact ⟨_, _, rfl⟩
    · split
      · exact ⟨_, _, rfl⟩
      · split
        · exact ⟨_, _, rfl⟩
        · exact ⟨_, _, rfl⟩
  obtain ⟨b, e0, hout⟩ := hout
  simp only [handle] at hlen
  split at hlen
  · next _ to i jid e hsub =>
    rw [hsub] at hout
    simp only [List.cons.injEq, PowOut.mineResult.injEq, and_true] at hout
    obtain ⟨hto, hi, hjid, -, -⟩ := hout
    have hmem : PowOut.mineResult cx.port id jobId true e ∈
        (NapPow.submit ⟨s.cfg.maxTarget, s.cfg.maxJobs⟩ (s.jobs.map toNapJob) cx.port id jobId t target m).2 := by
      rw [hsub]; simp [hto, hi, hjid]
    obtain ⟨h1, h2, h3⟩ := NapPow.submit_accepted hmem
    refine ⟨fun j hj hp hid => h1 (toNapJob j) (List.mem_map_of_mem hj) hp hid, h2, by simpa using h3⟩
  · simp at hlen

/-! ### Vectors (upstream examples) -/

def mkHost (hid : String) : Host :=
  { crypto := ⟨fun _ => hid, fun _ => true⟩, verifyEvent := fun _ => true, sniff := fun _ => "",
    rasterize := fun _ => none, looksCiphertext := fun _ => false, encryptedWith := fun _ => none,
    transform := id }

def exId (d : String) : Identity := { dTag := some d, artifactHash := "h" }

def exCx : Ctx := { port := 3, window := 1, identity := exId "miner", exposed := [.pow], inst := 0 }
def otherCx : Ctx := { port := 4, window := 2, identity := exId "other", exposed := [.pow], inst := 0 }

def exWorld : World := { now := 1234567890, live := [exCx, otherCx], user := "user…" }

def run1 (h : Host) (w : World) (cx : Ctx) (s : St) (j : String) : St × List Eff :=
  match decode (Json.parse! j) with
  | .ok r => handle h w cx s r
  | _ => (s, [])

def sendsTo (p : PortId) (es : List Eff) : List Json := es.filterMap fun | .send q m => if q = p then some m else none | _ => none

def callNs (es : List Eff) : List Nat := es.filterMap fun | .call t _ => some t.n | _ => none

#guard decode (Json.parse! "{ \"type\": \"pow.mine\", \"id\": \"m1\", \"jobId\": \"job-1\", \"template\": { \"kind\": 1, \"content\": \"gm\", \"tags\": [] }, \"target\": 21, \"options\": { \"workers\": 4, \"priority\": 0 } }") matches
  .ok (.submit .mine "m1" "job-1" ⟨1, "gm", [], none⟩ 21 ⟨some 4, some 0, none, none⟩)
#guard decode (Json.parse! "{ \"type\": \"pow.queue\", \"id\": \"q1\" }") matches .ok (.queue "q1")
#guard decode (Json.parse! "{ \"type\": \"pow.pause\", \"id\": \"ps1\", \"jobId\": \"job-2\" }") matches .ok (.pause "ps1" (some "job-2"))
#guard decode (Json.parse! "{ \"type\": \"pow.hashrate\", \"id\": \"h1\" }") matches .ok (.hashrate "h1")
#guard decode (Json.parse! "{ \"type\": \"pow.formatHashRate\", \"id\": \"f\" }") matches .unknown
#guard match decode (Json.parse! "{ \"type\": \"pow.mine\", \"id\": \"m2\", \"jobId\": \"j\", \"template\": { \"kind\": 1 }, \"target\": 3 }") with
  | .reject [m] => Json.same m (Json.parse! "{\"type\":\"pow.mine.result\",\"id\":\"m2\",\"jobId\":\"j\",\"accepted\":false,\"state\":\"error\",\"error\":\"invalid template\"}")
  | _ => false

-- Example 1: job-1 queued behind a mining job and a queued job, then started, progress, done.
#guard
  let h := mkHost "000007abc…"
  let (s1, _) := run1 h exWorld otherCx .init "{ \"type\": \"pow.mine\", \"id\": \"a\", \"jobId\": \"a\", \"template\": { \"kind\": 1, \"content\": \"x\" }, \"target\": 1 }"
  let (s2, _) := run1 h exWorld otherCx s1 "{ \"type\": \"pow.mine\", \"id\": \"b\", \"jobId\": \"b\", \"template\": { \"kind\": 1, \"content\": \"y\" }, \"target\": 1 }"
  let (s3, e3) := run1 h exWorld exCx s2 "{ \"type\": \"pow.mine\", \"id\": \"m1\", \"jobId\": \"job-1\", \"template\": { \"kind\": 1, \"content\": \"gm\", \"tags\": [] }, \"target\": 21, \"options\": { \"workers\": 4, \"priority\": 0 } }"
  (match sendsTo 3 e3 with
   | [m] => Json.same m (Json.parse! "{ \"type\": \"pow.mine.result\", \"id\": \"m1\", \"jobId\": \"job-1\", \"accepted\": true, \"state\": \"queued\", \"position\": 1 }")
   | _ => false) &&
  -- the other napplet cancels both of its jobs; job-1 starts
  let (s4, _) := run1 h exWorld otherCx s3 "{ \"type\": \"pow.cancel\", \"id\": \"c\", \"jobId\": \"b\" }"
  let (s5, e5) := run1 h exWorld otherCx s4 "{ \"type\": \"pow.cancel\", \"id\": \"c\", \"jobId\": \"a\" }"
  (match sendsTo 3 e5, callNs e5 with
   | [m], [n] =>
     Json.same m (Json.parse! "{ \"type\": \"pow.state\", \"jobId\": \"job-1\", \"state\": \"mining\" }") &&
     (match onEvent h exWorld s5 (.nap .pow "progress" (Json.parse! ("{\"call\": " ++ toString n ++ ", \"bestPow\": 18, \"bestNonce\": \"773201\", \"hashes\": 2310000, \"hashRate\": 412000, \"workers\": [ { \"workerId\": 0, \"bestPow\": 18, \"hashes\": 590000, \"hashRate\": 104000 }, { \"workerId\": 1, \"bestPow\": 16, \"hashes\": 580000, \"hashRate\": 103000 }, { \"workerId\": 2, \"bestPow\": 17, \"hashes\": 575000, \"hashRate\": 102500 }, { \"workerId\": 3, \"bestPow\": 15, \"hashes\": 565000, \"hashRate\": 102500 } ], \"elapsedMs\": 5600 }"))) with
      | (s6, [.send 3 pm]) =>
        Json.same pm (Json.parse! "{ \"type\": \"pow.progress\", \"jobId\": \"job-1\", \"progress\": { \"jobId\": \"job-1\", \"target\": 21, \"state\": \"mining\", \"bestPow\": 18, \"bestNonce\": \"773201\", \"hashes\": 2310000, \"hashRate\": 412000, \"workers\": [ { \"workerId\": 0, \"bestPow\": 18, \"hashes\": 590000, \"hashRate\": 104000 }, { \"workerId\": 1, \"bestPow\": 16, \"hashes\": 580000, \"hashRate\": 103000 }, { \"workerId\": 2, \"bestPow\": 17, \"hashes\": 575000, \"hashRate\": 102500 }, { \"workerId\": 3, \"bestPow\": 15, \"hashes\": 565000, \"hashRate\": 102500 } ], \"elapsedMs\": 5600 } }") &&
        (match onReply h exWorld s6 n (.json (Json.parse! "{\"nonce\": \"1099148\", \"hashes\": 4980000, \"elapsedMs\": 12100}")) with
         | (_, [.send 3 st, .send 3 dm]) =>
           Json.same st (Json.parse! "{ \"type\": \"pow.state\", \"jobId\": \"job-1\", \"state\": \"done\" }") &&
           Json.same dm (Json.parse! "{ \"type\": \"pow.done\", \"jobId\": \"job-1\", \"result\": { \"jobId\": \"job-1\", \"ok\": true, \"pow\": 21, \"nonce\": \"1099148\", \"hashes\": 4980000, \"elapsedMs\": 12100, \"event\": { \"id\": \"000007abc…\", \"pubkey\": \"user…\", \"kind\": 1, \"content\": \"gm\", \"tags\": [[\"nonce\", \"1099148\", \"21\"]], \"created_at\": 1234567890 } } }")
         | _ => false)
      | _ => false)
   | _, _ => false)

-- Example 2: mine and publish (consent, sign, publish).
#guard
  let h := mkHost "000000def…"
  let w := { exWorld with now := 1234567999 }
  let (s1, e1) := run1 h w exCx .init "{ \"type\": \"pow.mineAndPublish\", \"id\": \"p1\", \"jobId\": \"job-2\", \"template\": { \"kind\": 1, \"content\": \"powered note\", \"tags\": [] }, \"target\": 24 }"
  (match sendsTo 3 e1, callNs e1 with
   | [m], [n] =>
     Json.same m (Json.parse! "{ \"type\": \"pow.mineAndPublish.result\", \"id\": \"p1\", \"jobId\": \"job-2\", \"accepted\": true, \"state\": \"mining\" }") &&
     (match onReply h w s1 n (.json (Json.parse! "{\"nonce\": \"55230914\", \"hashes\": 31200000, \"elapsedMs\": 74000}")) with
      | (s2, [.call ⟨.pow, n2⟩ (.prompt .pow "publish" _)]) =>
        match onReply h w s2 n2 (.decision true none) with
        | (s3, [.call ⟨.pow, n3⟩ (.sign ev)]) =>
          let signed : NostrEvent :=
            { id := "000000def…", pubkey := ev.pubkey, createdAt := ev.createdAt,
              kind := ev.kind, tags := ev.tags, content := ev.content, sig := "…" }
          match onReply h w s3 n3 (.signed (some signed)) with
          | (s4, [.call ⟨.pow, n4⟩ (.publish _ none)]) =>
            match onReply h w s4 n4 (.published [("wss://relay.example.com", true)]) with
            | (_, [.send 3 _, .send 3 dm]) =>
              Json.same dm (Json.parse! "{ \"type\": \"pow.done\", \"jobId\": \"job-2\", \"result\": { \"jobId\": \"job-2\", \"ok\": true, \"pow\": 24, \"nonce\": \"55230914\", \"hashes\": 31200000, \"elapsedMs\": 74000, \"event\": { \"id\": \"000000def…\", \"pubkey\": \"user…\", \"kind\": 1, \"content\": \"powered note\", \"tags\": [[\"nonce\", \"55230914\", \"24\"]], \"created_at\": 1234567999, \"sig\": \"…\" }, \"published\": { \"eventId\": \"000000def…\", \"relays\": { \"wss://relay.example.com\": true } } } }")
            | _ => false
          | _ => false
        | _ => false
      | _ => false)
   | _, _ => false)

-- Example 3: queue view, then pause one job.
#guard
  let h := mkHost "0"
  let (s1, e1) := run1 h exWorld exCx .init "{ \"type\": \"pow.mineAndPublish\", \"id\": \"p1\", \"jobId\": \"job-2\", \"template\": { \"kind\": 1, \"content\": \"powered note\", \"tags\": [] }, \"target\": 24 }"
  let (s2, _) := run1 h exWorld exCx s1 "{ \"type\": \"pow.mine\", \"id\": \"m3\", \"jobId\": \"job-3\", \"template\": { \"kind\": 1, \"content\": \"z\" }, \"target\": 28, \"options\": { \"priority\": 5 } }"
  match callNs e1 with
  | [n] =>
    let (s3, _) := onEvent h exWorld s2 (.nap .pow "progress" (Json.parse! ("{\"call\": " ++ toString n ++ ", \"bestPow\": 22, \"hashes\": 1, \"hashRate\": 418000, \"workers\": [], \"elapsedMs\": 1}")))
    let (s4, e4) := run1 h exWorld exCx s3 "{ \"type\": \"pow.queue\", \"id\": \"q1\" }"
    (match e4 with
     | [.send 3 m] => Json.same m (Json.parse! "{ \"type\": \"pow.queue.result\", \"id\": \"q1\", \"jobs\": [ { \"jobId\": \"job-2\", \"target\": 24, \"state\": \"mining\", \"priority\": 0, \"bestPow\": 22, \"hashRate\": 418000, \"kind\": 1, \"mode\": \"mineAndPublish\" }, { \"jobId\": \"job-3\", \"target\": 28, \"state\": \"queued\", \"priority\": 5, \"position\": 0, \"bestPow\": 0, \"hashRate\": 0, \"kind\": 1, \"mode\": \"mine\" } ] }")
     | _ => false) &&
    (match run1 h exWorld exCx s4 "{ \"type\": \"pow.pause\", \"id\": \"ps1\", \"jobId\": \"job-2\" }" with
     | (_, es) => (sendsTo 3 es).any fun m => Json.same m (Json.parse! "{ \"type\": \"pow.pause.result\", \"id\": \"ps1\", \"jobId\": \"job-2\" }"))
  | _ => false

-- Example 4: hash rate (two jobs of this napplet mining with 4 workers each).
#guard
  let h := mkHost "0"
  let s0 : St := .init { maxConcurrent := 2 }
  let (s1, e1) := run1 h exWorld exCx s0 "{ \"type\": \"pow.mine\", \"id\": \"a\", \"jobId\": \"job-1\", \"template\": { \"kind\": 1, \"content\": \"x\" }, \"target\": 20, \"options\": { \"workers\": 4 } }"
  let (s2, e2) := run1 h exWorld exCx s1 "{ \"type\": \"pow.mine\", \"id\": \"b\", \"jobId\": \"job-2\", \"template\": { \"kind\": 1, \"content\": \"y\" }, \"target\": 20, \"options\": { \"workers\": 4 } }"
  match callNs e1, callNs e2 with
  | [n1], [n2] =>
    let (s3, _) := onEvent h exWorld s2 (.nap .pow "progress" (Json.parse! ("{\"call\": " ++ toString n1 ++ ", \"bestPow\": 1, \"hashes\": 1, \"hashRate\": 412000, \"workers\": [ { \"workerId\": 0, \"bestPow\": 1, \"hashes\": 1, \"hashRate\": 103000 } ], \"elapsedMs\": 1}")))
    let (s4, _) := onEvent h exWorld s3 (.nap .pow "progress" (Json.parse! ("{\"call\": " ++ toString n2 ++ ", \"bestPow\": 1, \"hashes\": 1, \"hashRate\": 412000, \"workers\": [], \"elapsedMs\": 1}")))
    match run1 h exWorld exCx s4 "{ \"type\": \"pow.hashrate\", \"id\": \"h1\" }" with
    | (_, [.send 3 m]) => Json.same m (Json.parse! "{ \"type\": \"pow.hashrate.result\", \"id\": \"h1\", \"hashrate\": { \"hashRate\": 824000, \"workers\": 8, \"perWorker\": [ { \"workerId\": 0, \"hashRate\": 103000 } ], \"byJob\": [ { \"jobId\": \"job-1\", \"hashRate\": 412000 }, { \"jobId\": \"job-2\", \"hashRate\": 412000 } ] } }")
    | _ => false
  | _, _ => false

end Napplet.Run.Pow
