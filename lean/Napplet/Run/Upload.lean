/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Upload

/-!
# NAP-UPLOAD runtime component

Upstream: `napplet/naps` PR #33, `naps/NAP-UPLOAD.md` at `f5cc981e`.

Wire (napplet → shell): `upload.info {id}`, `upload.upload {id, request}`,
`upload.status {id, uploadId}`.
Wire (shell → napplet): `upload.info.result {id, info, error?}`,
`upload.upload.result {id, result?, error?}`, `upload.status.result {id, status?, error?}`,
and the push `upload.status.changed {status}` (no `id`).

`request` is `UploadRequest`: `data` (required), `rail?`, `mimeType?`, `filename?`,
`caption?`, `noTransform?`, `metadata?` (an object, carried as JSON).
**Modelling decision:** `data` is a `Blob`/`ArrayBuffer` in the structured clone;
the model represents it as its byte list, a JSON array of integers 0–255 (`bytesJson`).
It is never base64 (upstream forbids requiring that).

Flow of one `upload.upload` (the gates are `NapUpload.upload`'s, in its order):
1. More than `Cfg.maxActive` unfinished uploads on this endpoint → top-level
   `"quota exceeded"` (per-napplet rate limit).
2. Rail (`NapUpload.chooseRail`: requested and enabled, else the configured default)
   → `"unsupported rail"` / `"no server configured"`; the rail's server (shell
   configuration, never napplet input) → `"no server configured"`; size →
   `"file too large"`; sniffed MIME (`Host.sniff`, not the napplet's `mimeType`) →
   `"unsupported media type"`. Failing any gate creates no upload: top-level `error`.
3. An upload is created: shell-generated `uploadId` `"upload-<k>"`, status `pending`.
   If this napplet has not consented before, the user is asked (`Call.prompt`);
   a refusal ends it with `{ok: false, status: "cancelled", error: "user cancelled"}`.
   Approval is remembered for the napplet (`consented`, persistent, by manifest key).
4. The stored bytes are `data`, or `Host.transform data` (metadata stripping)
   unless `noTransform` is `true`. The shell builds the rail's authorisation over
   their SHA-256 and has the user's signer sign it (`Call.sign`): NIP-98 kind 27235
   for `nip96`, Blossom (BUD-02/BUD-11) kind 24242 for `blossom`; other rails carry
   no authorisation. A signature that does not match the template or fails
   `Host.verifyEvent` ends the upload with `"upload failed"`.
5. The gates and consent are checked again, then the bytes go to the server
   (`Call.nap .upload "put"`). If they are more than `Cfg.syncMaxBytes`, the initial
   `upload.upload.result` (status `uploading`) is sent now and the end is pushed as
   `upload.status.changed`; otherwise the result is sent when the server answers.
6. `complete` (with `url`) is reported only when the server confirmed storage and
   confirmed the hash of the bytes sent (`sha256` or `originalSha256` of its reply
   equals the shell's hash of the stored bytes). `sha256` is the server's hash of
   the stored file (NIP-94 `x`); `originalSha256` (NIP-94 `ox`) is the hash of the
   napplet's bytes, present exactly when it differs from `sha256` (shell or server
   transformed the file). `nip94` is built from these verified values
   (`url`, `m`, `x`, `ox`, `size`, `dim`, `fallback`) when `Cfg.nip94`.

Malformed requests: no string `id` → nothing; `upload.upload` whose `request` is
not an object with a byte-array `data`, or has a present optional field of the
wrong type → `upload.upload.result {id, error: "invalid request"}`; `upload.status`
without a string `uploadId` → `upload.status.result {id, error: "invalid request"}`.
A top-level `error` result omits `result`/`status` (no upload exists, so there is
no `uploadId` to report); `upload.info.result` with `error` carries `info` with no
rails (as kehto does).

Uploads are per endpoint: `uploadId` is visible only to the endpoint that created it
(scoped to the requesting napplet instance), and teardown abandons unfinished ones.

## Host operations

* `Call.prompt .upload "upload" {napplet, rail, server, size, mimeType, filename?,
  data}` → `Reply.decision allowed _`. First-upload consent for this napplet. The
  prompt MUST show the requesting napplet (`napplet` = `Ctx.catalogId`), the file
  type, size and target server, SHOULD let the user inspect `data` (byte array) and
  SHOULD say the upload will be public and durable. Any non-`decision` reply is a
  refusal.
* `Call.sign ev` (core): the rail authorisation. `ev` is the template built by
  `authTemplate`; the reply must satisfy `Call.sign`'s contract.
* `Call.nap .upload "put" {call, server, rail, auth, data, sha256, size, mimeType,
  filename?, caption?, noTransform, metadata?}` → `Reply.json`. Send `data` (byte
  array) to `server` over `rail`: for `nip96` a NIP-96 upload (`POST` to `server`,
  the configured NIP-96 `api_url`, with the NIP-98 `Authorization: Nostr <base64
  of auth>` header, `no_transform` form field from `noTransform`, `caption`,
  `content_type`); for `blossom` a BUD-02 `PUT <server>/upload` with the kind 24242
  `auth` in `Authorization: Nostr …`; for other rails the host's own protocol
  (`auth` is `null`). `sha256` is the shell's hash of `data`; `call` is the call
  tag number, used by `progress` events. Reply: on success `{ok: true, url,
  sha256, originalSha256?, size?, mimeType?, dimensions?: {width, height},
  blurhash?, fallbackUrls?}` where `sha256` is the server-reported hash of the
  stored file (Blossom descriptor `sha256`, NIP-96 `x`) and `originalSha256` the
  server-reported hash of the received bytes when it transformed them (NIP-96 `ox`);
  `url`/`fallbackUrls` are where the server says it stored the file (the host MAY
  upload to mirrors and list them). On failure `{ok: false, error?}` with `error`
  one of upstream's strings (`"server rejected"`, `"upload failed"`,
  `"quota exceeded"`, …). The host MUST NOT report `ok: true` unless the server
  confirmed storage.
* `HostEvent.nap .upload "progress" {call, bytesSent, bytesTotal}`: progress of the
  `put` with tag number `call`; pushed to the napplet as `upload.status.changed` once
  the initial result went out.
* `Effect.cancel tag`: abandon an outstanding prompt, signature or `put` when the
  endpoint is torn down.
* Pure host functions used: `Host.crypto.sha256` (FIPS 180-4), `Host.sniff`,
  `Host.transform`, `Host.verifyEvent`.
-/

namespace Napplet.Run.Upload

open NapUpload

/-! ### Configuration -/

def railName : Rail → String
  | .nip96 => "nip96" | .blossom => "blossom" | .other s => s

def railOf (s : String) : Rail :=
  if s = "nip96" then .nip96 else if s = "blossom" then .blossom else .other s

structure RailCfg where
  rail : Rail
  enabled : Bool := true
  /-- The server for this rail (NIP-96 `api_url`, Blossom server origin). -/
  server : Option String := none
  /-- URL forms disclosed in `upload.info` (`https`, `blossom`, …). -/
  returns : List String := []

structure Cfg where
  rails : List RailCfg := []
  defaultRail : Option Rail := none
  /-- Upstream example limit, and kehto's request cap. -/
  maxBytes : Nat := 100 * 1024 * 1024
  /-- Accepted sniffed MIME types; `none` accepts all. -/
  mimeTypes : Option (List String) := none
  /-- Larger uploads answer `uploading` at once and report the end by push. -/
  syncMaxBytes : Nat := 1024 * 1024
  /-- Unfinished uploads per endpoint. -/
  maxActive : Nat := 4
  /-- Blossom authorisation lifetime in seconds. -/
  authExpiry : Nat := 300
  /-- Answer `upload.info`; `false` redacts it. -/
  discloseInfo : Bool := true
  /-- Populate `nip94` in results. -/
  nip94 : Bool := true

def Cfg.railCfg (cfg : Cfg) (r : Rail) : Option RailCfg := cfg.rails.find? (·.rail == r)
def Cfg.railEnabled (cfg : Cfg) (r : Rail) : Bool := (cfg.railCfg r).any (·.enabled)
def Cfg.server (cfg : Cfg) (r : Rail) : Option String := (cfg.railCfg r).bind (·.server)
def Cfg.mimeAllowed (cfg : Cfg) (m : String) : Bool := cfg.mimeTypes.all (·.contains m)

/-! ### Requests -/

structure UploadReq where
  rail : Option String := none
  data : Bytes
  mimeType : Option String := none
  filename : Option String := none
  caption : Option String := none
  noTransform : Option Bool := none
  metadata : Option (List (String × Json)) := none
  deriving DecidableEq, Repr

inductive Req where
  | info (id : String)
  | upload (id : String) (r : UploadReq)
  | status (id : String) (uploadId : String)
  deriving DecidableEq, Repr

/-! ### Results -/

structure Res where
  ok : Bool
  status : UploadState
  url : Option String := none
  fallbackUrls : List String := []
  sha256 : Option String := none
  originalSha256 : Option String := none
  size : Option Nat := none
  mimeType : Option String := none
  dimensions : Option (Nat × Nat) := none
  blurhash : Option String := none
  nip94 : Option (List (List String)) := none
  error : Option String := none
  deriving DecidableEq, Repr

inductive Stage where
  | consent (n : Nat)
  | signing (n : Nat) (t : UnsignedEvent)
  | putting (n : Nat)
  | done
  deriving DecidableEq, Repr

def Stage.tag? : Stage → Option Nat
  | .consent n | .signing n _ | .putting n => some n
  | .done => none

structure Rec where
  uploadId : String
  port : PortId
  reqId : String
  /-- The initial `upload.upload.result` has been sent. -/
  answered : Bool
  napplet : ManifestKey
  rail : Rail
  server : String
  req : UploadReq
  stored : Bytes
  stage : Stage
  res : Res
  bytesSent : Option Nat := none
  bytesTotal : Option Nat := none
  updatedAt : Nat
  deriving DecidableEq, Repr

structure St where
  cfg : Cfg
  recs : List Rec
  /-- Napplets that consented to uploading (persistent, by manifest key). -/
  consented : List ManifestKey
  next : Nat
  nextUpload : Nat

def St.init (cfg : Cfg := {}) : St := ⟨cfg, [], [], 0, 1⟩

/-! ### Byte arrays -/

def byteOf? (j : Json) : Option UInt8 :=
  (j.asNat?).bind fun n => if n < 256 then some (UInt8.ofNat n) else none

def bytesOf? (j : Json) : Option Bytes := (j.asArr?).bind (·.mapM byteOf?)

def bytesJson (bs : Bytes) : Json := .arr (bs.map fun b => Json.nat b.toNat)

@[simp] theorem bytesOf?_bytesJson (bs : Bytes) : bytesOf? (bytesJson bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bytesOf?, bytesJson, Json.asArr?, Option.bind_some, List.map_cons, List.mapM_cons] at ih ⊢
    simp [ih, byteOf?, b.toNat_lt]

/-! ### Codec -/

def optStr (j : Json) (k : String) : Option (Option String) :=
  match j.get? k with
  | none => some none
  | some (.str s) => some (some s)
  | some _ => none

def optBool (j : Json) (k : String) : Option (Option Bool) :=
  match j.get? k with
  | none => some none
  | some (.bool b) => some (some b)
  | some _ => none

def optObj (j : Json) (k : String) : Option (Option (List (String × Json))) :=
  match j.get? k with
  | none => some none
  | some (.obj kvs) => some (some kvs)
  | some _ => none

def reqOf? (j : Json) : Option UploadReq := do
  let data ← (j.get? "data").bind bytesOf?
  let rail ← optStr j "rail"
  let mimeType ← optStr j "mimeType"
  let filename ← optStr j "filename"
  let caption ← optStr j "caption"
  let noTransform ← optBool j "noTransform"
  let metadata ← optObj j "metadata"
  some { rail, data, mimeType, filename, caption, noTransform, metadata }

def reqJson (r : UploadReq) : Json :=
  Json.mkObj [("rail", r.rail.map .str), ("data", some (bytesJson r.data)),
    ("mimeType", r.mimeType.map .str), ("filename", r.filename.map .str),
    ("caption", r.caption.map .str), ("noTransform", r.noTransform.map .bool),
    ("metadata", r.metadata.map .obj)]

def requestTypes : List String := ["upload.info", "upload.upload", "upload.status"]

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some t =>
    if t ∉ requestTypes then .unknown else
    match reqId? j with
    | none => .reject []
    | some id =>
      if t = "upload.info" then .ok (.info id)
      else if t = "upload.upload" then
        match (j.get? "request").bind reqOf? with
        | some r => .ok (.upload id r)
        | none => .reject (errorReply "upload.upload.result" j "invalid request")
      else
        match j.getStr? "uploadId" with
        | some u => .ok (.status id u)
        | none => .reject (errorReply "upload.status.result" j "invalid request")
  | none => .unknown

def encodeReq : Req → Json
  | .info id => Json.msg "upload.info" [("id", some (.str id))]
  | .upload id r => Json.msg "upload.upload" [("id", some (.str id)), ("request", some (reqJson r))]
  | .status id u => Json.msg "upload.status" [("id", some (.str id)), ("uploadId", some (.str u))]

def stateName : UploadState → String
  | .pending => "pending" | .uploading => "uploading" | .complete => "complete"
  | .failed => "failed" | .cancelled => "cancelled"

def resFields (uid : String) (rail : Rail) (r : Res) : List (String × Option Json) :=
  [("ok", some (.bool r.ok)), ("uploadId", some (.str uid)), ("status", some (.str (stateName r.status))),
   ("rail", some (.str (railName rail))), ("url", r.url.map .str),
   ("fallbackUrls", if r.fallbackUrls.isEmpty then none else some (Json.strs r.fallbackUrls)),
   ("sha256", r.sha256.map .str), ("originalSha256", r.originalSha256.map .str),
   ("size", r.size.map .nat), ("mimeType", r.mimeType.map .str),
   ("dimensions", r.dimensions.map fun (w, h) => .obj [("width", .nat w), ("height", .nat h)]),
   ("blurhash", r.blurhash.map .str), ("nip94", r.nip94.map Json.tags), ("error", r.error.map .str)]

/-- `UploadResult`. -/
def resultJson (r : Rec) : Json := Json.mkObj (resFields r.uploadId r.rail r.res)

/-- `UploadStatus`: the result fields plus progress and `updatedAt`. -/
def statusJson (r : Rec) : Json :=
  Json.mkObj (resFields r.uploadId r.rail r.res ++
    [("bytesSent", r.bytesSent.map .nat), ("bytesTotal", r.bytesTotal.map .nat),
     ("updatedAt", some (.nat r.updatedAt))])

def topError (t id e : String) : Json := Json.msg t [("id", some (.str id)), ("error", some (.str e))]

def infoJson (cfg : Cfg) : Json :=
  Json.mkObj
    [("rails", some (.arr (cfg.rails.map fun rc => Json.mkObj
        [("rail", some (.str (railName rc.rail))), ("enabled", some (.bool rc.enabled)),
         ("returns", if rc.returns.isEmpty then none else some (Json.strs rc.returns))]))),
     ("maxBytes", some (.nat cfg.maxBytes)),
     ("mimeTypes", cfg.mimeTypes.map Json.strs)]

/-! ### Policy gates (those of `NapUpload.upload`) -/

/-- The policy part of a `NapUpload.UploadEnv` built from the configuration and host. -/
def env (h : Host) (cfg : Cfg) : UploadEnv :=
  { defaultRail := cfg.defaultRail, railEnabled := cfg.railEnabled, server := cfg.server,
    maxBytes := cfg.maxBytes, mimeAllowed := cfg.mimeAllowed, sniff := h.sniff,
    transform := h.transform, sha256 := h.crypto.sha256, signAuth := fun _ _ => "",
    put := fun _ _ _ => none, userApproves := false }

def modelReq (r : UploadReq) : UploadRequest :=
  { rail := r.rail.map railOf, data := r.data, noTransform := r.noTransform == some true }

/-- Rail, server, size and MIME, in `NapUpload.upload`'s order. -/
def gates (h : Host) (cfg : Cfg) (r : UploadReq) : Except String (Rail × String) :=
  match chooseRail (env h cfg) (modelReq r) with
  | .error e => .error e
  | .ok rail =>
    match cfg.server rail with
    | none => .error "no server configured"
    | some srv =>
      if r.data.length > cfg.maxBytes then .error "file too large"
      else if cfg.mimeAllowed (h.sniff r.data) = false then .error "unsupported media type"
      else .ok (rail, srv)

/-- `gates` passed with this rail and server. -/
def gatesPass (h : Host) (cfg : Cfg) (r : UploadReq) (rail : Rail) (srv : String) : Bool :=
  match gates h cfg r with
  | .ok p => p == (rail, srv)
  | .error _ => false

theorem gatesPass_iff {h : Host} {cfg : Cfg} {r : UploadReq} {rail : Rail} {srv : String} :
    gatesPass h cfg r rail srv = true ↔ gates h cfg r = .ok (rail, srv) := by
  unfold gatesPass
  split <;> simp_all

/-- A request the gates refuse is refused by `NapUpload.upload` with the same
top-level error, whatever the server, signer and user would do. -/
theorem gates_agree (h : Host) (cfg : Cfg) (r : UploadReq) (e : String) (hg : gates h cfg r = .error e)
    (put : String → Rail → Bytes → Option String) (signAuth : Rail → Hash → String) (approves c : Bool)
    (to : Endpoint) (id : String) :
    upload { env h cfg with put, signAuth, userApproves := approves } c to id (modelReq r) =
      (c, [.topError to id e]) := by
  unfold gates at hg
  unfold upload
  simp only [chooseRail, env, modelReq] at hg ⊢
  split at hg
  · rename_i e' he
    simp only [Except.error.injEq] at hg
    subst hg
    simp only [he]
  · rename_i rail hr
    simp only [hr]
    split at hg
    · simp only [Except.error.injEq] at hg; subst hg; rename_i hs; simp [hs]
    · rename_i srv hs
      simp only [hs]
      split at hg
      · simp only [Except.error.injEq] at hg; subst hg; rename_i hl; simp [hl]
      · rename_i hl
        split at hg
        · simp only [Except.error.injEq] at hg; subst hg; rename_i hm; simp [hl, hm]
        · simp at hg

/-! ### Authorisation templates -/

/-- NIP-98 (kind 27235) for `nip96`, Blossom kind 24242 for `blossom`, nothing otherwise. -/
def authTemplate (cfg : Cfg) (now : Nat) (user : String) (r : Rec) (hash : Hash) : Option UnsignedEvent :=
  match r.rail with
  | .nip96 => some
    { pubkey := user, createdAt := now, kind := 27235, content := "",
      tags := [["u", r.server], ["method", "POST"], ["payload", hash]] }
  | .blossom => some
    { pubkey := user, createdAt := now, kind := 24242,
      content := "Upload " ++ r.req.filename.getD "blob",
      tags := [["t", "upload"], ["x", hash], ["expiration", toString (now + cfg.authExpiry)]] }
  | .other _ => none

/-- A signed event fits the template it was asked for and verifies. -/
def fits (h : Host) (t : UnsignedEvent) (ev : NostrEvent) : Bool :=
  ev.pubkey == t.pubkey && ev.createdAt == t.createdAt && ev.kind == t.kind &&
  ev.tags == t.tags && ev.content == t.content && h.verifyEvent ev

/-! ### Component -/

def putArgs (h : Host) (r : Rec) (auth : Option NostrEvent) (n : Nat) : Json :=
  Json.mkObj
    [("call", some (.nat n)), ("server", some (.str r.server)), ("rail", some (.str (railName r.rail))),
     ("auth", some (auth.elim .null NostrEvent.toJson)), ("data", some (bytesJson r.stored)),
     ("sha256", some (.str (h.crypto.sha256 r.stored))), ("size", some (.nat r.stored.length)),
     ("mimeType", some (.str (h.sniff r.stored))), ("filename", r.req.filename.map .str),
     ("caption", r.req.caption.map .str), ("noTransform", some (.bool (r.req.noTransform == some true))),
     ("metadata", r.req.metadata.map .obj)]

def setRec (s : St) (r : Rec) : St :=
  { s with recs := s.recs.map fun q => if q.uploadId = r.uploadId then r else q }

/-- Report a record: the initial result if not yet sent, otherwise a push. -/
def report (r : Rec) : Rec × Eff :=
  if r.answered then (r, .send r.port (Json.msg "upload.status.changed" [("status", some (statusJson r))]))
  else ({ r with answered := true },
        .send r.port (Json.msg "upload.upload.result" [("id", some (.str r.reqId)), ("result", some (resultJson r))]))

/-- End an upload with `res`. -/
def finish (w : World) (s : St) (r : Rec) (res : Res) : St × List Eff :=
  let (r', e) := report { r with stage := .done, res, updatedAt := w.now }
  (setRec s r', [e])

def failRes (st : UploadState) (e : String) : Res := { ok := false, status := st, error := some e }

/-- Send the bytes, after checking the gates and consent again. -/
def put (h : Host) (w : World) (s : St) (r : Rec) (auth : Option NostrEvent) : St × List Eff :=
  if gatesPass h s.cfg r.req r.rail r.server ∧ r.napplet ∈ s.consented then
    let r1 := { r with stage := .putting s.next, res := { ok := true, status := .uploading }, updatedAt := w.now }
    let call := Eff.call ⟨.upload, s.next⟩ (.nap .upload "put" (putArgs h r auth s.next))
    let s1 := { s with next := s.next + 1 }
    if r.stored.length > s.cfg.syncMaxBytes && !r.answered then
      let (r2, e) := report r1
      (setRec s1 r2, [call, e])
    else (setRec s1 r1, [call])
  else finish w s r (failRes .failed "policy denied")

/-- Ask the signer for the rail's authorisation, or go straight to `put`. -/
def authorize (h : Host) (w : World) (s : St) (r : Rec) : St × List Eff :=
  match authTemplate s.cfg w.now w.user r (h.crypto.sha256 r.stored) with
  | some t =>
    (setRec { s with next := s.next + 1 } { r with stage := .signing s.next t },
     [.call ⟨.upload, s.next⟩ (.sign t)])
  | none => put h w s r none

def consentDetails (h : Host) (cx : Ctx) (r : Rec) : Json :=
  Json.mkObj [("napplet", some (.str cx.catalogId)), ("rail", some (.str (railName r.rail))),
    ("server", some (.str r.server)), ("size", some (.nat r.stored.length)),
    ("mimeType", some (.str (h.sniff r.stored))), ("filename", r.req.filename.map .str),
    ("data", some (bytesJson r.stored))]

def active (s : St) (p : PortId) : Nat :=
  (s.recs.filter fun r => r.port == p && r.stage != .done).length

def handle (h : Host) (w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .info id =>
    if s.cfg.discloseInfo then
      (s, [.send cx.port (Json.msg "upload.info.result" [("id", some (.str id)), ("info", some (infoJson s.cfg))])])
    else
      (s, [.send cx.port (Json.msg "upload.info.result"
        [("id", some (.str id)), ("info", some (.obj [("rails", .arr [])])), ("error", some (.str "policy denied"))])])
  | .status id u =>
    match s.recs.find? (fun r => r.port == cx.port && r.uploadId == u) with
    | some r => (s, [.send cx.port (Json.msg "upload.status.result" [("id", some (.str id)), ("status", some (statusJson r))])])
    | none => (s, [.send cx.port (topError "upload.status.result" id "unknown upload")])
  | .upload id req =>
    if active s cx.port ≥ s.cfg.maxActive then (s, [.send cx.port (topError "upload.upload.result" id "quota exceeded")])
    else
    match gates h s.cfg req with
    | .error e => (s, [.send cx.port (topError "upload.upload.result" id e)])
    | .ok (rail, srv) =>
      let stored := if req.noTransform = some true then req.data else h.transform req.data
      let r : Rec :=
        { uploadId := "upload-" ++ toString s.nextUpload, port := cx.port, reqId := id,
          answered := false, napplet := cx.identity.key, rail := rail, server := srv, req := req,
          stored := stored, stage := .done, res := { ok := true, status := .pending }, updatedAt := w.now }
      let s1 := { s with recs := s.recs ++ [r], nextUpload := s.nextUpload + 1 }
      if cx.identity.key ∈ s.consented then authorize h w s1 r
      else
        (setRec { s1 with next := s1.next + 1 } { r with stage := .consent s1.next },
         [.call ⟨.upload, s1.next⟩ (.prompt .upload "upload" (consentDetails h cx r))])

/-- Interpret the server's answer to `put`. -/
def interpret (h : Host) (cfg : Cfg) (r : Rec) (j : Json) : Res :=
  let x := j.getStr? "sha256"
  let ox := j.getStr? "originalSha256"
  let mine := h.crypto.sha256 r.stored
  let orig := h.crypto.sha256 r.req.data
  if j.get? "ok" = some (.bool true) then
    match j.getStr? "url", x with
    | some url, some xs =>
      if xs = mine ∨ ox = some mine then
        let osha := if xs = orig then none else some orig
        let size := ((j.get? "size").bind Json.asNat?).getD r.stored.length
        let mime := (j.getStr? "mimeType").getD (h.sniff r.stored)
        let dims := (j.get? "dimensions").bind fun d => do
          some ((← (d.get? "width").bind Json.asNat?), (← (d.get? "height").bind Json.asNat?))
        let fallback := ((j.get? "fallbackUrls").bind Json.asStrs?).getD []
        let nip94 := if cfg.nip94 then
            some ([["url", url], ["m", mime], ["x", xs]] ++ (osha.map fun o => ["ox", o]).toList ++
              [["size", toString size]] ++ (dims.map fun (w, hh) => ["dim", toString w ++ "x" ++ toString hh]).toList ++
              fallback.map fun f => ["fallback", f])
          else none
        { ok := true, status := .complete, url := some url, fallbackUrls := fallback, sha256 := some xs,
          originalSha256 := osha, size := some size, mimeType := some mime, dimensions := dims,
          blurhash := j.getStr? "blurhash", nip94 }
      else failRes .failed "server rejected"
    | _, _ => failRes .failed "server rejected"
  else failRes .failed ((j.getStr? "error").getD "upload failed")

def onReply (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.recs.find? (fun r => r.stage.tag? == some n) with
  | none => (s, [])
  | some r =>
    match r.stage, rep with
    | .consent _, .decision true _ =>
      authorize h w { s with consented := if r.napplet ∈ s.consented then s.consented else r.napplet :: s.consented } r
    | .consent _, _ => finish w s r (failRes .cancelled "user cancelled")
    | .signing _ t, .signed (some ev) =>
      if fits h t ev then put h w s r (some ev) else finish w s r (failRes .failed "upload failed")
    | .signing _ _, _ => finish w s r (failRes .failed "upload failed")
    | .putting _, .json j => finish w s r (interpret h s.cfg r j)
    | .putting _, _ => finish w s r (failRes .failed "upload failed")
    | .done, _ => (s, [])

def onEvent (_h : Host) (w : World) (s : St) : HostEvent → St × List Eff
  | .nap .upload "progress" a =>
    match (a.get? "call").bind Json.asNat? with
    | none => (s, [])
    | some n =>
      match s.recs.find? (fun r => r.stage == .putting n) with
      | none => (s, [])
      | some r =>
        let r1 := { r with bytesSent := (a.get? "bytesSent").bind Json.asNat?,
                           bytesTotal := (a.get? "bytesTotal").bind Json.asNat?, updatedAt := w.now }
        if r.answered then
          (setRec s r1, [.send r.port (Json.msg "upload.status.changed" [("status", some (statusJson r1))])])
        else (setRec s r1, [])
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with recs := s.recs.filter (·.port != p) },
   ((s.recs.filter (·.port == p)).filterMap (·.stage.tag?)).map fun n => .effect (.cancel ⟨.upload, n⟩))

def mentions (s : St) (p : PortId) : Bool := s.recs.any (·.port == p)

/-! ### Properties: codec -/

theorem reqOf?_reqJson (r : UploadReq) : reqOf? (reqJson r) = some r := by
  obtain ⟨ra, d, m, f, c, nt, md⟩ := r
  cases ra <;> cases m <;> cases f <;> cases c <;> cases nt <;> cases md <;>
    simp [reqOf?, reqJson, Json.mkObj, Json.get?, Json.lookup, optStr, optBool, optObj]

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r with
  | info id => simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]
  | status id u => simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]
  | upload id r =>
    have := reqOf?_reqJson r
    simp [decode, encodeReq, requestTypes, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?, this]

/-! ### Properties: per-endpoint state -/

/-- Ports held by records only change by adding records of the requesting endpoint. -/
def ports (s : St) : List PortId := s.recs.map (·.port)

theorem mentions_iff (s : St) (q : PortId) : mentions s q = true ↔ q ∈ ports s := by
  simp only [mentions, ports, List.any_eq_true, beq_iff_eq, List.mem_map]

theorem ports_setRec {s : St} {r : Rec} {q : PortId} (hq : q ∈ ports (setRec s r)) : q ∈ ports s ∨ q = r.port := by
  simp only [ports, setRec, List.map_map, List.mem_map] at hq ⊢
  obtain ⟨x, hx, hxq⟩ := hq
  by_cases hu : x.uploadId = r.uploadId
  · right; simp only [Function.comp, hu, ite_true] at hxq; exact hxq.symm
  · left; exact ⟨x, hx, by simpa only [Function.comp, hu, ite_false] using hxq⟩

theorem ports_report (r : Rec) : (report r).1.port = r.port := by
  unfold report; split <;> rfl

/-- Every port a step leaves in the records was already there or is `p`. -/
def Within (s s' : St) (p : PortId) : Prop := ∀ q ∈ ports s', q ∈ ports s ∨ q = p

theorem within_setRec {s s' : St} {p : PortId} {r : Rec} (hw : Within s s' p) (hr : r.port = p) :
    Within s (setRec s' r) p := by
  intro q hq
  rcases ports_setRec hq with h | h
  · exact hw q h
  · exact .inr (h.trans hr)

theorem within_refl (s : St) (p : PortId) : Within s s p := fun _ h => .inl h

theorem finish_within (w : World) (s : St) (r : Rec) (res : Res) :
    Within s (finish w s r res).1 r.port := by
  simp only [finish]
  exact within_setRec (within_refl _ _) (ports_report _)

theorem put_within (h : Host) (w : World) (s : St) (r : Rec) (auth : Option NostrEvent) :
    Within s (put h w s r auth).1 r.port := by
  simp only [put]
  split
  · split
    · exact within_setRec (fun q hq => .inl hq) (ports_report _)
    · exact within_setRec (fun q hq => .inl hq) rfl
  · exact finish_within w s r _

theorem authorize_within (h : Host) (w : World) (s : St) (r : Rec) :
    Within s (authorize h w s r).1 r.port := by
  simp only [authorize]
  split
  · exact within_setRec (fun q hq => .inl hq) rfl
  · exact put_within h w s r none

theorem within_trans {s1 s2 s3 : St} {p : PortId} (h1 : Within s1 s2 p) (h2 : Within s2 s3 p) : Within s1 s3 p := by
  intro q hq
  rcases h2 q hq with h | h
  · exact h1 q h
  · exact .inr h

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp [drop, mentions] at h ⊢
  obtain ⟨x, hx, -, hq⟩ := h
  exact ⟨x, hx, hq⟩

theorem within_append (s s' : St) (r : Rec) (p : PortId) (hs : s'.recs = s.recs ++ [r]) (hr : r.port = p) :
    Within s s' p := by
  intro q hq
  simp only [ports, hs, List.map_append, List.mem_append, List.map_cons, List.map_nil,
    List.mem_singleton] at hq
  rcases hq with hq | hq
  · exact .inl hq
  · exact .inr (hq.trans hr)

theorem handle_within (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    Within s (handle h w cx s r).1 cx.port := by
  cases r with
  | info id => simp only [handle]; split <;> exact within_refl _ _
  | status id u => simp only [handle]; split <;> exact within_refl _ _
  | upload id req =>
    simp only [handle]
    split
    · exact within_refl _ _
    · split
      · exact within_refl _ _
      · split
        · exact within_trans (within_append _ _ _ _ rfl rfl) (authorize_within h w _ _)
        · exact within_setRec (within_append _ _ _ _ rfl rfl) rfl

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  rw [mentions_iff] at hm ⊢
  rcases handle_within h w cx s r q hm with h1 | h1
  · exact .inl h1
  · exact .inr ⟨cx, hcx, h1.symm⟩

theorem onReply_within (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) :
    ∀ q ∈ ports (onReply h w s n rep).1, q ∈ ports s := by
  intro q hq
  simp only [onReply] at hq
  split at hq
  · exact hq
  · rename_i r hr
    have hp : r.port ∈ ports s := List.mem_map_of_mem (List.mem_of_find?_eq_some hr)
    have fin : ∀ s', Within s s' r.port → q ∈ ports s' → q ∈ ports s := fun s' hw hq' =>
      (hw q hq').elim id (fun e => e ▸ hp)
    split at hq
    · refine fin _ ?_ hq
      exact within_trans (fun q hq => .inl hq) (authorize_within h w _ r)
    · exact fin _ (finish_within w s r _) hq
    · split at hq
      · exact fin _ (put_within h w s r _) hq
      · exact fin _ (finish_within w s r _) hq
    · exact fin _ (finish_within w s r _) hq
    · exact fin _ (finish_within w s r _) hq
    · exact fin _ (finish_within w s r _) hq
    · exact hq

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  rw [mentions_iff] at hm ⊢
  exact .inl (onReply_within h w s n rep q hm)

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  rw [mentions_iff] at hm ⊢
  simp only [onEvent] at hm
  split at hm
  · split at hm
    · exact hm
    · split at hm
      · exact hm
      · rename_i r hr
        have hp : r.port ∈ ports s := List.mem_map_of_mem (List.mem_of_find?_eq_some hr)
        split at hm <;> (dsimp only at hm; rcases ports_setRec hm with h1 | h1; exact h1; exact h1 ▸ hp)
  · exact hm

/-! ### Properties lifted from `NapUpload` -/

theorem setRec_consented (s : St) (r : Rec) : (setRec s r).consented = s.consented := rfl

theorem put_consented (h : Host) (w : World) (s : St) (r : Rec) (a : Option NostrEvent) :
    (put h w s r a).1.consented = s.consented := by
  simp only [put, finish]; split
  · split <;> rfl
  · rfl

theorem authorize_consented (h : Host) (w : World) (s : St) (r : Rec) :
    (authorize h w s r).1.consented = s.consented := by
  simp only [authorize]; split
  · rfl
  · exact put_consented h w s r none

/-- Consent is never revoked by a request (latch). -/
theorem handle_consent_latch (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    (handle h w cx s r).1.consented = s.consented := by
  cases r with
  | info => simp only [handle]; split <;> rfl
  | status => simp only [handle]; split <;> rfl
  | upload id req =>
    simp only [handle]
    split
    · rfl
    · split
      · rfl
      · split
        · exact authorize_consented h w _ _
        · rfl

/-- Consent only grows, and only on the user's approval of a consent prompt. -/
theorem onReply_consent (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (k : ManifestKey) :
    (k ∈ s.consented → k ∈ (onReply h w s n rep).1.consented) ∧
    (k ∈ (onReply h w s n rep).1.consented → k ∈ s.consented ∨ ∃ c, rep = .decision true c) := by
  simp only [onReply]
  split
  · exact ⟨id, .inl⟩
  · rename_i r _
    split
    · rename_i c
      rw [authorize_consented]
      dsimp only
      constructor
      · intro hk; split <;> simp [hk]
      · intro hk
        split at hk
        · exact .inl hk
        · simp only [List.mem_cons] at hk
          rcases hk with rfl | hk
          · exact .inr ⟨_, rfl⟩
          · exact .inl hk
    all_goals first
      | (simp only [finish, setRec_consented]; exact ⟨id, .inl⟩)
      | (split <;> first | (rw [put_consented]; exact ⟨id, .inl⟩)
                         | (simp only [finish, setRec_consented]; exact ⟨id, .inl⟩))
      | exact ⟨id, .inl⟩

/-- Bytes leave the shell only from `put`, after the policy gates passed for this
record (rail enabled, shell-configured server, size, sniffed MIME) and the napplet
consented. -/
theorem put_sends_only_checked (h : Host) (w : World) (s : St) (r : Rec) (auth : Option NostrEvent)
    (t : CallTag) (a : Json) (he : Eff.call t (.nap .upload "put" a) ∈ (put h w s r auth).2) :
    gates h s.cfg r.req = .ok (r.rail, r.server) ∧ r.napplet ∈ s.consented ∧
    a = putArgs h r auth t.n := by
  simp only [put] at he
  split at he
  · rename_i hg
    split at he
    · simp only [List.mem_cons] at he
      rcases he with he | he
      · simp at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨gatesPass_iff.mp hg.1, hg.2, rfl⟩
      · unfold report at he; split at he <;> simp at he
    · simp at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨gatesPass_iff.mp hg.1, hg.2, rfl⟩
  · simp only [finish] at he
    unfold report at he; split at he <;> simp at he

theorem authorize_puts (h : Host) (w : World) (s : St) (r : Rec) (t : CallTag) (a : Json)
    (he : Eff.call t (.nap .upload "put" a) ∈ (authorize h w s r).2) :
    gates h s.cfg r.req = .ok (r.rail, r.server) ∧ r.napplet ∈ s.consented ∧
    authTemplate s.cfg w.now w.user r (h.crypto.sha256 r.stored) = none ∧ a = putArgs h r none t.n := by
  simp only [authorize] at he
  split at he
  · simp at he
  · rename_i ht
    exact ⟨(put_sends_only_checked h w s r none t a he).1, (put_sends_only_checked h w s r none t a he).2.1,
      ht, (put_sends_only_checked h w s r none t a he).2.2⟩

/-- A request sends bytes only for an already-consented napplet, through a rail
that needs no signed authorisation, after the policy gates. -/
theorem handle_put_requires_policy (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (t : CallTag)
    (a : Json) (he : Eff.call t (.nap .upload "put" a) ∈ (handle h w cx s r).2) :
    cx.identity.key ∈ s.consented ∧ ∃ rec, gates h s.cfg rec.req = .ok (rec.rail, rec.server) ∧
      a = putArgs h rec none t.n := by
  cases r with
  | info => simp only [handle] at he; split at he <;> simp at he
  | status => simp only [handle] at he; split at he <;> simp at he
  | upload id req =>
    simp only [handle] at he
    split at he
    · simp at he
    · split at he
      · simp at he
      · split at he
        · rename_i hk
          obtain ⟨hg, -, -, ha⟩ := authorize_puts h w _ _ t a he
          exact ⟨hk, _, hg, ha⟩
        · simp at he

/-- A host reply sends bytes only after the gates passed and the napplet consented
(earlier, or by this very approval); with an authorisation that the signer
produced for the shell's template (kind 27235 or 24242 over the stored bytes'
hash) and that verifies; or with none for a rail that has no authorisation. -/
theorem onReply_put_requires_policy (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (t : CallTag)
    (a : Json) (he : Eff.call t (.nap .upload "put" a) ∈ (onReply h w s n rep).2) :
    ∃ rec, gates h s.cfg rec.req = .ok (rec.rail, rec.server) ∧
      (rec.napplet ∈ s.consented ∨ ∃ c, rep = .decision true c) ∧
      ((∃ now user, authTemplate s.cfg now user rec (h.crypto.sha256 rec.stored) = none ∧ a = putArgs h rec none t.n) ∨
       (∃ tmpl ev, rec.stage = .signing n tmpl ∧ rep = .signed (some ev) ∧ fits h tmpl ev = true ∧
          a = putArgs h rec (some ev) t.n)) := by
  simp only [onReply] at he
  split at he
  · simp at he
  · rename_i r hr
    have hn : r.stage.tag? = some n := by have := List.find?_some hr; simpa using this
    split at he
    · obtain ⟨hg, hk, ht, ha⟩ := authorize_puts h w _ r t a he
      exact ⟨r, hg, .inr ⟨_, rfl⟩, .inl ⟨_, _, ht, ha⟩⟩
    · simp only [finish] at he; unfold report at he; split at he <;> simp at he
    · rename_i n' tm ev hs
      split at he
      · rename_i hf
        obtain ⟨hg, hk, ha⟩ := put_sends_only_checked h w s r _ t a he
        have : n' = n := by rw [hs] at hn; simpa [Stage.tag?] using hn
        subst this
        exact ⟨r, hg, .inl hk, .inr ⟨tm, ev, hs, rfl, hf, ha⟩⟩
      · simp only [finish] at he; unfold report at he; split at he <;> simp at he
    all_goals first
      | simp at he
      | (simp only [finish] at he; unfold report at he; split at he <;> simp at he)

/-- The shell's authorisation templates commit to the stored bytes' hash. -/
theorem authTemplate_hash (cfg : Cfg) (now : Nat) (user : String) (r : Rec) (hash : Hash) (t : UnsignedEvent)
    (ht : authTemplate cfg now user r hash = some t) :
    (t.kind = 27235 ∧ ["payload", hash] ∈ t.tags) ∨ (t.kind = 24242 ∧ ["x", hash] ∈ t.tags) := by
  unfold authTemplate at ht
  split at ht
  · simp only [Option.some.injEq] at ht; subst ht; simp
  · simp only [Option.some.injEq] at ht; subst ht; simp
  · simp at ht

/-- A signing stage always asks for the shell's own template. -/
theorem authorize_signs (h : Host) (w : World) (s : St) (r : Rec) (t : CallTag) (ev : UnsignedEvent)
    (he : Eff.call t (.sign ev) ∈ (authorize h w s r).2) :
    authTemplate s.cfg w.now w.user r (h.crypto.sha256 r.stored) = some ev := by
  simp only [authorize] at he
  split at he
  · rename_i tm htm; simp at he; rw [htm, he.2]
  · simp only [put] at he
    split at he
    · split at he
      · simp only [List.mem_cons] at he
        rcases he with he | he
        · simp at he
        · unfold report at he; split at he <;> simp at he
      · simp at he
    · simp only [finish] at he; unfold report at he; split at he <;> simp at he

/-- `complete` is reported only when the server confirmed storage with a URL and
confirmed the hash of the bytes the shell sent; `sha256` is the server's hash of the
stored file and `originalSha256` is reported exactly when that differs from the
hash of the napplet's bytes. -/
theorem interpret_complete (h : Host) (cfg : Cfg) (r : Rec) (j : Json) (hc : (interpret h cfg r j).status = .complete) :
    j.get? "ok" = some (.bool true) ∧ ∃ url x, j.getStr? "url" = some url ∧ j.getStr? "sha256" = some x ∧
      (x = h.crypto.sha256 r.stored ∨ j.getStr? "originalSha256" = some (h.crypto.sha256 r.stored)) ∧
      (interpret h cfg r j).url = some url ∧ (interpret h cfg r j).sha256 = some x ∧
      ((interpret h cfg r j).originalSha256.isSome ↔ x ≠ h.crypto.sha256 r.req.data) := by
  unfold interpret at hc ⊢
  dsimp only at hc ⊢
  split at hc
  · rename_i hok
    split at hc
    · rename_i url xs hu hx
      split at hc
      · rename_i hconf
        simp only [hok, hu, hx, if_pos hconf, ite_true]
        refine ⟨trivial, url, xs, rfl, rfl, ?_, rfl, rfl, ?_⟩
        · rcases hconf with h1 | h1
          · exact .inl h1
          · exact .inr h1
        · split <;> simp_all
      · simp [failRes] at hc
    · simp [failRes] at hc
  · simp [failRes] at hc

theorem mem_setRec {s : St} {r x : Rec} (hx : x ∈ (setRec s r).recs) : x ∈ s.recs ∨ x = r := by
  simp only [setRec, List.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  split at hyx
  · exact .inr hyx.symm
  · exact .inl (hyx ▸ hy)

theorem report_res (r : Rec) : (report r).1.res = r.res := by
  unfold report; split <;> rfl

theorem finish_recs {w : World} {s : St} {r x : Rec} {res : Res} (hx : x ∈ (finish w s r res).1.recs) :
    x ∈ s.recs ∨ x.res = res := by
  simp only [finish] at hx
  rcases mem_setRec hx with h1 | h1
  · exact .inl h1
  · exact .inr (h1 ▸ report_res _)

theorem put_recs {h : Host} {w : World} {s : St} {r x : Rec} {a : Option NostrEvent}
    (hx : x ∈ (put h w s r a).1.recs) : x ∈ s.recs ∨ x.res.status ≠ .complete := by
  simp only [put] at hx
  split at hx
  · split at hx
    · rcases mem_setRec hx with h1 | h1
      · exact .inl h1
      · exact .inr (by rw [h1, report_res]; simp)
    · rcases mem_setRec hx with h1 | h1
      · exact .inl h1
      · exact .inr (by rw [h1]; simp)
  · rcases finish_recs hx with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [h1]; simp [failRes])

theorem authorize_recs {h : Host} {w : World} {s : St} {r x : Rec} (hx : x ∈ (authorize h w s r).1.recs) :
    x ∈ s.recs ∨ x.res = r.res ∨ x.res.status ≠ .complete := by
  simp only [authorize] at hx
  split at hx
  · rcases mem_setRec hx with h1 | h1
    · exact .inl h1
    · exact .inr (.inl (by rw [h1]))
  · rcases put_recs hx with h1 | h1
    · exact .inl h1
    · exact .inr (.inr h1)

/-- A record is `complete` after a host reply only if it already was, or the reply
is the server's answer to this record's `put` and `interpret` judged it complete
(so `interpret_complete` applies). -/
theorem onReply_complete (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (x : Rec)
    (hx : x ∈ (onReply h w s n rep).1.recs) (hc : x.res.status = .complete) :
    (∃ r ∈ s.recs, x.res = r.res) ∨
    ∃ r ∈ s.recs, ∃ j, r.stage = .putting n ∧ rep = .json j ∧ x.res = interpret h s.cfg r j := by
  simp only [onReply] at hx
  split at hx
  · exact .inl ⟨x, hx, rfl⟩
  · rename_i r hr
    have hrm := List.mem_of_find?_eq_some hr
    have hn : r.stage.tag? = some n := by have := List.find?_some hr; simpa using this
    have old : x ∈ s.recs → (∃ r ∈ s.recs, x.res = r.res) ∨
        ∃ r ∈ s.recs, ∃ j, r.stage = .putting n ∧ rep = .json j ∧ x.res = interpret h s.cfg r j :=
      fun h1 => Or.inl ⟨x, h1, rfl⟩
    split at hx
    · rcases authorize_recs hx with h1 | h1 | h1
      · exact old h1
      · exact .inl ⟨r, hrm, h1⟩
      · exact absurd hc h1
    · rcases finish_recs hx with h1 | h1
      · exact old h1
      · simp [h1, failRes] at hc
    · split at hx
      · rcases put_recs hx with h1 | h1
        · exact old h1
        · exact absurd hc h1
      · rcases finish_recs hx with h1 | h1
        · exact old h1
        · simp [h1, failRes] at hc
    · rcases finish_recs hx with h1 | h1
      · exact old h1
      · simp [h1, failRes] at hc
    · rename_i n' j hs
      rcases finish_recs hx with h1 | h1
      · exact old h1
      · have : n' = n := by rw [hs] at hn; simpa [Stage.tag?] using hn
        subst this
        exact .inr ⟨r, hrm, j, hs, rfl, h1⟩
    · rcases finish_recs hx with h1 | h1
      · exact old h1
      · simp [h1, failRes] at hc
    · exact old hx

/-- A request never reports `complete`: new records start `pending`, and `put`
starts `uploading`. -/
theorem handle_no_complete (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (x : Rec)
    (hx : x ∈ (handle h w cx s r).1.recs) (hc : x.res.status = .complete) : ∃ q ∈ s.recs, x.res = q.res := by
  cases r with
  | info => simp only [handle] at hx; split at hx <;> exact ⟨x, hx, rfl⟩
  | status => simp only [handle] at hx; split at hx <;> exact ⟨x, hx, rfl⟩
  | upload id req =>
    simp only [handle] at hx
    split at hx
    · exact ⟨x, hx, rfl⟩
    · split at hx
      · exact ⟨x, hx, rfl⟩
      · split at hx
        · rcases authorize_recs hx with h1 | h1 | h1
          · simp only [List.mem_append, List.mem_singleton] at h1
            rcases h1 with h1 | h1
            · exact ⟨x, h1, rfl⟩
            · rw [h1] at hc; simp at hc
          · rw [h1] at hc; simp at hc
          · exact absurd hc h1
        · rcases mem_setRec hx with h1 | h1
          · simp only [List.mem_append, List.mem_singleton] at h1
            rcases h1 with h1 | h1
            · exact ⟨x, h1, rfl⟩
            · rw [h1] at hc; simp at hc
          · rw [h1] at hc; simp at hc

/-! ### Vectors (upstream examples) -/

def sampleHost (sha : String) (mime : String) : Host :=
  { crypto := ⟨fun _ => sha, fun _ => true⟩, verifyEvent := fun _ => true,
    sniff := fun _ => mime, rasterize := fun _ => none,
    looksCiphertext := fun _ => false, encryptedWith := fun _ => none, transform := id }

def sampleCtx : Ctx :=
  { port := 5, window := 2, identity := { dTag := some "notes", artifactHash := "aa", publisher := "pk" },
    exposed := [.upload], inst := 0 }

def sampleWorld (now : Nat) : World := { now, live := [sampleCtx], user := "userpk" }

def sampleCfg : Cfg :=
  { rails := [{ rail := .nip96, server := some "https://files.example.com/api/v2/media", returns := ["https"] },
              { rail := .blossom, server := some "https://blossom.example.com", returns := ["https", "blossom"] }],
    defaultRail := some .nip96, maxBytes := 104857600,
    mimeTypes := some ["image/png", "image/jpeg", "application/pdf"] }

def sends (es : List Eff) : List Json := es.filterMap fun | .send _ m => some m | _ => none

def decodeOk (j : Json) : Option Req := match decode j with | .ok r => some r | _ => none

#guard match decodeOk (Json.parse! "{ \"type\": \"upload.info\", \"id\": \"i1\" }") with
  | some r => match sends (handle (sampleHost "" "") (sampleWorld 0) sampleCtx (.init sampleCfg) r).2 with
    | [m] => Json.same m (Json.parse! "{ \"type\": \"upload.info.result\", \"id\": \"i1\", \"info\": { \"rails\": [ { \"rail\": \"nip96\", \"enabled\": true, \"returns\": [\"https\"] }, { \"rail\": \"blossom\", \"enabled\": true, \"returns\": [\"https\", \"blossom\"] } ], \"maxBytes\": 104857600, \"mimeTypes\": [\"image/png\", \"image/jpeg\", \"application/pdf\"] } }")
    | _ => false
  | none => false

-- Upload an image (asynchronous: `uploading`, then `upload.status.changed`).
def ex1Req : Json := Json.parse! "{ \"type\": \"upload.upload\", \"id\": \"u1\", \"request\": { \"rail\": \"nip96\", \"data\": [137, 80, 78, 71], \"filename\": \"diagram.png\", \"caption\": \"architecture diagram\", \"mimeType\": \"image/png\" } }"
def ex1Host : Host := sampleHost "def456..." "image/png"
def ex1Cfg : Cfg := { sampleCfg with syncMaxBytes := 0 }
def ex1St : St := { St.init ex1Cfg with nextUpload := 1, consented := [sampleCtx.identity.key] }
def ex1PutReply : Json := Json.parse! "{ \"ok\": true, \"url\": \"https://files.example.com/abc123.png\", \"sha256\": \"abc123...\", \"originalSha256\": \"def456...\", \"size\": 18234, \"mimeType\": \"image/png\", \"dimensions\": { \"width\": 1280, \"height\": 720 }, \"blurhash\": \"L6PZfSi_.AyE_3t7t7R**0o#DgR4\" }"

#guard match decodeOk ex1Req with
  | some r =>
    match handle ex1Host (sampleWorld 1234567890) sampleCtx ex1St r with
    | (s1, [.call ⟨.upload, 0⟩ (.sign t)]) =>
      t.kind == 27235 && t.tags == [["u", "https://files.example.com/api/v2/media"], ["method", "POST"], ["payload", "def456..."]] &&
      (let ev : NostrEvent := ⟨"e", t.pubkey, t.createdAt, t.kind, t.tags, t.content, "s"⟩
       match onReply ex1Host (sampleWorld 1234567891) s1 0 (.signed (some ev)) with
       | (s2, [.call ⟨.upload, 1⟩ (.nap .upload "put" _), .send 5 m]) =>
         Json.same m (Json.parse! "{ \"type\": \"upload.upload.result\", \"id\": \"u1\", \"result\": { \"ok\": true, \"uploadId\": \"upload-1\", \"status\": \"uploading\", \"rail\": \"nip96\" } }") &&
         (match sends (onReply ex1Host (sampleWorld 1234567901) s2 1 (.json ex1PutReply)).2 with
          | [m'] => Json.same m' (Json.parse! "{ \"type\": \"upload.status.changed\", \"status\": { \"ok\": true, \"uploadId\": \"upload-1\", \"status\": \"complete\", \"rail\": \"nip96\", \"url\": \"https://files.example.com/abc123.png\", \"sha256\": \"abc123...\", \"originalSha256\": \"def456...\", \"size\": 18234, \"mimeType\": \"image/png\", \"dimensions\": { \"width\": 1280, \"height\": 720 }, \"blurhash\": \"L6PZfSi_.AyE_3t7t7R**0o#DgR4\", \"nip94\": [ [\"url\", \"https://files.example.com/abc123.png\"], [\"m\", \"image/png\"], [\"x\", \"abc123...\"], [\"ox\", \"def456...\"], [\"size\", \"18234\"], [\"dim\", \"1280x720\"] ], \"updatedAt\": 1234567901 } }")
          | _ => false)
       | _ => false)
    | _ => false
  | none => false

-- Upload a blob to Blossom (synchronous: the result carries `complete`).
def ex2Req : Json := Json.parse! "{ \"type\": \"upload.upload\", \"id\": \"u2\", \"request\": { \"rail\": \"blossom\", \"data\": [37, 80, 68, 70], \"filename\": \"notes.pdf\" } }"
def ex2Host : Host := sampleHost "sha256hash..." "application/pdf"
def ex2St : St := { St.init { sampleCfg with nip94 := false } with nextUpload := 2, consented := [sampleCtx.identity.key] }

#guard match decodeOk ex2Req with
  | some r =>
    match handle ex2Host (sampleWorld 100) sampleCtx ex2St r with
    | (s1, [.call ⟨.upload, 0⟩ (.sign t)]) =>
      t.kind == 24242 && t.content == "Upload notes.pdf" &&
      t.tags == [["t", "upload"], ["x", "sha256hash..."], ["expiration", "400"]] &&
      (let ev : NostrEvent := ⟨"e", t.pubkey, t.createdAt, t.kind, t.tags, t.content, "s"⟩
       match onReply ex2Host (sampleWorld 101) s1 0 (.signed (some ev)) with
       | (s2, [.call ⟨.upload, 1⟩ (.nap .upload "put" _)]) =>
         (match sends (onReply ex2Host (sampleWorld 102) s2 1 (.json (Json.parse! "{ \"ok\": true, \"url\": \"https://blossom.example.com/sha256hash.pdf\", \"sha256\": \"sha256hash...\", \"size\": 90211, \"mimeType\": \"application/pdf\" }"))).2 with
          | [m] => Json.same m (Json.parse! "{ \"type\": \"upload.upload.result\", \"id\": \"u2\", \"result\": { \"ok\": true, \"uploadId\": \"upload-2\", \"status\": \"complete\", \"rail\": \"blossom\", \"url\": \"https://blossom.example.com/sha256hash.pdf\", \"sha256\": \"sha256hash...\", \"size\": 90211, \"mimeType\": \"application/pdf\" } }")
          | _ => false)
       | _ => false)
    | _ => false
  | none => false

-- User cancelled at the consent prompt.
#guard match handle ex1Host (sampleWorld 1) sampleCtx { St.init sampleCfg with nextUpload := 3 }
    (.upload "u3" { rail := some "nip96", data := [1, 2, 3] }) with
  | (s1, [.call ⟨.upload, 0⟩ (.prompt .upload "upload" _)]) =>
    match sends (onReply ex1Host (sampleWorld 2) s1 0 (.decision false none)).2 with
    | [m] => Json.same m (Json.parse! "{ \"type\": \"upload.upload.result\", \"id\": \"u3\", \"result\": { \"ok\": false, \"uploadId\": \"upload-3\", \"status\": \"cancelled\", \"rail\": \"nip96\", \"error\": \"user cancelled\" } }")
    | _ => false
  | _ => false

-- Gate failures are top-level errors; malformed requests are `invalid request`.
#guard match sends (handle ex1Host (sampleWorld 1) sampleCtx (.init sampleCfg) (.upload "u4" { rail := some "ftp", data := [1] })).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"upload.upload.result\", \"id\": \"u4\", \"error\": \"unsupported rail\" }")
  | _ => false
#guard match decode (Json.parse! "{ \"type\": \"upload.upload\", \"id\": \"u5\", \"request\": { \"data\": \"aGk=\" } }") with
  | .reject [m] => Json.same m (Json.parse! "{ \"type\": \"upload.upload.result\", \"id\": \"u5\", \"error\": \"invalid request\" }")
  | _ => false
#guard decode (Json.parse! "{ \"type\": \"upload.delete\", \"id\": \"u6\" }") matches .unknown

end Napplet.Run.Upload
