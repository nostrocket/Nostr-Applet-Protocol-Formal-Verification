/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# NAP-UPLOAD (`upload`, PR napplet/naps#33 branch `nap-upload`)

Shell-mediated upload (NIP-96, Blossom). The request carries no server, URL or
credential: server choice, authorisation signing and storage are shell-side.

Results:
* `send_requires_policy`: bytes leave the shell only if rail, size, MIME and consent
  policy all passed, to the server the shell configured for that rail.
* `send_auth_by_shell`: the upload authorisation is the shell's signature over the
  hash of the stored bytes.
* `complete_requires_confirmation`: a `complete` result with a URL is reported only
  when the server confirmed storing those bytes.
* `complete_hashes`: `sha256` is the hash of the stored bytes, and `originalSha256`
  is reported exactly when the shell transformed them.
* `consent_latch`: consent is remembered once given and never revoked by a request.
* `unsupported_rail_no_send`, `rejected_no_send`, `upload_same_id`.
-/

namespace Napplet.NapUpload

inductive Rail where
  | nip96
  | blossom
  | other (name : String)
  deriving DecidableEq, Repr

inductive UploadState where
  | pending | uploading | complete | failed | cancelled
  deriving DecidableEq, Repr

structure UploadEnv where
  defaultRail : Option Rail
  railEnabled : Rail → Bool
  /-- Server the shell configured for a rail. Never napplet input. -/
  server : Rail → Option String
  maxBytes : Nat
  mimeAllowed : String → Bool
  sniff : Bytes → String
  /-- Metadata stripping (e.g. EXIF) or other transformation. -/
  transform : Bytes → Bytes
  sha256 : Bytes → Hash
  /-- NIP-98 / kind 24242 authorisation over a blob hash, signed by the shell. -/
  signAuth : Rail → Hash → String
  /-- Server PUT: `some url` only if the server confirmed storage. -/
  put : String → Rail → Bytes → Option String
  /-- Outcome of the first-upload consent prompt. -/
  userApproves : Bool

structure UploadRequest where
  rail : Option Rail
  data : Bytes
  noTransform : Bool := false
  deriving DecidableEq, Repr

structure UploadResult where
  ok : Bool
  status : UploadState
  rail : Rail
  url : Option String
  sha256 : Option Hash
  originalSha256 : Option Hash
  error : Option String
  deriving DecidableEq, Repr

inductive UploadOut where
  /-- Bytes leave the shell. -/
  | send (server : String) (rail : Rail) (auth : String) (bytes : Bytes)
  | result (to : Endpoint) (id : String) (r : UploadResult)
  /-- No upload was created. -/
  | topError (to : Endpoint) (id : String) (error : String)
  deriving DecidableEq, Repr

def chooseRail (env : UploadEnv) (req : UploadRequest) : Except String Rail :=
  match req.rail with
  | some r => if env.railEnabled r then .ok r else .error "unsupported rail"
  | none =>
    match env.defaultRail with
    | some r => if env.railEnabled r then .ok r else .error "no server configured"
    | none => .error "no server configured"

/-- Handle `upload.upload`. Returns the new consent flag for this napplet. -/
def upload (env : UploadEnv) (consented : Bool) (to : Endpoint) (id : String)
    (req : UploadRequest) : Bool × List UploadOut :=
  match chooseRail env req with
  | .error e => (consented, [.topError to id e])
  | .ok rail =>
    match env.server rail with
    | none => (consented, [.topError to id "no server configured"])
    | some srv =>
      if req.data.length > env.maxBytes then (consented, [.topError to id "file too large"])
      else if env.mimeAllowed (env.sniff req.data) = false then
        (consented, [.topError to id "unsupported media type"])
      else if consented = false && env.userApproves = false then
        (consented, [.topError to id "user cancelled"])
      else
        let stored := if req.noTransform then req.data else env.transform req.data
        let h := env.sha256 stored
        let orig := if stored = req.data then none else some (env.sha256 req.data)
        let auth := env.signAuth rail h
        match env.put srv rail stored with
        | some url =>
          (true, [.send srv rail auth stored,
                  .result to id ⟨true, .complete, rail, some url, some h, orig, none⟩])
        | none =>
          (true, [.send srv rail auth stored,
                  .result to id ⟨false, .failed, rail, none, none, none, some "upload failed"⟩])

/-- Everything a successful path through the policy gates guarantees. -/
theorem upload_passed {env : UploadEnv} {c : Bool} {to : Endpoint} {id : String}
    {req : UploadRequest} {o : UploadOut} (h : o ∈ (upload env c to id req).2)
    (hn : ∀ i e, o ≠ .topError to i e) :
    ∃ rail srv, chooseRail env req = .ok rail ∧ env.server rail = some srv ∧
      req.data.length ≤ env.maxBytes ∧ env.mimeAllowed (env.sniff req.data) = true ∧
      (c = true ∨ env.userApproves = true) ∧
      (let stored := if req.noTransform then req.data else env.transform req.data
       o = .send srv rail (env.signAuth rail (env.sha256 stored)) stored ∨
       (∃ url, env.put srv rail stored = some url ∧
         o = .result to id ⟨true, .complete, rail, some url, some (env.sha256 stored),
           (if stored = req.data then none else some (env.sha256 req.data)), none⟩) ∨
       (env.put srv rail stored = none ∧
         o = .result to id ⟨false, .failed, rail, none, none, none, some "upload failed"⟩)) := by
  unfold upload at h
  split at h
  · simp at h; exact absurd h (hn _ _)
  · rename_i rail hr
    split at h
    · simp at h; exact absurd h (hn _ _)
    · rename_i srv hs
      split at h
      · simp at h; exact absurd h (hn _ _)
      · rename_i hsz
        split at h
        · simp at h; exact absurd h (hn _ _)
        · rename_i hm
          split at h
          · simp at h; exact absurd h (hn _ _)
          · rename_i hc
            refine ⟨rail, srv, hr, hs, by omega, by simpa using hm, ?_, ?_⟩
            · simp only [Bool.and_eq_true, not_and, Bool.not_eq_true] at hc
              cases c with
              | true => exact .inl rfl
              | false => exact .inr (by simpa using hc rfl)
            · dsimp only at h ⊢
              split at h
              · rename_i url hp
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with h | h
                · exact .inl h
                · exact .inr (.inl ⟨url, hp, h⟩)
              · rename_i hp
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                rcases h with h | h
                · exact .inl h
                · exact .inr (.inr ⟨hp, h⟩)

/-- Bytes leave the shell only after every policy gate and consent, to the
shell-configured server for the chosen rail, with a shell-signed authorisation. -/
theorem send_requires_policy {env : UploadEnv} {c : Bool} {to : Endpoint} {id : String}
    {req : UploadRequest} {srv : String} {rail : Rail} {auth : String} {b : Bytes}
    (h : UploadOut.send srv rail auth b ∈ (upload env c to id req).2) :
    chooseRail env req = .ok rail ∧ env.server rail = some srv ∧
    req.data.length ≤ env.maxBytes ∧ env.mimeAllowed (env.sniff req.data) = true ∧
    (c = true ∨ env.userApproves = true) ∧ auth = env.signAuth rail (env.sha256 b) := by
  obtain ⟨rail', srv', hr, hs, hsz, hm, hc, ho⟩ := upload_passed h (by intro i e; simp)
  dsimp only at ho
  rcases ho with ho | ⟨_, _, ho⟩ | ⟨_, ho⟩
  · simp only [UploadOut.send.injEq] at ho
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ho
    exact ⟨hr, hs, hsz, hm, hc, rfl⟩
  · simp at ho
  · simp at ho

theorem send_auth_by_shell {env : UploadEnv} {c : Bool} {to : Endpoint} {id : String}
    {req : UploadRequest} {srv : String} {rail : Rail} {auth : String} {b : Bytes}
    (h : UploadOut.send srv rail auth b ∈ (upload env c to id req).2) :
    auth = env.signAuth rail (env.sha256 b) :=
  (send_requires_policy h).2.2.2.2.2

/-- `complete` with a URL is reported only when the server confirmed storage, and
its hashes describe the bytes actually stored. -/
theorem complete_requires_confirmation {env : UploadEnv} {c : Bool} {to : Endpoint}
    {id : String} {req : UploadRequest} {r : UploadResult}
    (h : UploadOut.result to id r ∈ (upload env c to id req).2) (hc : r.status = .complete) :
    ∃ srv url, env.server r.rail = some srv ∧ r.url = some url ∧
      let stored := if req.noTransform then req.data else env.transform req.data
      env.put srv r.rail stored = some url ∧ r.sha256 = some (env.sha256 stored) ∧
      r.originalSha256 = (if stored = req.data then none else some (env.sha256 req.data)) := by
  obtain ⟨rail, srv, hr, hs, -, -, -, ho⟩ := upload_passed h (by intro i e; simp)
  dsimp only at ho ⊢
  rcases ho with ho | ⟨url, hp, ho⟩ | ⟨_, ho⟩
  · simp at ho
  · simp only [UploadOut.result.injEq, true_and] at ho
    subst ho
    exact ⟨srv, url, hs, rfl, hp, rfl, rfl⟩
  · simp only [UploadOut.result.injEq, true_and] at ho
    subst ho
    simp at hc

/-- `originalSha256` appears exactly when the shell changed the bytes. -/
theorem complete_hashes {env : UploadEnv} {c : Bool} {to : Endpoint} {id : String}
    {req : UploadRequest} {r : UploadResult}
    (h : UploadOut.result to id r ∈ (upload env c to id req).2) (hc : r.status = .complete) :
    let stored := if req.noTransform then req.data else env.transform req.data
    r.sha256 = some (env.sha256 stored) ∧ (r.originalSha256.isSome ↔ stored ≠ req.data) := by
  obtain ⟨srv, url, -, -, -, h1, h2⟩ := complete_requires_confirmation h hc
  dsimp only at h1 h2 ⊢
  refine ⟨h1, ?_⟩
  rw [h2]
  split <;> simp_all

/-- Consent, once recorded, stays recorded; and it is only recorded when the user
approved or had already consented. -/
theorem consent_latch (env : UploadEnv) (c : Bool) (to : Endpoint) (id : String)
    (req : UploadRequest) :
    (c = true → (upload env c to id req).1 = true) ∧
    ((upload env c to id req).1 = true → c = true ∨ env.userApproves = true) := by
  unfold upload
  constructor
  · intro hc; subst hc
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · dsimp only; split <;> rfl
  · intro h1
    split at h1
    · exact .inl h1
    · split at h1
      · exact .inl h1
      · split at h1
        · exact .inl h1
        · split at h1
          · exact .inl h1
          · split at h1
            · exact .inl h1
            · rename_i hc
              simp only [Bool.and_eq_true, not_and, Bool.not_eq_true] at hc
              cases c with
              | true => exact .inl rfl
              | false => exact .inr (by simpa using hc rfl)

theorem unsupported_rail_no_send {env : UploadEnv} {c : Bool} {to : Endpoint} {id : String}
    {req : UploadRequest} {r : Rail} (hr : req.rail = some r) (he : env.railEnabled r = false) :
    upload env c to id req = (c, [.topError to id "unsupported rail"]) := by
  simp [upload, chooseRail, hr, he]

/-- A rejected request produces exactly one top-level error and no network output. -/
theorem rejected_no_send {env : UploadEnv} {c : Bool} {to : Endpoint} {id : String}
    {req : UploadRequest} (hlarge : req.data.length > env.maxBytes) :
    ∀ srv rail auth b, UploadOut.send srv rail auth b ∉ (upload env c to id req).2 := by
  intro srv rail auth b h
  have := (send_requires_policy h).2.2.1
  omega

theorem upload_same_id {env : UploadEnv} {c : Bool} {to : Endpoint} {id : String}
    {req : UploadRequest} :
    ∃ o ∈ (upload env c to id req).2, (∃ r, o = .result to id r) ∨ (∃ e, o = .topError to id e) := by
  unfold upload
  split
  · exact ⟨_, List.mem_singleton_self _, .inr ⟨_, rfl⟩⟩
  · split
    · exact ⟨_, List.mem_singleton_self _, .inr ⟨_, rfl⟩⟩
    · split
      · exact ⟨_, List.mem_singleton_self _, .inr ⟨_, rfl⟩⟩
      · split
        · exact ⟨_, List.mem_singleton_self _, .inr ⟨_, rfl⟩⟩
        · split
          · exact ⟨_, List.mem_singleton_self _, .inr ⟨_, rfl⟩⟩
          · dsimp only
            split
            · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), .inl ⟨_, rfl⟩⟩
            · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), .inl ⟨_, rfl⟩⟩

end Napplet.NapUpload
