import Napplet.Basic

/-!
# NAP-RESOURCE (`resource`, PR napplet/naps#80 branch `nub-resource`)

Sandboxed fetching through the runtime. The network, hashing, MIME sniffing and SVG
rasterisation are opaque functions in `Env`; the policy around them is modelled.

Results:
* `bytes_no_private_hop`: no delivered resource came through a private, loopback,
  link-local, ULA or metadata address on any hop.
* `bytes_size_capped`, `bytes_redirects_capped`.
* `bytes_mime_sniffed_not_svg`: MIME is runtime-sniffed from the delivered bytes,
  never upstream `Content-Type`, and raw SVG is never delivered.
* `blossom_hash_verified`: a delivered `blossom:` blob matched its hash.
* `http_disabled_by_default`, `unknown_scheme_unsupported`.
* `bytesMany_items`: per-URL results in input order, each independent of siblings.
* `cancel_drops_late`, `at_most_one_terminal`: one terminal envelope per request,
  none after cancellation.
* IP classification vectors.
-/

namespace Napplet.NapResource

/-! ## Address classification -/

/-- An address: 4 octets (IPv4) or 16 octets (IPv6). -/
inductive Ip where
  | v4 (a b c d : Nat)
  | v6 (bytes : List Nat)
  deriving DecidableEq, Repr

def v4Private (a b c _d : Nat) : Bool :=
  a == 10 || a == 127 || a == 0 ||
  (a == 172 && 16 ≤ b && b ≤ 31) ||
  (a == 192 && b == 168) ||
  (a == 169 && b == 254) ||
  (a == 100 && 64 ≤ b && b ≤ 127) ||
  (a == 255 && b == 255 && c == 255)

/-- RFC1918, loopback, link-local (incl. 169.254.169.254), ULA, CGNAT, unspecified,
and IPv4-mapped IPv6. -/
def isPrivate : Ip → Bool
  | .v4 a b c d => v4Private a b c d
  | .v6 bs =>
    match bs with
    | [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,x] => x == 0 || x == 1
    | [0,0,0,0, 0,0,0,0, 0,0,255,255, a,b,c,d] => v4Private a b c d
    | b0 :: b1 :: _ =>
      (b0 / 2 == 0xfc / 2) ||              -- fc00::/7
      (b0 == 0xfe && b1 / 64 == 0x80 / 64)  -- fe80::/10
    | _ => true

example : isPrivate (.v4 169 254 169 254) = true := by decide
example : isPrivate (.v4 10 1 2 3) = true := by decide
example : isPrivate (.v4 172 20 0 1) = true := by decide
example : isPrivate (.v4 172 32 0 1) = false := by decide
example : isPrivate (.v4 192 168 1 1) = true := by decide
example : isPrivate (.v4 127 0 0 1) = true := by decide
example : isPrivate (.v4 93 184 216 34) = false := by decide
example : isPrivate (.v6 [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]) = true := by decide
example : isPrivate (.v6 [0,0,0,0,0,0,0,0,0,0,255,255,192,168,0,1]) = true := by decide
example : isPrivate (.v6 [0xfd,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]) = true := by decide
example : isPrivate (.v6 [0xfe,0x80,0,0,0,0,0,0,0,0,0,0,0,0,0,1]) = true := by decide
example : isPrivate (.v6 [0x26,0x06,0x47,0,0,0,0,0,0,0,0,0,0,0,0,1]) = false := by decide

/-! ## Fetch policy -/

inductive Scheme where
  | https | http | data | blossom | hashtree | htree | nostr
  deriving DecidableEq, Repr

def schemeOf (url : String) : Option Scheme :=
  if url.startsWith "https:" then some .https
  else if url.startsWith "http:" then some .http
  else if url.startsWith "data:" then some .data
  else if url.startsWith "blossom:" then some .blossom
  else if url.startsWith "hashtree:" then some .hashtree
  else if url.startsWith "htree:" then some .htree
  else if url.startsWith "nostr:" then some .nostr
  else none

inductive ResErr where
  | invalidRequest | notFound | blockedByPolicy | timeout | tooLarge
  | unsupportedScheme | decodeFailed | networkError | quotaExceeded
  deriving DecidableEq, Repr

/-- What the runtime observed while resolving one URL. -/
structure FetchOutcome where
  /-- Address connected to on each hop (first request, then each redirect). -/
  hops : List Ip
  /-- Response body, or `none` for not found. -/
  body : Option Bytes
  timedOut : Bool
  /-- Upstream `Content-Type`. Never used. -/
  upstreamType : String

structure Env where
  fetch : String → FetchOutcome
  sha256 : Bytes → Hash
  sniff : Bytes → String
  /-- Rasterise SVG in an isolated, network-less context. -/
  rasterize : Bytes → Option Bytes

structure Policy where
  maxBytes : Nat := 10 * 1024 * 1024
  maxRedirects : Nat := 5
  maxUrls : Nat := 100
  httpEnabled : Bool := false
  disabled : List Scheme := []

structure Delivered where
  blob : Bytes
  mime : String
  deriving DecidableEq, Repr

def svgMime : String := "image/svg+xml"

/-- Classify by sniffing; rasterise SVG; never deliver raw SVG. -/
def finish (env : Env) (body : Bytes) : Except ResErr Delivered :=
  if env.sniff body = svgMime then
    match env.rasterize body with
    | some r => if env.sniff r = svgMime then .error .decodeFailed else .ok ⟨r, env.sniff r⟩
    | none => .error .decodeFailed
  else .ok ⟨body, env.sniff body⟩

/-- Network checks applied to every scheme the runtime resolves. -/
def fetchChecked (env : Env) (pol : Policy) (url : String) : Except ResErr Bytes :=
  let o := env.fetch url
  if o.timedOut then .error .timeout
  else if o.hops.length > pol.maxRedirects + 1 then .error .blockedByPolicy
  else if o.hops.any isPrivate then .error .blockedByPolicy
  else match o.body with
    | none => .error .notFound
    | some b => if b.length > pol.maxBytes then .error .tooLarge else .ok b

/-- `blossom:<sha256>.<ext>` → the hash. -/
def blossomHash? (url : String) : Option Hash :=
  let cs := url.toList.drop 8
  let h := cs.take 64
  if h.length = 64 && (cs.drop 64).head? == some '.' then some (String.ofList h) else none

#guard blossomHash? ("blossom:" ++ String.ofList (List.replicate 64 'a') ++ ".png") ==
  some (String.ofList (List.replicate 64 'a'))
#guard blossomHash? "blossom:abc.png" == none
#guard schemeOf "https://example.com/a.png" == some .https
#guard schemeOf "ftp://example.com" == none

def schemeAllowed (pol : Policy) (s : Scheme) : Bool :=
  !(decide (s ∈ pol.disabled)) && (s != .http || pol.httpEnabled)

/-- `resource.bytes(url)`. -/
def bytes (env : Env) (pol : Policy) (url : String) : Except ResErr Delivered :=
  match schemeOf url with
  | none => .error .unsupportedScheme
  | some s =>
    if schemeAllowed pol s = false then .error .unsupportedScheme
    else if s = .blossom then
      match blossomHash? url with
      | none => .error .invalidRequest
      | some h =>
        match fetchChecked env pol url with
        | .error e => .error e
        | .ok b => if env.sha256 b ≠ h then .error .decodeFailed else finish env b
    else
      match fetchChecked env pol url with
      | .error e => .error e
      | .ok b => finish env b

/-! ### Single-URL guarantees -/

theorem fetchChecked_ok {env : Env} {pol : Policy} {url : String} {b : Bytes}
    (h : fetchChecked env pol url = .ok b) :
    (∀ ip ∈ (env.fetch url).hops, isPrivate ip = false) ∧
    (env.fetch url).hops.length ≤ pol.maxRedirects + 1 ∧
    (env.fetch url).body = some b ∧ b.length ≤ pol.maxBytes := by
  unfold fetchChecked at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i hr
      split at h
      · simp at h
      · rename_i hp
        split at h
        · simp at h
        · rename_i b' hb
          split at h
          · simp at h
          · rename_i hs
            simp only [Except.ok.injEq] at h
            subst h
            simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hp
            exact ⟨hp, by omega, hb, by omega⟩

theorem finish_ok {env : Env} {body : Bytes} {d : Delivered} (h : finish env body = .ok d) :
    d.mime ≠ svgMime ∧ d.mime = env.sniff d.blob := by
  unfold finish at h
  split at h
  · split at h
    · split at h
      · simp at h
      · rename_i hr
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨hr, rfl⟩
    · simp at h
  · rename_i hs
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨hs, rfl⟩

/-- The common core of every successful `bytes`. -/
theorem bytes_ok {env : Env} {pol : Policy} {url : String} {d : Delivered}
    (h : bytes env pol url = .ok d) :
    ∃ s b, schemeOf url = some s ∧ schemeAllowed pol s = true ∧
      fetchChecked env pol url = .ok b ∧ finish env b = .ok d ∧
      (s = .blossom → ∃ hh, blossomHash? url = some hh ∧ env.sha256 b = hh) := by
  unfold bytes at h
  split at h
  · simp at h
  · rename_i s hs
    split at h
    · simp at h
    · rename_i ha
      split at h
      · rename_i hbl
        split at h
        · simp at h
        · rename_i hh hhash
          split at h
          · simp at h
          · rename_i b hb
            split at h
            · simp at h
            · rename_i heq
              refine ⟨s, b, hs, by simpa using ha, hb, h, fun _ => ⟨hh, hhash, ?_⟩⟩
              simpa using heq
      · rename_i hbl
        split at h
        · simp at h
        · rename_i b hb
          exact ⟨s, b, hs, by simpa using ha, hb, h, fun hs' => absurd hs' hbl⟩

/-- SSRF: nothing is delivered through a private address on any hop. -/
theorem bytes_no_private_hop {env : Env} {pol : Policy} {url : String} {d : Delivered}
    (h : bytes env pol url = .ok d) : ∀ ip ∈ (env.fetch url).hops, isPrivate ip = false := by
  obtain ⟨_, _, _, _, hf, _, _⟩ := bytes_ok h
  exact (fetchChecked_ok hf).1

theorem bytes_redirects_capped {env : Env} {pol : Policy} {url : String} {d : Delivered}
    (h : bytes env pol url = .ok d) : (env.fetch url).hops.length ≤ pol.maxRedirects + 1 := by
  obtain ⟨_, _, _, _, hf, _, _⟩ := bytes_ok h
  exact (fetchChecked_ok hf).2.1

theorem bytes_size_capped {env : Env} {pol : Policy} {url : String} {d : Delivered}
    (h : bytes env pol url = .ok d) :
    ∃ b, (env.fetch url).body = some b ∧ b.length ≤ pol.maxBytes := by
  obtain ⟨_, b, _, _, hf, _, _⟩ := bytes_ok h
  exact ⟨b, (fetchChecked_ok hf).2.2⟩

/-- MIME comes from sniffing the delivered bytes, and raw SVG is never delivered. -/
theorem bytes_mime_sniffed_not_svg {env : Env} {pol : Policy} {url : String} {d : Delivered}
    (h : bytes env pol url = .ok d) : d.mime ≠ svgMime ∧ d.mime = env.sniff d.blob := by
  obtain ⟨_, _, _, _, _, hfin, _⟩ := bytes_ok h
  exact finish_ok hfin

/-- A delivered `blossom:` blob matched its content hash. -/
theorem blossom_hash_verified {env : Env} {pol : Policy} {url : String} {d : Delivered}
    (hs : schemeOf url = some .blossom) (h : bytes env pol url = .ok d) :
    ∃ hh b, blossomHash? url = some hh ∧ (env.fetch url).body = some b ∧ env.sha256 b = hh := by
  obtain ⟨s, b, hs', _, hf, _, hbl⟩ := bytes_ok h
  rw [hs] at hs'
  obtain ⟨hh, h1, h2⟩ := hbl (Option.some.inj hs').symm
  exact ⟨hh, b, h1, (fetchChecked_ok hf).2.2.1, h2⟩

/-- `http:` is not canonical and is off unless policy enables it. -/
theorem http_disabled_by_default {env : Env} {url : String} (hs : schemeOf url = some .http) :
    bytes env {} url = .error .unsupportedScheme := by
  simp [bytes, hs, schemeAllowed]

theorem unknown_scheme_unsupported {env : Env} {pol : Policy} {url : String}
    (hs : schemeOf url = none) : bytes env pol url = .error .unsupportedScheme := by
  simp [bytes, hs]

/-! ### Bulk requests -/

/-- `resource.bytesMany(urls)`. -/
def bytesMany (env : Env) (pol : Policy) (urls : List String) :
    Except ResErr (List (String × Except ResErr Delivered)) :=
  if urls = [] then .error .invalidRequest
  else if urls.length > pol.maxUrls then .error .tooLarge
  else .ok (urls.map fun u => (u, bytes env pol u))

/-- Items preserve input order and length, and each URL is processed exactly as an
independent `bytes(url)`: one failure cannot affect its siblings. -/
theorem bytesMany_items {env : Env} {pol : Policy} {urls : List String}
    {items : List (String × Except ResErr Delivered)} (h : bytesMany env pol urls = .ok items) :
    items = urls.map (fun u => (u, bytes env pol u)) := by
  unfold bytesMany at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simpa using h.symm

theorem bytesMany_length {env : Env} {pol : Policy} {urls : List String}
    {items : List (String × Except ResErr Delivered)} (h : bytesMany env pol urls = .ok items) :
    items.length = urls.length := by
  simp [bytesMany_items h]

theorem bytesMany_empty (env : Env) (pol : Policy) :
    bytesMany env pol [] = .error .invalidRequest := by
  simp [bytesMany]

/-! ### Terminal envelopes and cancellation -/

inductive ReqEvent where
  | request (id : String)
  | cancel (id : String)
  /-- The fetch for `id` finished (successfully or not). -/
  | complete (id : String)
  deriving DecidableEq, Repr

/-- One step over the set of pending request ids. Returns the id of the terminal
envelope to send, if any. Duplicate in-flight ids are ignored. -/
def track (pending : List String) : ReqEvent → List String × Option String
  | .request id => if id ∈ pending then (pending, none) else (id :: pending, none)
  | .cancel id => (pending.filter (· != id), none)
  | .complete id =>
    if id ∈ pending then (pending.filter (· != id), some id) else (pending, none)

/-- Late terminal envelopes for cancelled ids are dropped. -/
theorem cancel_drops_late (pending : List String) (id : String) :
    (track (track pending (.cancel id)).1 (.complete id)).2 = none := by
  simp [track]

/-- Run a trace, collecting terminal envelopes. -/
def runTrace : List String → List ReqEvent → List String
  | _, [] => []
  | p, e :: es =>
    let r := track p e
    r.2.toList ++ runTrace r.1 es

theorem terminal_requires_pending {p : List String} {e : ReqEvent} {id : String}
    (h : (track p e).2 = some id) : id ∈ p ∧ id ∉ (track p e).1 := by
  cases e with
  | request i => simp only [track] at h; split at h <;> simp at h
  | cancel i => simp [track] at h
  | complete i =>
    simp only [track] at h
    split at h
    · simp at h; subst h; simp_all [track]
    · simp at h

/-- Between two `request`s for the same id, at most one terminal envelope is sent:
once a terminal goes out, the id is no longer pending, and only a new `request`
makes it pending again. -/
theorem no_terminal_without_request (p : List String) (id : String) (es : List ReqEvent)
    (hp : id ∉ p) (hr : ∀ e ∈ es, e ≠ .request id) : id ∉ runTrace p es := by
  induction es generalizing p with
  | nil => simp [runTrace]
  | cons e es ih =>
    simp only [runTrace, List.mem_append, Option.mem_toList, not_or]
    have hpe : id ∉ (track p e).1 := by
      cases e with
      | request i =>
        have : id ≠ i := by intro h; subst h; exact hr _ (by simp) rfl
        simp only [track]
        split <;> simp_all
      | cancel i => simp [track, hp]
      | complete i =>
        simp only [track]
        split <;> simp_all
    refine ⟨?_, ih _ hpe (fun e' he' => hr e' (by simp [he']))⟩
    intro h
    exact hp (terminal_requires_pending h).1

/-- A request followed by its completion yields exactly one terminal envelope for that
id, however many further completions or cancellations arrive. -/
theorem at_most_one_terminal (p : List String) (id : String) (es : List ReqEvent)
    (hp : id ∉ p) (hr : ∀ e ∈ es, e ≠ .request id) :
    (runTrace p (.request id :: .complete id :: es)).count id = 1 := by
  have hn : id ∉ runTrace (p.filter (· != id)) es :=
    no_terminal_without_request _ id es (by simp) hr
  have h0 : (runTrace (p.filter (· != id)) es).count id = 0 := List.count_eq_zero.2 hn
  simp [runTrace, track, hp, h0]

end Napplet.NapResource
