import Napplet.Basic

/-!
# NAP-INTENT (`intent`) and convention URI binding

* `resolve` is the normative handler-resolution precedence:
  explicit authorised selection / `choose` → user default → usable recommendation →
  normal resolution. Proved: an explicit selection never falls back to the
  recommendation, a user default always beats a recommendation, an unusable
  recommendation falls back to step 4.
* `invoke` produces the result and at most one delivery, to the resolved handler,
  stamped with the authenticated sender.
* `bindUri` is the web-projection convention URI binding. Proved: the bound identity is
  queryless and fragment-free, parameter names are unique, fragments are rejected
  outside `intent.invoke`, and a query cannot be combined with an explicit payload.
-/

namespace Napplet.NapIntent

abbrev HandlerId := String

/-! ## Handler resolution -/

inductive Selection where
  /-- Explicit handler catalog identifier. -/
  | explicit (h : HandlerId)
  /-- `handler: "choose"`: ask the user. -/
  | choose
  /-- Absent `handler`, or `"default"`. -/
  | auto
  deriving DecidableEq, Repr

structure ResolveCtx where
  /-- Whether the user authorised addressing this handler explicitly. -/
  authorized : HandlerId → Bool
  /-- Outcome of the `choose` UI. -/
  userChoice : Option HandlerId
  /-- The user's applicable default handler. -/
  userDefault : Option HandlerId
  /-- Handler recommended by a `#<naddr>` hint. -/
  recommendation : Option HandlerId
  /-- Policy permits it and it supports archetype, action and convention. -/
  recommendationUsable : HandlerId → Bool
  /-- Normal installed-handler resolution or user choice. -/
  fallback : Option HandlerId

def resolve (ctx : ResolveCtx) : Selection → Option HandlerId
  | .explicit h => if ctx.authorized h then some h else none
  | .choose => ctx.userChoice
  | .auto =>
    match ctx.userDefault with
    | some d => some d
    | none =>
      match ctx.recommendation with
      | some r => if ctx.recommendationUsable r then some r else ctx.fallback
      | none => ctx.fallback

/-- An explicit selection resolves to itself or fails; it never silently falls back. -/
theorem explicit_no_fallback (ctx : ResolveCtx) (h r : HandlerId)
    (hr : resolve ctx (.explicit h) = some r) : r = h := by
  simp only [resolve] at hr
  split at hr <;> simp_all

/-- The user's default beats any recommendation. -/
theorem default_wins (ctx : ResolveCtx) (d : HandlerId) (hd : ctx.userDefault = some d) :
    resolve ctx .auto = some d := by
  simp [resolve, hd]

/-- An unavailable, unsupported, declined or denied recommendation falls back to step 4. -/
theorem unusable_recommendation_falls_back (ctx : ResolveCtx) (r : HandlerId)
    (hd : ctx.userDefault = none) (hr : ctx.recommendation = some r)
    (hu : ctx.recommendationUsable r = false) : resolve ctx .auto = ctx.fallback := by
  simp [resolve, hd, hr, hu]

/-! ## Invocation and delivery -/

structure IntentRequest where
  archetype : String
  action : String
  convention : String
  payload : List (String × String)
  handler : Selection
  deriving DecidableEq, Repr

inductive IntentOut where
  | result (to : Endpoint) (id : String) (ok : Bool) (handler : Option HandlerId)
      (error : Option String)
  | deliver (target : HandlerId) (sender : Endpoint) (convention : String)
      (payload : List (String × String))
  deriving DecidableEq, Repr

/-- The convention must be exactly `napplet:<archetype>/<action>`. -/
def conventionOk (r : IntentRequest) : Bool :=
  r.convention == "napplet:" ++ r.archetype ++ "/" ++ r.action

/-- `intent.invoke` from authenticated endpoint `sender`. `ok = true` means the runtime
accepted delivery responsibility. -/
def invoke (ctx : ResolveCtx) (sender : Endpoint) (id : String) (r : IntentRequest) :
    List IntentOut :=
  if conventionOk r = false then [.result sender id false none (some "invalid convention")]
  else
    match resolve ctx r.handler with
    | none => [.result sender id false none (some "no handler")]
    | some h => [.result sender id true (some h) none, .deliver h sender r.convention r.payload]

theorem invoke_result_first (ctx : ResolveCtx) (sender : Endpoint) (id : String)
    (r : IntentRequest) :
    ∃ ok h e rest, invoke ctx sender id r = .result sender id ok h e :: rest := by
  unfold invoke
  split
  · exact ⟨_, _, _, _, rfl⟩
  · split <;> exact ⟨_, _, _, _, rfl⟩

/-- Every delivery goes to the resolved handler, carries the authenticated sender and
the validated convention, and only happens when the result is `ok`. -/
theorem invoke_delivery {ctx : ResolveCtx} {sender : Endpoint} {id : String}
    {r : IntentRequest} {t : HandlerId} {snd : Endpoint} {conv : String}
    {pl : List (String × String)} (h : IntentOut.deliver t snd conv pl ∈ invoke ctx sender id r) :
    resolve ctx r.handler = some t ∧ snd = sender ∧ conv = r.convention ∧
    conventionOk r = true ∧ pl = r.payload := by
  unfold invoke at h
  split at h
  · simp at h
  · rename_i hc
    split at h
    · simp at h
    · rename_i hh hres
      simp at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp_all

/-- At most one delivery per invocation, so the payload reaches only the target. -/
theorem invoke_single_delivery (ctx : ResolveCtx) (sender : Endpoint) (id : String)
    (r : IntentRequest) :
    ((invoke ctx sender id r).filter fun o => match o with
      | .deliver .. => true | _ => false).length ≤ 1 := by
  unfold invoke
  split
  · simp
  · split <;> simp

/-! ## Convention URI binding (web projection) -/

/-- Split at the first occurrence of `c`. -/
def splitFirst (c : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | x :: xs => if x = c then ([], some xs) else ((splitFirst c xs).1.cons x, (splitFirst c xs).2)

theorem splitFirst_fst_sub {c : Char} {l : List Char} {x : Char}
    (h : x ∈ (splitFirst c l).1) : x ∈ l := by
  induction l with
  | nil => simp [splitFirst] at h
  | cons y ys ih =>
    simp only [splitFirst] at h
    split at h
    · simp at h
    · simp at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

/-- Split on every occurrence of `c`. -/
def splitAll (c : Char) (l : List Char) : List (List Char) :=
  match h : splitFirst c l with
  | (a, none) => [a]
  | (a, some rest) =>
    have : rest.length < l.length := by
      induction l generalizing a rest with
      | nil => simp [splitFirst] at h
      | cons y ys ih =>
        simp only [splitFirst] at h
        split at h
        · simp at h; obtain ⟨-, rfl⟩ := h; simp
        · simp at h
          obtain ⟨-, h2⟩ := h
          have := ih (splitFirst c ys).1 rest (Prod.ext rfl h2)
          simp; omega
    a :: splitAll c rest
termination_by l.length

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Percent-decode to bytes. `+` stays literal; a bad escape fails. -/
def pctBytes : List Char → Option (List UInt8)
  | [] => some []
  | '%' :: h1 :: h2 :: rest =>
    match hexVal h1, hexVal h2 with
    | some a, some b => (pctBytes rest).map ((a * 16 + b).toUInt8 :: ·)
    | _, _ => none
  | '%' :: _ => none
  | c :: rest => (pctBytes rest).map ((String.singleton c).toUTF8.toList ++ ·)

/-- Percent-decode as UTF-8 text, with no type coercion. -/
def pctDecode (l : List Char) : Option String :=
  (pctBytes l).bind fun bs => String.fromUTF8? ⟨bs.toArray⟩

/-- Parse `name=value&...`. -/
def parseQuery (q : List Char) : Option (List (String × String)) :=
  (splitAll '&' q).mapM fun seg =>
    match splitFirst '=' seg with
    | ([], _) => none
    | (n, v) =>
      match pctDecode n, pctDecode (v.getD []) with
      | some n', some v' => some (n', v')
      | _, _ => none

def nameChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- `napplet:<archetype>/<intent>` with non-empty name segments. -/
def validIdent (l : List Char) : Bool :=
  l.take 8 == "napplet:".toList &&
    match splitFirst '/' (l.drop 8) with
    | (a, some b) => !a.isEmpty && !b.isEmpty && a.all nameChar && b.all nameChar
    | _ => false

theorem validIdent_no_query {l : List Char} (h : validIdent l = true) :
    '?' ∉ l ∧ '#' ∉ l := by
  simp only [validIdent, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨ht, hs⟩ := h
  have key : ∀ c, c ∈ l.drop 8 → nameChar c = true ∨ c = '/' := by
    intro c hc
    split at hs
    · rename_i a b hab
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true] at hs
      obtain ⟨⟨⟨-, -⟩, ha⟩, hb⟩ := hs
      -- every char of drop 8 is in a, is '/', or is in b
      have split_cover : ∀ (m : List Char) (a b : List Char),
          splitFirst '/' m = (a, some b) → ∀ x ∈ m, x ∈ a ∨ x = '/' ∨ x ∈ b := by
        intro m
        induction m with
        | nil => intro a b h; simp [splitFirst] at h
        | cons y ys ih =>
          intro a b h x hx
          simp only [splitFirst] at h
          split at h
          · rename_i hy
            simp at h
            obtain ⟨rfl, rfl⟩ := h
            simp at hx
            rcases hx with rfl | hx
            · exact .inr (.inl hy)
            · exact .inr (.inr hx)
          · simp at h
            obtain ⟨h1, h2⟩ := h
            simp at hx
            rcases hx with rfl | hx
            · exact .inl (by rw [← h1]; simp)
            · rcases ih _ _ (by rw [Prod.mk.injEq]; exact ⟨rfl, h2⟩) x hx with h' | h' | h'
              · exact .inl (by rw [← h1]; simp [h'])
              · exact .inr (.inl h')
              · exact .inr (.inr h')
      rcases split_cover _ a b hab c hc with h' | h' | h'
      · exact .inl (ha c h')
      · exact .inr h'
      · exact .inl (hb c h')
    · simp at hs
  have notIn : ∀ c, nameChar c = false → c ≠ '/' → c ∉ "napplet:".toList → c ∉ l := by
    intro c hn hs' hp hc
    rw [← List.take_append_drop 8 l] at hc
    rcases List.mem_append.mp hc with h1 | h1
    · rw [ht] at h1
      exact hp h1
    · rcases key c h1 with h2 | h2
      · rw [hn] at h2; exact Bool.false_ne_true h2
      · exact hs' h2
  exact ⟨notIn '?' (by decide) (by decide) (by decide), notIn '#' (by decide) (by decide) (by decide)⟩

/-- Which operation the URI is passed to. -/
inductive UriOp where
  | intentInvoke
  | other
  deriving DecidableEq, Repr

inductive BindError where
  | fragmentNotAllowed
  | badConvention
  | queryWithPayload
  | badEncoding
  | repeatedName
  deriving DecidableEq, Repr

structure Bound where
  identity : List Char
  payload : List (String × String)
  handlerHint : Option (List Char)
  deriving Repr

/-- Web-projection convention URI binding. -/
def bindUri (uri : String) (op : UriOp) (explicitPayload : Bool) : Except BindError Bound :=
  let p1 := splitFirst '#' uri.toList
  if p1.2.isSome && op == .other then .error .fragmentNotAllowed else
  let p2 := splitFirst '?' p1.1
  if validIdent p2.1 = false then .error .badConvention else
  if p2.2.isSome && explicitPayload then .error .queryWithPayload else
  match (match p2.2 with | none => some [] | some q => parseQuery q) with
  | none => .error .badEncoding
  | some params =>
    if decide (params.map Prod.fst).Nodup then
      .ok { identity := p2.1, payload := params, handlerHint := p1.2 }
    else .error .repeatedName

theorem bindUri_ok {uri : String} {op : UriOp} {ep : Bool} {b : Bound}
    (h : bindUri uri op ep = .ok b) :
    '?' ∉ b.identity ∧ '#' ∉ b.identity ∧ (b.payload.map Prod.fst).Nodup ∧
    (op = .other → b.handlerHint = none) := by
  unfold bindUri at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hfrag
    split at h
    · simp at h
    · rename_i hv
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i params _
          split at h
          · rename_i hnd
            simp only [Except.ok.injEq] at h
            subst h
            simp only [Bool.not_eq_false] at hv
            obtain ⟨hq, hh⟩ := validIdent_no_query hv
            refine ⟨hq, hh, by simpa using hnd, ?_⟩
            intro hop
            subst hop
            simp only [Bool.and_eq_true, beq_self_eq_true, and_true,
              Option.isSome_iff_ne_none, ne_eq] at hfrag
            simpa using hfrag
          · simp at h

-- Conformance vectors (evaluated).
#guard (bindUri "napplet:profile/open?pubkey=abc123" .other false).toOption.map
  (·.payload) == some [("pubkey", "abc123")]
#guard (bindUri "napplet:profile/open?pubkey=a+b" .other false).toOption.map
  (·.payload) == some [("pubkey", "a+b")]
#guard (bindUri "napplet:profile/open?pubkey=%E2%9C%93" .other false).toOption.map
  (·.payload) == some [("pubkey", "✓")]
#guard (bindUri "napplet:profile/open#naddr1xyz" .other false) matches .error .fragmentNotAllowed
#guard (bindUri "napplet:profile/open?pubkey=abc#naddr1xyz" .intentInvoke false).toOption.map
  (·.handlerHint) == some (some "naddr1xyz".toList)
#guard (bindUri "napplet:profile/open?a=1&a=2" .other false) matches .error .repeatedName
#guard (bindUri "napplet:profile/open?a=%zz" .other false) matches .error .badEncoding
#guard (bindUri "napplet:profile/open?a=1" .other true) matches .error .queryWithPayload
#guard (bindUri "napplet:profile" .other false) matches .error .badConvention
#guard (bindUri "nostr:profile/open" .other false) matches .error .badConvention

end Napplet.NapIntent
