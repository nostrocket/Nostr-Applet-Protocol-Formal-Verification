/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Link

/-!
# NAP-LINK runtime component

Upstream: `napplet/naps` PR #53, `naps/NAP-LINK.md` at `100e5c93`.

Wire (napplet → shell): `link.open {id, url, options?: {label?}}`.
Wire (shell → napplet): `link.open.result {id, status, error?}` with `status`
`"opened"` or `"denied"`; `error` only with `"denied"`, one of `"invalid-url"`,
`"unsupported-scheme"`, `"blocked-by-policy"`, `"user-denied"`.

Decision order for one request, from the endpoint's verified identity `key`:
1. `url` is not an absolute URL (`NapLink.schemeOf`), or an `http`/`https` URL
   without a host: `invalid-url`.
2. The scheme is local or code-bearing (`NapLink.forbidden`, whatever the
   configuration says) or not in `Cfg.allowedSchemes`: `unsupported-scheme`.
3. A persisted deny rule for this napplet matches: `blocked-by-policy`.
4. A persisted allow rule for this napplet matches: open at once.
5. Prompting is off (`Cfg.prompt = false`) or this endpoint already has
   `Cfg.maxPrompts` prompts outstanding (prompt-spam limit): `blocked-by-policy`.
6. Otherwise ask the user (`Call.prompt .link "open"`); answer when the host replies.

The label is display text only: it goes into the prompt and nowhere else.
Rules are persistent user preferences keyed by the napplet's manifest key, not by
port; prompts are per endpoint and are cancelled on teardown.

Malformed requests: no string `id` → nothing (no correlation possible);
`url` missing or not a string → `link.open.result {id, status: "denied",
error: "invalid-url"}`; `options` that is not an object, or a non-string
`label`, is ignored (the label is an untrusted display hint; kehto does the same).

## Host operations

* `Call.prompt .link "open" {url, host?, label?, napplet}` → `Reply.decision allowed choice`.
  Ask the user whether to open `url`. The prompt MUST show the napplet
  (`napplet` is its catalog identifier `Ctx.catalogId`; show its name and author
  when known), the destination `url` and hostname `host` (treat IDN, punycode and
  lookalike hostnames as phishing risks), and MAY show `label`, marked as text
  supplied by the napplet. Choices: `choice` `"once"` (or absent) applies to this
  request only; `"napplet"` persists the answer for every link from this napplet;
  `"host"` (allow only) persists allow for links to this hostname from this
  napplet; `"url"` persists the answer for this exact URL from this napplet.
  Any other reply is treated as a refusal by policy (`blocked-by-policy`).
* `Effect.nap .link "open" {url}`: open `url` for the user outside the napplet
  sandbox (new tab, external browser, in-shell browser or native handler, the
  host's choice) with `noopener` (HTML `rel=noopener` / `window.open(url, "_blank",
  "noopener")`) or an equivalent: the opened context MUST NOT get `window.opener`
  or any other reference back to the napplet. The model only emits it for URLs
  that passed steps 1–2 and either a persisted allow rule or the user's approval.
* `Effect.cancel tag`: withdraw an outstanding prompt (endpoint torn down).
-/

namespace Napplet.Run.Link

open NapLink

/-! ### Configuration and state -/

/-- What a persisted rule matches for one napplet. -/
inductive Target where
  /-- Every link from the napplet. -/
  | napplet
  /-- Links to this hostname (lowercase). -/
  | host (h : String)
  /-- This exact URL. -/
  | url (u : String)
  deriving DecidableEq, Repr

/-- A persisted per-napplet choice (NAP-LINK §Shell Behavior: "MAY persist user
choices per napplet, per hostname, or per URL"). -/
structure Rule where
  napplet : ManifestKey
  target : Target
  allow : Bool
  deriving DecidableEq, Repr

structure Cfg where
  /-- Schemes policy allows; `forbidden` schemes are refused even if listed. -/
  allowedSchemes : List String := ["https", "http"]
  /-- Rules the user configured before this session. -/
  rules : List Rule := []
  /-- Ask the user when no rule matches; `false` refuses by policy. -/
  prompt : Bool := true
  /-- Outstanding prompts per endpoint before further requests are refused. -/
  maxPrompts : Nat := 4

structure Pending where
  n : Nat
  port : PortId
  id : String
  url : String
  napplet : ManifestKey
  deriving DecidableEq, Repr

structure St where
  cfg : Cfg
  /-- Persistent rules (configured plus those the user chose in prompts). -/
  rules : List Rule
  pending : List Pending
  next : Nat

def St.init (cfg : Cfg := {}) : St := ⟨cfg, cfg.rules, [], 0⟩

inductive Req where
  | openUrl (id : String) (url : String) (label : Option String)
  deriving DecidableEq, Repr

def Req.id : Req → String
  | .openUrl id _ _ => id

/-! ### URLs -/

/-- Hostname of `scheme://[userinfo@]host[:port]...`, lowercased; `none` without `//`. -/
def hostOf (url : String) : Option String :=
  let cs := url.toList
  let rest := cs.drop ((cs.takeWhile (· != ':')).length + 1)
  match rest with
  | '/' :: '/' :: auth =>
    let a := auth.takeWhile fun c => c != '/' && c != '?' && c != '#'
    let a := if a.contains '@' then (a.reverse.takeWhile (· != '@')).reverse else a
    let hostPart := match a with
      | '[' :: _ => (a.takeWhile (· != ']')) ++ [']']
      | _ => a.takeWhile (· != ':')
    some (String.ofList (hostPart.map Char.toLower))
  | _ => none

#guard hostOf "https://User@Example.COM:8443/a?b#c" == some "example.com"
#guard hostOf "mailto:a@b.c" == none

/-- Steps 1–2: `none` when the URL may be opened at all, else the error. -/
def schemeCheck (cfg : Cfg) (url : String) : Option String :=
  match schemeOf url with
  | none => some "invalid-url"
  | some sc =>
    if (sc = "http" ∨ sc = "https") ∧ (hostOf url).getD "" = "" then some "invalid-url"
    else if sc ∈ forbidden ∨ sc ∉ cfg.allowedSchemes then some "unsupported-scheme"
    else none

def Rule.matches (r : Rule) (k : ManifestKey) (url : String) : Bool :=
  r.napplet == k &&
  match r.target with
  | .napplet => true
  | .host h => hostOf url == some h
  | .url u => u == url

def ruleDenies (s : St) (k : ManifestKey) (url : String) : Bool :=
  s.rules.any fun r => !r.allow && r.matches k url

def ruleAllows (s : St) (k : ManifestKey) (url : String) : Bool :=
  s.rules.any fun r => r.allow && r.matches k url

inductive Verdict where
  | deny (error : String)
  | allow
  | ask
  deriving DecidableEq, Repr

def verdict (s : St) (k : ManifestKey) (url : String) : Verdict :=
  match schemeCheck s.cfg url with
  | some e => .deny e
  | none =>
    if ruleDenies s k url then .deny "blocked-by-policy"
    else if ruleAllows s k url then .allow
    else if !s.cfg.prompt then .deny "blocked-by-policy"
    else .ask

/-! ### Codec -/

def labelOf (j : Json) : Option String :=
  match j.get? "options" with
  | some o => o.getStr? "label"
  | none => none

def resultJson (id : String) (opened : Bool) (error : Option String) : Json :=
  Json.msg "link.open.result"
    [("id", some (.str id)), ("status", some (.str (if opened then "opened" else "denied"))),
     ("error", error.map .str)]

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some "link.open" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match j.getStr? "url" with
      | none => .reject [resultJson id false (some "invalid-url")]
      | some u => .ok (.openUrl id u (labelOf j))
  | _ => .unknown

def encodeReq : Req → Json
  | .openUrl id u l =>
    Json.msg "link.open" [("id", some (.str id)), ("url", some (.str u)),
      ("options", l.map fun l => .obj [("label", .str l)])]

def openArgs (url : String) : Json := .obj [("url", .str url)]

def openEff (url : String) : Eff := .effect (.nap .link "open" (openArgs url))

def promptDetails (cx : Ctx) (url : String) (label : Option String) : Json :=
  Json.mkObj [("url", some (.str url)), ("host", (hostOf url).map .str),
    ("label", label.map .str), ("napplet", some (.str cx.catalogId))]

/-! ### Component -/

def handle (_h : Host) (_w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .openUrl id url label =>
    let k := cx.identity.key
    match verdict s k url with
    | .deny e => (s, [.send cx.port (resultJson id false (some e))])
    | .allow => (s, [openEff url, .send cx.port (resultJson id true none)])
    | .ask =>
      if (s.pending.filter (·.port == cx.port)).length ≥ s.cfg.maxPrompts then
        (s, [.send cx.port (resultJson id false (some "blocked-by-policy"))])
      else
        ({ s with pending := ⟨s.next, cx.port, id, url, k⟩ :: s.pending, next := s.next + 1 },
         [.call ⟨.link, s.next⟩ (.prompt .link "open" (promptDetails cx url label))])

/-- The rule a prompt answer persists, if any. -/
def ruleOf (p : Pending) (allowed : Bool) : Option String → Option Rule
  | some "napplet" => some ⟨p.napplet, .napplet, allowed⟩
  | some "url" => some ⟨p.napplet, .url p.url, allowed⟩
  | some "host" => if allowed then (hostOf p.url).map fun h => ⟨p.napplet, .host h, true⟩ else none
  | _ => none

/-- The outcome of a prompt answer. The scheme is checked again before opening. -/
def answer (s : St) (p : Pending) : Reply → List Rule × List Eff
  | .decision true c =>
    match schemeCheck s.cfg p.url with
    | some e => (s.rules, [.send p.port (resultJson p.id false (some e))])
    | none =>
      ((ruleOf p true c).toList ++ s.rules, [openEff p.url, .send p.port (resultJson p.id true none)])
  | .decision false c =>
    ((ruleOf p false c).toList ++ s.rules, [.send p.port (resultJson p.id false (some "user-denied"))])
  | _ => (s.rules, [.send p.port (resultJson p.id false (some "blocked-by-policy"))])

def onReply (_h : Host) (_w : World) (s : St) (n : Nat) (rep : Reply) : St × List Eff :=
  match s.pending.find? (·.n == n) with
  | none => (s, [])
  | some p =>
    let (rules, effs) := answer s p rep
    ({ s with rules, pending := s.pending.filter (·.n != n) }, effs)

def onEvent (_h : Host) (_w : World) (s : St) (_e : HostEvent) : St × List Eff := (s, [])

def drop (s : St) (p : PortId) : St × List Eff :=
  ({ s with pending := s.pending.filter (·.port != p) },
   (s.pending.filter (·.port == p)).map fun q => .effect (.cancel ⟨.link, q.n⟩))

def mentions (s : St) (p : PortId) : Bool := s.pending.any (·.port == p)

/-! ### Properties: codec and per-endpoint state -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  obtain ⟨id, u, l⟩ := r
  cases l <;> simp [decode, encodeReq, labelOf, Json.msg, Json.mkObj, Json.getStr?, Json.get?,
    Json.lookup, reqId?]

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp [drop, mentions] at h ⊢
  obtain ⟨x, hx, -, hq⟩ := h
  exact ⟨x, hx, hq⟩

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  obtain ⟨id, url, l⟩ := r
  simp only [handle] at hm
  split at hm
  · exact .inl hm
  · exact .inl hm
  · split at hm
    · exact .inl hm
    · simp only [mentions, List.any_cons] at hm
      rcases Bool.or_eq_true _ _ ▸ hm with h1 | h1
      · exact .inr ⟨cx, hcx, by simpa using h1⟩
      · exact .inl h1

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  simp only [onReply] at hm
  split at hm
  · exact hm
  · simp [mentions] at hm ⊢
    obtain ⟨x, hx, hq⟩ := hm
    exact ⟨x, hx, hq.2⟩

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q :=
  .inl hm

/-- Teardown withdraws exactly the endpoint's outstanding prompts. -/
theorem drop_cancels (s : St) (p : PortId) :
    (drop s p).2 = (s.pending.filter (·.port == p)).map fun q => .effect (.cancel ⟨.link, q.n⟩) := rfl

/-! ### Properties lifted from `NapLink` -/

theorem schemeCheck_ok {cfg : Cfg} {url : String} (h : schemeCheck cfg url = none) :
    ∃ sc, schemeOf url = some sc ∧ sc ∉ forbidden ∧ sc ∈ cfg.allowedSchemes := by
  unfold schemeCheck at h
  split at h
  · simp at h
  · rename_i sc hs
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hf
        simp only [not_or, Classical.not_not] at hf
        exact ⟨sc, hs, hf.1, hf.2⟩

theorem verdict_allow {s : St} {k : ManifestKey} {url : String} (h : verdict s k url = .allow) :
    schemeCheck s.cfg url = none ∧ ruleDenies s k url = false ∧ ruleAllows s k url = true := by
  unfold verdict at h
  split at h
  · simp at h
  · rename_i hc
    split at h
    · simp at h
    · rename_i hd
      split at h
      · rename_i ha
        exact ⟨hc, by simpa using hd, ha⟩
      · split at h <;> simp at h

/-- What `handle` can emit. -/
theorem handle_effs (h : Host) (w : World) (cx : Ctx) (s : St) (id url : String)
    (l : Option String) (e : Eff) (he : e ∈ (handle h w cx s (.openUrl id url l)).2) :
    (∃ err, e = .send cx.port (resultJson id false (some err))) ∨
    (verdict s cx.identity.key url = .allow ∧
      (e = openEff url ∨ e = .send cx.port (resultJson id true none))) ∨
    (verdict s cx.identity.key url = .ask ∧
      e = .call ⟨.link, s.next⟩ (.prompt .link "open" (promptDetails cx url l))) := by
  simp only [handle] at he
  split at he
  · simp at he; exact .inl ⟨_, he⟩
  · rename_i hv
    simp at he
    exact .inr (.inl ⟨hv, he⟩)
  · rename_i hv
    split at he
    · simp at he; exact .inl ⟨_, he⟩
    · simp at he; exact .inr (.inr ⟨hv, he⟩)

theorem answer_effs (s : St) (p : Pending) (rep : Reply) (e : Eff) (he : e ∈ (answer s p rep).2) :
    (∃ err, e = .send p.port (resultJson p.id false (some err))) ∨
    ((∃ c, rep = .decision true c) ∧ schemeCheck s.cfg p.url = none ∧
      (e = openEff p.url ∨ e = .send p.port (resultJson p.id true none))) := by
  unfold answer at he
  split at he
  · split at he
    · simp at he; exact .inl ⟨_, he⟩
    · rename_i hc
      simp at he
      exact .inr ⟨⟨_, rfl⟩, hc, he⟩
  · simp at he; exact .inl ⟨_, he⟩
  · simp at he; exact .inl ⟨_, he⟩

theorem onReply_effs (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (e : Eff)
    (he : e ∈ (onReply h w s n rep).2) :
    ∃ p ∈ s.pending, p.n = n ∧ e ∈ (answer s p rep).2 := by
  simp only [onReply] at he
  split at he
  · simp at he
  · rename_i p hp
    have := List.find?_some hp
    simp at this
    exact ⟨p, List.mem_of_find?_eq_some hp, this, he⟩

/-- Only absolute URLs with a policy-allowed, non-forbidden scheme are ever opened,
from a request or from a prompt answer. -/
theorem handle_opened_scheme_safe (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (a : Json)
    (he : Eff.effect (.nap .link "open" a) ∈ (handle h w cx s r).2) :
    ∃ url sc, a = openArgs url ∧ schemeOf url = some sc ∧ sc ∉ forbidden ∧ sc ∈ s.cfg.allowedSchemes := by
  obtain ⟨id, url, l⟩ := r
  rcases handle_effs h w cx s id url l _ he with ⟨_, h1⟩ | ⟨hv, h1 | h1⟩ | ⟨_, h1⟩
  · simp at h1
  · simp only [openEff, Eff.effect.injEq, Effect.nap.injEq, true_and] at h1
    exact ⟨url, (schemeCheck_ok (verdict_allow hv).1).elim fun sc h => ⟨sc, h1, h⟩⟩
  · simp at h1
  · simp at h1

theorem onReply_opened_scheme_safe (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply)
    (a : Json) (he : Eff.effect (.nap .link "open" a) ∈ (onReply h w s n rep).2) :
    ∃ url sc, a = openArgs url ∧ schemeOf url = some sc ∧ sc ∉ forbidden ∧ sc ∈ s.cfg.allowedSchemes := by
  obtain ⟨p, -, -, hp⟩ := onReply_effs h w s n rep _ he
  rcases answer_effs s p rep _ hp with ⟨_, h1⟩ | ⟨-, hc, h1 | h1⟩
  · simp at h1
  · simp only [openEff, Eff.effect.injEq, Effect.nap.injEq, true_and] at h1
    exact ⟨p.url, (schemeCheck_ok hc).elim fun sc h => ⟨sc, h1, h⟩⟩
  · simp at h1

/-- `javascript:`, `data:`, `blob:`, `file:` and the other forbidden schemes are never
opened, whatever the configuration lists. -/
theorem forbidden_never_opened (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req)
    (n : Nat) (rep : Reply) (url sc : String) (hs : schemeOf url = some sc) (hf : sc ∈ forbidden) :
    Eff.effect (.nap .link "open" (openArgs url)) ∉ (handle h w cx s r).2 ∧
    Eff.effect (.nap .link "open" (openArgs url)) ∉ (onReply h w s n rep).2 := by
  constructor
  · intro he
    obtain ⟨u, sc', hu, hs', hf', -⟩ := handle_opened_scheme_safe h w cx s r _ he
    simp [openArgs] at hu; subst hu
    rw [hs] at hs'; cases hs'; exact hf' hf
  · intro he
    obtain ⟨u, sc', hu, hs', hf', -⟩ := onReply_opened_scheme_safe h w s n rep _ he
    simp [openArgs] at hu; subst hu
    rw [hs] at hs'; cases hs'; exact hf' hf

/-- A request opens a link directly only under a persisted allow rule for this
napplet (and no deny rule). -/
theorem handle_opened_requires_rule (h : Host) (w : World) (cx : Ctx) (s : St) (id url : String)
    (l : Option String) (a : Json) (he : Eff.effect (.nap .link "open" a) ∈ (handle h w cx s (.openUrl id url l)).2) :
    a = openArgs url ∧ ruleAllows s cx.identity.key url = true ∧ ruleDenies s cx.identity.key url = false := by
  rcases handle_effs h w cx s id url l _ he with ⟨_, h1⟩ | ⟨hv, h1 | h1⟩ | ⟨_, h1⟩
  · simp at h1
  · simp only [openEff, Eff.effect.injEq, Effect.nap.injEq, true_and] at h1
    exact ⟨h1, (verdict_allow hv).2.2, (verdict_allow hv).2.1⟩
  · simp at h1
  · simp at h1

/-- A host reply opens a link only when it is the user's approval of an outstanding
prompt, and then only that prompt's URL. -/
theorem onReply_opened_requires_user (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply)
    (a : Json) (he : Eff.effect (.nap .link "open" a) ∈ (onReply h w s n rep).2) :
    (∃ c, rep = .decision true c) ∧ ∃ p ∈ s.pending, p.n = n ∧ a = openArgs p.url := by
  obtain ⟨p, hp, hn, hpe⟩ := onReply_effs h w s n rep _ he
  rcases answer_effs s p rep _ hpe with ⟨_, h1⟩ | ⟨hc, -, h1 | h1⟩
  · simp at h1
  · simp only [openEff, Eff.effect.injEq, Effect.nap.injEq, true_and] at h1
    exact ⟨hc, p, hp, hn, h1⟩
  · simp at h1

/-- Every open goes through `Effect.nap .link "open"`, whose contract is `noopener`;
the component has no other way to navigate. -/
theorem opened_only_via_open_effect (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req)
    (d : Domain) (op : String) (a : Json) (he : Eff.effect (.nap d op a) ∈ (handle h w cx s r).2) :
    d = .link ∧ op = "open" := by
  obtain ⟨id, url, l⟩ := r
  rcases handle_effs h w cx s id url l _ he with ⟨_, h1⟩ | ⟨-, h1 | h1⟩ | ⟨_, h1⟩
  · simp at h1
  · simp [openEff] at h1; exact ⟨h1.1, h1.2.1⟩
  · simp at h1
  · simp at h1

/-- Erase prompt details (the only place the label goes). -/
def eraseDetails : Eff → Eff
  | .call t (.prompt d k _) => .call t (.prompt d k .null)
  | e => e

/-- The napplet-supplied label never affects the decision, the state, or anything
sent; it only appears in the prompt text. -/
theorem label_irrelevant (h : Host) (w : World) (cx : Ctx) (s : St) (id url : String)
    (l₁ l₂ : Option String) :
    (handle h w cx s (.openUrl id url l₁)).1 = (handle h w cx s (.openUrl id url l₂)).1 ∧
    (handle h w cx s (.openUrl id url l₁)).2.map eraseDetails =
      (handle h w cx s (.openUrl id url l₂)).2.map eraseDetails := by
  simp only [handle]
  split
  · simp
  · simp
  · split <;> simp [eraseDetails]

/-- Every request is answered with its `id`, at once or when the prompt is answered. -/
theorem handle_answers (h : Host) (w : World) (cx : Ctx) (s : St) (id url : String) (l : Option String) :
    (∃ st e, Eff.send cx.port (resultJson id st e) ∈ (handle h w cx s (.openUrl id url l)).2) ∨
    (∃ p ∈ (handle h w cx s (.openUrl id url l)).1.pending, p.port = cx.port ∧ p.id = id) := by
  simp only [handle]
  split
  · exact .inl ⟨false, _, List.mem_singleton_self _⟩
  · exact .inl ⟨true, none, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩
  · split
    · exact .inl ⟨false, _, List.mem_singleton_self _⟩
    · exact .inr ⟨_, List.mem_cons_self .., rfl, rfl⟩

theorem onReply_answers (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (p : Pending)
    (hp : s.pending.find? (·.n == n) = some p) :
    ∃ st e, Eff.send p.port (resultJson p.id st e) ∈ (onReply h w s n rep).2 := by
  simp only [onReply, hp]
  unfold answer
  split
  · split
    · exact ⟨false, _, List.mem_singleton_self _⟩
    · exact ⟨true, none, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩
  · exact ⟨false, _, List.mem_singleton_self _⟩
  · exact ⟨false, _, List.mem_singleton_self _⟩

/-! ### Vectors (upstream examples) -/

/-- A sample endpoint and host for the vectors. -/
def sampleHost : Host :=
  { crypto := ⟨fun _ => "", fun _ => true⟩, verifyEvent := fun _ => true,
    sniff := fun _ => "application/octet-stream", rasterize := fun _ => none,
    looksCiphertext := fun _ => false, encryptedWith := fun _ => none, transform := id }

def sampleCtx : Ctx :=
  { port := 7, window := 1, identity := { dTag := some "reader", artifactHash := "aa", publisher := "pk" },
    exposed := [.link], inst := 0 }

def sampleWorld : World := { now := 1234567890, live := [sampleCtx], user := "" }

/-- A user who already allowed every link from this napplet. -/
def sampleSt : St := St.init { rules := [⟨sampleCtx.identity.key, .napplet, true⟩] }

def run (j : Json) (s : St := sampleSt) : List Eff :=
  match decode j with
  | .ok r => (handle sampleHost sampleWorld sampleCtx s r).2
  | .reject rs => rs.map (.send sampleCtx.port)
  | .unknown => []

#guard decode (Json.parse! "{ \"type\": \"link.open\", \"id\": \"l1\", \"url\": \"https://example.com/post/123\", \"options\": { \"label\": \"Read post\" } }")
  matches .ok (.openUrl "l1" "https://example.com/post/123" (some "Read post"))
#guard decode (Json.parse! "{ \"type\": \"link.open\", \"id\": \"l2\", \"url\": \"file:///etc/passwd\" }")
  matches .ok (.openUrl "l2" "file:///etc/passwd" none)
#guard decode (Json.parse! "{ \"type\": \"link.close\", \"id\": \"l2\" }") matches .unknown
#guard decode (Json.parse! "{ \"type\": \"link.open\", \"url\": \"https://a.b\" }") matches .reject []

#guard match run (Json.parse! "{ \"type\": \"link.open\", \"id\": \"l1\", \"url\": \"https://example.com/post/123\", \"options\": { \"label\": \"Read post\" } }") with
  | [.effect (.nap .link "open" a), .send 7 m] =>
    Json.same a (Json.parse! "{\"url\": \"https://example.com/post/123\"}") &&
    Json.same m (Json.parse! "{ \"type\": \"link.open.result\", \"id\": \"l1\", \"status\": \"opened\" }")
  | _ => false

#guard match run (Json.parse! "{ \"type\": \"link.open\", \"id\": \"l2\", \"url\": \"file:///etc/passwd\" }") with
  | [.send 7 m] => Json.same m (Json.parse! "{ \"type\": \"link.open.result\", \"id\": \"l2\", \"status\": \"denied\", \"error\": \"unsupported-scheme\" }")
  | _ => false

#guard match run (Json.parse! "{ \"type\": \"link.open\", \"id\": \"l3\", \"url\": \"/relative\" }") with
  | [.send 7 m] => Json.same m (Json.parse! "{ \"type\": \"link.open.result\", \"id\": \"l3\", \"status\": \"denied\", \"error\": \"invalid-url\" }")
  | _ => false

#guard match run (Json.parse! "{ \"type\": \"link.open\", \"id\": \"l4\", \"url\": 5 }") with
  | [.send 7 m] => Json.same m (Json.parse! "{ \"type\": \"link.open.result\", \"id\": \"l4\", \"status\": \"denied\", \"error\": \"invalid-url\" }")
  | _ => false

-- Without a rule, the user is asked; approval opens, refusal is `user-denied`.
#guard match handle sampleHost sampleWorld sampleCtx (St.init {}) (.openUrl "l5" "https://example.com/" (some "Go")) with
  | (s, [.call ⟨.link, 0⟩ (.prompt .link "open" d)]) =>
    Json.same d (Json.parse! "{\"url\":\"https://example.com/\",\"host\":\"example.com\",\"label\":\"Go\",\"napplet\":\"nip5d:35129:pk:reader\"}") &&
    (match onReply sampleHost sampleWorld s 0 (.decision true (some "host")) with
     | (s', [.effect (.nap .link "open" _), .send 7 m]) =>
       Json.same m (Json.parse! "{ \"type\": \"link.open.result\", \"id\": \"l5\", \"status\": \"opened\" }") &&
       s'.pending.isEmpty && ruleAllows s' sampleCtx.identity.key "https://example.com/other"
     | _ => false) &&
    (match onReply sampleHost sampleWorld s 0 (.decision false none) with
     | (_, [.send 7 m]) => Json.same m (Json.parse! "{ \"type\": \"link.open.result\", \"id\": \"l5\", \"status\": \"denied\", \"error\": \"user-denied\" }")
     | _ => false)
  | _ => false

end Napplet.Run.Link
