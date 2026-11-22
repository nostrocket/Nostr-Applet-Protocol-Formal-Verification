/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Basic

/-!
# Building the `srcdoc` (NIP-5D §Security, NAPPLETS-SPEC §16.1)

`buildSrcdoc bytes csp bootstrap` is the document the host puts in the iframe's
`srcdoc`: the verified artifact bytes with the CSP `<meta>` as the first element of
`<head>`, immediately followed by the bootstrap `<script>`, so both come before any
napplet-controlled element in parse order.

The tokeniser is modelled from the WHATWG HTML tokenizer as far as the insertion point
needs it (`step`): whitespace runs, comments (with the abrupt `<!-->` and `<!--->`
endings and the `--!>` ending), markup declarations and bogus comments (`<!DOCTYPE …>`,
`<!…>`, `<?…>`, `</…>` with a non-letter), the empty end tag `</>`, start and end tags
with the attribute states (quoted values may contain `>`), ASCII case folding of tag
names, and end of input inside any of them. Everything else is text.

The insertion point (`split`) is after the longest run of complete tokens that create no
element before `<head>` (whitespace, comments, declarations, `</>`, `<html …>` start
tags), and after a `<head …>` start tag if that is the next token. When there is no such
`<head>`, `buildSrcdoc` inserts its own `<head>`; the HTML tree builder then puts the
napplet's own head content (`<base>`, `<meta charset>`, `<title>`, scripts before
`<body>`) after the injected elements, in the same head. A leading UTF-8 BOM is removed,
as UTF-8 decoding removes it; kept in a `srcdoc` string it would be text and push the
CSP into `<body>`, where browsers ignore it.

Main results:
* `buildSrcdoc_bytes`: the output is the (BOM-stripped) verified bytes with the injected
  bytes inserted at one point;
* `csp_first`: the first tokens of the output are complete napplet tokens that create no
  element, then a `<head>` start tag, then the CSP `<meta>`, then the bootstrap
  `<script>`: nothing from the napplet comes before the CSP in parse order;
* `scriptSafe` (checked for the shipped bootstrap in `Bootstrap.lean`): the bootstrap text
  contains no `</script` and no `<!--`, so the script element ends at the injected
  `</script>` and the bootstrap runs before any napplet script.
-/

namespace Napplet.Srcdoc

/-- Bytes as numbers, so the tokenizer can match on literals. -/
abbrev Code := List Nat

def isWs (c : Nat) : Bool := c == 9 || c == 10 || c == 12 || c == 13 || c == 32
def isAlpha (c : Nat) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
def lower (c : Nat) : Nat := if 65 ≤ c && c ≤ 90 then c + 32 else c

def codes (s : String) : Code := s.toUTF8.toList.map UInt8.toNat

/-- ASCII text as codes. -/
def ascii (s : String) : Code := s.toList.map Char.toNat

/-! ## Scanners -/

/-- Through the first `>` (declarations, bogus comments). -/
def scanGt : Code → Option (Code × Code)
  | [] => none
  | c :: r => if c = 62 then some ([c], r) else (scanGt r).map fun p => (c :: p.1, p.2)

/-- One transition of a scanner; `none` accepts. -/
def run (δ : Nat → Nat → Option Nat) : Nat → Code → Option (Code × Code)
  | _, [] => none
  | st, c :: r =>
    match δ st c with
    | none => some ([c], r)
    | some st' => (run δ st' r).map fun p => (c :: p.1, p.2)

/-- Tag states after `<` and the first letter (0 = tag name, 1 = before attribute name,
2 = attribute name, 3 = after attribute name, 4 = before attribute value, 5 and 6 =
double- and single-quoted value, 7 = unquoted value, 8 = after quoted value, 9 =
self-closing start tag). `none` accepts (emits the tag). -/
def tagδ (st c : Nat) : Option Nat :=
  let ws := isWs c
  match st with
  | 0 => if ws then some 1 else if c = 47 then some 9 else if c = 62 then none else some 0
  | 1 => if ws then some 1 else if c = 47 then some 9 else if c = 62 then none else some 2
  | 2 => if ws then some 3 else if c = 47 then some 9 else if c = 61 then some 4
         else if c = 62 then none else some 2
  | 3 => if ws then some 3 else if c = 47 then some 9 else if c = 61 then some 4
         else if c = 62 then none else some 2
  | 4 => if ws then some 4 else if c = 34 then some 5 else if c = 39 then some 6
         else if c = 62 then none else some 7
  | 5 => if c = 34 then some 8 else some 5
  | 6 => if c = 39 then some 8 else some 6
  | 7 => if ws then some 1 else if c = 62 then none else some 7
  | 8 => if ws then some 1 else if c = 47 then some 9 else if c = 62 then none else some 2
  | _ => if c = 62 then none else if ws then some 1 else if c = 47 then some 9 else some 2

/-- The markup scanner after `<` (state 10). 11 = `<!`, 13 = `<!-`, 12 = `</`, 20 = bogus
comment or declaration (to the first `>`), 30–35 = comment start, start dash, comment,
end dash, end, end bang (the comment less-than-sign states collapse into these), 0–9 =
tag states (`tagδ`). `none` accepts. -/
def mδ (st c : Nat) : Option Nat :=
  match st with
  | 10 => if c = 33 then some 11 else if c = 63 then some 20 else if c = 47 then some 12
          else if isAlpha c then some 0 else some 20
  | 11 => if c = 45 then some 13 else if c = 62 then none else some 20
  | 13 => if c = 45 then some 30 else if c = 62 then none else some 20
  | 12 => if c = 62 then none else if isAlpha c then some 0 else some 20
  | 20 => if c = 62 then none else some 20
  | 30 => if c = 45 then some 31 else if c = 62 then none else some 32
  | 31 => if c = 45 then some 34 else if c = 62 then none else some 32
  | 32 => if c = 45 then some 33 else some 32
  | 33 => if c = 45 then some 34 else some 32
  | 34 => if c = 62 then none else if c = 33 then some 35 else if c = 45 then some 34 else some 32
  | 35 => if c = 45 then some 33 else if c = 62 then none else some 32
  | _ => tagδ st c

theorem scanGt_app : ∀ {z c r : Code}, scanGt z = some (c, r) →
    z = c ++ r ∧ c ≠ [] ∧ ∀ y, scanGt (c ++ y) = some (c, y)
  | [], _, _, h => by simp [scanGt] at h
  | d :: z, c, r, h => by
    simp only [scanGt] at h
    split at h
    · rename_i hd; cases h; exact ⟨rfl, by simp, fun y => by simp [scanGt, hd]⟩
    · rename_i hd
      cases hz : scanGt z with
      | none => rw [hz] at h; cases h
      | some p =>
        rw [hz] at h; cases h
        obtain ⟨h1, -, h3⟩ := scanGt_app hz
        exact ⟨by rw [h1]; rfl, by simp, fun y => by simp [scanGt, hd, h3 y]⟩

theorem run_app {δ : Nat → Nat → Option Nat} : ∀ {st : Nat} {z c r : Code}, run δ st z = some (c, r) →
    z = c ++ r ∧ c ≠ [] ∧ ∀ y, run δ st (c ++ y) = some (c, y)
  | _, [], _, _, h => by simp [run] at h
  | st, d :: z, c, r, h => by
    simp only [run] at h
    split at h
    · rename_i hd; cases h; exact ⟨rfl, by simp, fun y => by simp [run, hd]⟩
    · rename_i st' hd
      cases hz : run δ st' z with
      | none => rw [hz] at h; cases h
      | some p =>
        rw [hz] at h; cases h
        obtain ⟨h1, -, h3⟩ := run_app hz
        exact ⟨by rw [h1]; rfl, by simp, fun y => by simp [run, hd, h3 y]⟩

/-! ## Tokens -/

inductive Tok where
  | ws
  /-- A comment, declaration (`<!DOCTYPE …>`, `<!…>`) or bogus comment (`<?…>`, `</…>`). -/
  | decl
  /-- `</>`: no token at all in HTML. -/
  | nothing
  | startTag (name : Code) (raw : Code)
  | endTag (name : Code)
  | text
  /-- End of input inside a comment, declaration or tag: the rest is consumed. -/
  | eof
  deriving DecidableEq, Repr

/-- Tag name of a scanned tag (`x` starts at the first letter): up to whitespace, `/` or
`>`, ASCII-lowercased. -/
def nameOf (x : Code) : Code :=
  (x.takeWhile fun c => !(isWs c || c == 47 || c == 62)).map lower

/-- The token a complete markup run `<…>` is. -/
def label : Code → Tok
  | [60, 47, 62] => .nothing
  | 60 :: 47 :: c :: rest => if isAlpha c then .endTag (nameOf (c :: rest)) else .decl
  | 60 :: c :: rest => if isAlpha c then .startTag (nameOf (c :: rest)) (60 :: c :: rest) else .decl
  | _ => .decl

/-- Does `<` followed by `d` start markup (rather than the text `<`)? -/
def opens (d : Nat) : Bool := d == 33 || d == 63 || d == 47 || isAlpha d

/-- After `<`: the token and the bytes it consumes after the `<`. -/
def lt : Code → Tok × Code × Code
  | [] => (.text, [], [])
  | d :: r =>
    if opens d then
      match run mδ 10 (d :: r) with
      | some (x, y) => (label (60 :: x), x, y)
      | none => (.eof, d :: r, [])
    else (.text, [], d :: r)

/-- One token: the token, the bytes it consumes, the rest. -/
def step : Code → Option (Tok × Code × Code)
  | [] => none
  | c :: r =>
    if isWs c then some (.ws, (c :: r).takeWhile isWs, (c :: r).dropWhile isWs)
    else if c = 60 then let (t, x, y) := lt r; some (t, 60 :: x, y)
    else some (.text, [c], r)

/-- The first `n` tokens and the bytes after them. -/
def lexR : Nat → Code → List Tok × Code
  | 0, z => ([], z)
  | n + 1, z =>
    match step z with
    | none => ([], z)
    | some (t, _, r) => let (ts, w) := lexR n r; (t :: ts, w)

/-- The first `n` tokens. -/
def lexN (n : Nat) (z : Code) : List Tok := (lexR n z).1

/-- Tokens that create no element before `<head>`. -/
def Tok.allowed : Tok → Bool
  | .ws | .decl | .nothing => true
  | .startTag n _ => n == ascii "html"
  | _ => false

def Tok.isHead : Tok → Bool
  | .startTag n _ => n == ascii "head"
  | _ => false

/-! ## Prefix stability: a complete token does not look past its last byte -/

theorem lt_app {z x r : Code} {t : Tok} (h : lt z = (t, x, r)) (ht : t ≠ .eof) (htx : t ≠ .text) :
    z = x ++ r ∧ x ≠ [] ∧ ∀ y, lt (x ++ y) = (t, x, y) := by
  match z, h with
  | [], h => simp only [lt, Prod.mk.injEq] at h; exact absurd h.1.symm htx
  | d :: z', h =>
    simp only [lt] at h
    split at h
    · rename_i hd
      split at h
      · rename_i x' y' hr
        obtain ⟨h1, h2, h3⟩ := run_app hr
        simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨h1, h2, fun y => ?_⟩
        match x', h1, h3 with
        | [], h1, _ => exact absurd rfl h2
        | e :: x'', h1, h3 =>
          simp only [List.cons_append, List.cons.injEq] at h1
          obtain ⟨rfl, -⟩ := h1
          simp only [List.cons_append, lt, hd, ↓reduceIte]
          rw [← List.cons_append, h3 y]
      · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm ht
    · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm htx

theorem takeWhile_dropWhile_head {p : Nat → Bool} : ∀ (z : Code),
    ∀ b ∈ (z.dropWhile p).head?, p b = false
  | [], b, h => by simp at h
  | c :: z, b, h => by
    by_cases hc : p c = true
    · simp only [List.dropWhile_cons, hc, ↓reduceIte] at h; exact takeWhile_dropWhile_head z b h
    · simp only [List.dropWhile_cons, hc, Bool.false_eq_true, ↓reduceIte, List.head?_cons,
        Option.mem_def, Option.some.injEq] at h
      subst h; simpa using hc

theorem takeWhile_all {p : Nat → Bool} : ∀ (z : Code), ∀ b ∈ z.takeWhile p, p b = true
  | [], b, h => by simp at h
  | c :: z, b, h => by
    by_cases hc : p c = true
    · simp only [List.takeWhile_cons, hc, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hc
      · exact takeWhile_all z b h
    · simp [List.takeWhile_cons, hc] at h

theorem takeWhile_app_all {p : Nat → Bool} : ∀ (c y : Code), (∀ b ∈ c, p b = true) →
    (∀ b ∈ y.head?, p b = false) → (c ++ y).takeWhile p = c ∧ (c ++ y).dropWhile p = y
  | [], [], _, _ => by simp
  | [], b :: y, _, hy => by
    have := hy b (by simp)
    simp [List.takeWhile_cons, List.dropWhile_cons, this]
  | d :: c, y, hc, hy => by
    have hd := hc d (by simp)
    obtain ⟨h1, h2⟩ := takeWhile_app_all c y (fun b hb => hc b (List.mem_cons_of_mem _ hb)) hy
    simp [List.takeWhile_cons, List.dropWhile_cons, hd, h1, h2]

theorem takeWhile_app_of_not {p : Nat → Bool} : ∀ {c : Code} (y : Code), (∃ b ∈ c, p b = false) →
    (c ++ y).takeWhile p = c.takeWhile p
  | [], _, ⟨_, h, _⟩ => by simp at h
  | d :: c, y, ⟨b, hb, hpb⟩ => by
    simp only [List.cons_append, List.takeWhile_cons]
    by_cases hd : p d = true
    · simp only [hd, ↓reduceIte]
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [hd] at hpb; cases hpb
      · rw [takeWhile_app_of_not y ⟨b, hb, hpb⟩]
    · simp [hd]

/-- The step lemma: a complete token other than text consumes the same bytes whatever
follows, provided a whitespace run is followed by a non-whitespace byte. -/
theorem step_app {z c r : Code} {t : Tok} (h : step z = some (t, c, r)) (ht : t ≠ .eof)
    (htx : t ≠ .text) (y : Code) (hy : t = .ws → ∀ b ∈ y.head?, isWs b = false) :
    z = c ++ r ∧ c ≠ [] ∧ step (c ++ y) = some (t, c, y) := by
  match z, h with
  | [], h => simp [step] at h
  | d :: z', h =>
    simp only [step] at h
    split at h
    · rename_i hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hw := takeWhile_all (p := isWs) (d :: z')
      refine ⟨(List.takeWhile_append_dropWhile).symm, by simp [List.takeWhile_cons, hd], ?_⟩
      obtain ⟨h1, h2⟩ := takeWhile_app_all _ y hw (hy rfl)
      have hne : ∃ c' rest, (d :: z').takeWhile isWs = c' :: rest := by
        simp [List.takeWhile_cons, hd]
      obtain ⟨c', rest, he⟩ := hne
      rw [he] at h1 h2 ⊢
      have hc' : isWs c' = true := hw c' (by rw [he]; simp)
      simp only [List.cons_append, step, hc', ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      rw [← List.cons_append, h1, h2]; simp
    · rename_i hd
      split at h
      · rename_i hlt
        generalize hl : lt z' = res at h
        obtain ⟨t', x, y'⟩ := res
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨h1, -, h3⟩ := lt_app hl ht htx
        subst hlt
        refine ⟨by rw [h1]; rfl, by simp, ?_⟩
        simp only [List.cons_append, step, hd, ↓reduceIte, h3 y]; rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact absurd h.1.symm htx

/-! ## Building the document -/

/-- The NAPPLETS-SPEC §16.1 baseline directives, in order, joined as one policy. -/
def baselineCsp : String :=
  "default-src 'none'; script-src 'unsafe-inline' 'wasm-unsafe-eval'; style-src 'unsafe-inline'; " ++
  "img-src data: blob:; font-src data:; connect-src 'none'; worker-src 'none'; child-src 'none'; " ++
  "frame-src 'none'; media-src 'none'; object-src 'none'; manifest-src 'none'; base-uri 'none'; " ++
  "form-action 'none'"

/-- Attribute-value escaping for a double-quoted value. -/
def escAttr (s : String) : Code :=
  (codes s).flatMap fun c => if c = 34 then ascii "&quot;" else if c = 38 then ascii "&amp;" else [c]

theorem escAttr_noquote (s : String) : ∀ b ∈ escAttr s, b ≠ 34 := by
  intro b hb
  simp only [escAttr, List.mem_flatMap] at hb
  obtain ⟨c, -, hc⟩ := hb
  split at hc
  · simp [ascii] at hc; omega
  · split at hc
    · simp [ascii] at hc; omega
    · rename_i h1 _; simp at hc; omega

def metaOpen : Code := ascii "<meta http-equiv=\"Content-Security-Policy\" content=\""
def metaClose : Code := ascii "\">"
def cspMeta (csp : String) : Code := metaOpen ++ escAttr csp ++ metaClose
def headOpen : Code := ascii "<head>"
def scriptOpen : Code := ascii "<script>"
def scriptClose : Code := ascii "</script>"

/-- The injected bytes: `<head>` unless the napplet's own `<head>` precedes, the CSP
`<meta>`, then the bootstrap script. -/
def inject (csp boot : String) (found : Bool) : Code :=
  (if found then [] else headOpen) ++ cspMeta csp ++ scriptOpen ++ codes boot ++ scriptClose

def stripBom : Code → Code
  | 0xEF :: 0xBB :: 0xBF :: r => r
  | z => z

/-- The napplet tokens before the insertion point, the bytes they cover, the rest, and
whether the last of them is the napplet's own `<head>`. -/
def split : Nat → Code → List Tok × Code × Code × Bool
  | 0, z => ([], [], z, false)
  | n + 1, z =>
    match step z with
    | none => ([], [], z, false)
    | some (t, c, r) =>
      if t.isHead then ([t], c, r, true)
      else if t.allowed then
        let (ts, p, q, f) := split n r
        (t :: ts, c ++ p, q, f)
      else ([], [], z, false)

def buildCodes (z : Code) (csp boot : String) : Code :=
  let z' := stripBom z
  let (_, p, q, f) := split (z'.length + 1) z'
  p ++ inject csp boot f ++ q

/-- The `srcdoc` bytes for verified artifact `bytes`, policy `csp` and bootstrap `boot`. -/
def buildSrcdoc (bytes : Bytes) (csp boot : String) : Bytes :=
  (buildCodes (bytes.map UInt8.toNat) csp boot).map Nat.toUInt8

/-! ## The verified bytes are kept -/

theorem split_bytes : ∀ (n : Nat) (z : Code), let r := split n z; z = r.2.1 ++ r.2.2.1
  | 0, z => rfl
  | n + 1, z => by
    simp only [split]
    split
    · rfl
    · rename_i t c r hs
      split
      · exact (step_app hs (by cases t <;> simp_all [Tok.isHead]) (by cases t <;> simp_all [Tok.isHead]) []
          (by intro h; subst h; simp [Tok.isHead] at *)).1
      · split
        · rename_i ha
          have hz := (step_app hs (by cases t <;> simp_all [Tok.allowed]) (by cases t <;> simp_all [Tok.allowed]) []
            (fun _ => by simp)).1
          have ih := split_bytes n r
          generalize split n r = res at ih ⊢
          obtain ⟨ts, p, q, f⟩ := res
          simp only at ih ⊢
          rw [hz, ih, List.append_assoc]
        · rfl

/-- The output is the verified bytes (without a leading BOM) with the injected bytes
inserted at one point. -/
theorem buildCodes_bytes (z : Code) (csp boot : String) :
    ∃ p q f, stripBom z = p ++ q ∧ buildCodes z csp boot = p ++ inject csp boot f ++ q := by
  have h := split_bytes ((stripBom z).length + 1) (stripBom z)
  simp only [buildCodes]
  generalize split ((stripBom z).length + 1) (stripBom z) = res at h ⊢
  obtain ⟨ts, p, q, f⟩ := res
  exact ⟨p, q, f, h, rfl⟩

theorem stripBom_eq (z : Code) : z = stripBom z ∨ z = [0xEF, 0xBB, 0xBF] ++ stripBom z := by
  unfold stripBom
  split
  · exact .inr rfl
  · exact .inl rfl

/-! ## Parse order -/

/-- Drive a scanner over a prefix without accepting. -/
def drive (δ : Nat → Nat → Option Nat) : Nat → Code → Option Nat
  | st, [] => some st
  | st, c :: s =>
    match δ st c with
    | none => none
    | some st' => drive δ st' s

theorem run_drive {δ : Nat → Nat → Option Nat} : ∀ {st st' : Nat} {s : Code} (w : Code),
    drive δ st s = some st' → run δ st (s ++ w) = (run δ st' w).map fun p => (s ++ p.1, p.2)
  | st, st', [], w, h => by
    simp only [drive, Option.some.injEq] at h; subst h
    cases hr : run δ st w <;> simp [hr]
  | st, st', c :: s, w, h => by
    simp only [drive] at h
    split at h
    · cases h
    · rename_i st'' hc
      simp only [List.cons_append, run, hc]
      rw [run_drive w h]
      cases hr : run δ st' w <;> simp [hr]

theorem drive_dq : ∀ (s : Code), (∀ b ∈ s, b ≠ 34) → drive mδ 5 s = some 5
  | [], _ => rfl
  | c :: s, h => by
    have hc := h c (by simp)
    have := drive_dq s (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp [drive, mδ, tagδ, hc, this]

theorem lt_of_run {d : Nat} {z' x y : Code} (ho : opens d = true)
    (hr : run mδ 10 (d :: z') = some (x, y)) : lt (d :: z') = (label (60 :: x), x, y) := by
  simp [lt, ho, hr]

/-- A start tag of a letter other than `/`: its name and raw bytes. -/
theorem label_start {d : Nat} {rest : Code} (hd : isAlpha d = true) (h47 : d ≠ 47) :
    label (60 :: d :: rest) = .startTag (nameOf (d :: rest)) (60 :: d :: rest) := by
  unfold label
  split <;> simp_all

/-- Lexing a start tag whose bytes are `60 :: d :: s` followed by anything. -/
theorem step_tag {d : Nat} {s w : Code} (hd : isAlpha d = true) (h47 : d ≠ 47)
    (hr : run mδ 10 (d :: s ++ w) = some (d :: s, w)) :
    step (60 :: d :: s ++ w) = some (.startTag (nameOf (d :: s)) (60 :: d :: s), 60 :: d :: s, w) := by
  have ho : opens d = true := by simp [opens, hd]
  have hl := lt_of_run (z' := s ++ w) ho hr
  simp only [List.cons_append] at hl ⊢
  simp only [step, isWs, Nat.reduceEqDiff, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hl,
    label_start hd h47]
  rfl

theorem lex_meta (csp : String) (w : Code) :
    step (cspMeta csp ++ w) = some (.startTag (ascii "meta") (cspMeta csp), cspMeta csp, w) := by
  have hm : metaOpen = 60 :: 109 :: metaOpen.drop 2 := by decide
  have hA : drive mδ 10 (109 :: metaOpen.drop 2) = some 5 := by decide
  have hE := drive_dq (escAttr csp) (escAttr_noquote csp)
  have hrun : run mδ 10 (109 :: (metaOpen.drop 2 ++ escAttr csp ++ metaClose) ++ w) =
      some (109 :: (metaOpen.drop 2 ++ escAttr csp ++ metaClose), w) := by
    have : 109 :: (metaOpen.drop 2 ++ escAttr csp ++ metaClose) ++ w =
        (109 :: metaOpen.drop 2) ++ (escAttr csp ++ (metaClose ++ w)) := by simp
    rw [this, run_drive _ hA, run_drive _ hE]
    simp [metaClose, ascii, run, mδ, tagδ, isWs]
  have hname : nameOf (109 :: (metaOpen.drop 2 ++ escAttr csp ++ metaClose)) = ascii "meta" := by
    have : 109 :: (metaOpen.drop 2 ++ escAttr csp ++ metaClose) =
        (109 :: metaOpen.drop 2) ++ (escAttr csp ++ metaClose) := by simp
    rw [this, nameOf, takeWhile_app_of_not _ ⟨32, by decide, by decide⟩]
    decide
  have := step_tag (d := 109) (s := metaOpen.drop 2 ++ escAttr csp ++ metaClose) (w := w)
    (by decide) (by decide) hrun
  rw [hname] at this
  have hc : cspMeta csp = 60 :: 109 :: (metaOpen.drop 2 ++ escAttr csp ++ metaClose) := by
    simp only [cspMeta]; rw [hm]; simp
  rw [hc]
  simpa using this

theorem lex_head (w : Code) :
    step (headOpen ++ w) = some (.startTag (ascii "head") headOpen, headOpen, w) := by
  have hr : run mδ 10 (104 :: [101, 97, 100, 62] ++ w) = some (104 :: [101, 97, 100, 62], w) := by
    simp [run, mδ, tagδ, isWs, isAlpha]
  have := step_tag (by decide) (by decide) hr
  have hn : nameOf (104 :: [101, 97, 100, 62]) = ascii "head" := by decide
  rw [hn] at this
  exact this

theorem lex_script (w : Code) :
    step (scriptOpen ++ w) = some (.startTag (ascii "script") scriptOpen, scriptOpen, w) := by
  have hr : run mδ 10 (115 :: [99, 114, 105, 112, 116, 62] ++ w) = some (115 :: [99, 114, 105, 112, 116, 62], w) := by
    simp [run, mδ, tagδ, isWs, isAlpha]
  have := step_tag (by decide) (by decide) hr
  have hn : nameOf (115 :: [99, 114, 105, 112, 116, 62]) = ascii "script" := by decide
  rw [hn] at this
  exact this

theorem lexR_step {k : Nat} {z c r : Code} {t : Tok} (h : step z = some (t, c, r)) :
    lexR (k + 1) z = (t :: (lexR k r).1, (lexR k r).2) := by
  simp [lexR, h]

theorem lexN_step {k : Nat} {z c r : Code} {t : Tok} (h : step z = some (t, c, r)) :
    lexN (k + 1) z = t :: lexN k r := by
  simp [lexN, lexR_step h]

theorem label_ne_ws (w : Code) : label w ≠ .ws := by
  unfold label; split <;> (try split) <;> simp

theorem lt_ne_ws (z : Code) : (lt z).1 ≠ .ws := by
  unfold lt
  split
  · simp
  · split
    · split
      · exact label_ne_ws _
      · simp
    · simp

theorem step_ws_rest {z c r : Code} (h : step z = some (.ws, c, r)) : ∀ b ∈ r.head?, isWs b = false := by
  match z, h with
  | [], h => simp [step] at h
  | d :: z', h =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact takeWhile_dropWhile_head _
    · split at h
      · have hn := lt_ne_ws z'
        generalize lt z' = res at h hn; obtain ⟨t, x, y⟩ := res
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact absurd h.1 hn
      · simp at h

theorem allowed_ne {t : Tok} (h : t.allowed = true ∨ t.isHead = true) : t ≠ .eof ∧ t ≠ .text := by
  cases t <;> simp_all [Tok.allowed, Tok.isHead]

/-- Lexing the bytes before the insertion point, then anything that starts with a
non-whitespace byte, gives the napplet tokens first. -/
theorem split_lex : ∀ (n : Nat) (z x : Code), (∀ b ∈ x.head?, isWs b = false) →
    let r := split n z
    (r.2.2.2 = true → ∃ ts h, r.1 = ts ++ [h] ∧ h.isHead = true ∧ ∀ t ∈ ts, t.allowed = true) ∧
    (r.2.2.2 = false → ∀ t ∈ r.1, t.allowed = true) ∧
    ∀ m, lexR (r.1.length + m) (r.2.1 ++ x) = (r.1 ++ (lexR m x).1, (lexR m x).2)
  | 0, z, x, _ => by simp [split]
  | n + 1, z, x, hx => by
    simp only [split]
    split
    · simp
    · rename_i t c r hs
      split
      · rename_i hh
        obtain ⟨hne, htx⟩ := allowed_ne (.inr hh)
        have hst := (step_app hs hne htx x (fun h => by subst h; simp [Tok.isHead] at hh)).2.2
        refine ⟨fun _ => ⟨[], t, rfl, hh, by simp⟩, fun h => by simp at h, fun m => ?_⟩
        simp only [List.length_singleton, List.singleton_append]
        rw [Nat.add_comm, lexR_step hst]
      · split
        · rename_i hn ha
          obtain ⟨hne, htx⟩ := allowed_ne (.inl ha)
          have hbytes := split_bytes n r
          obtain ⟨ih1, ih2, ih3⟩ := split_lex n r x hx
          generalize hres : split n r = res at hbytes ih1 ih2 ih3 ⊢
          obtain ⟨ts, p, q, f⟩ := res
          simp only at hbytes ih1 ih2 ih3 ⊢
          have hy : t = .ws → ∀ b ∈ (p ++ x).head?, isWs b = false := by
            intro htw
            subst htw
            cases p with
            | nil => simpa using hx
            | cons b p' =>
              have := step_ws_rest hs
              rw [hbytes] at this
              simpa using this
          have hst := (step_app hs hne htx (p ++ x) hy).2.2
          refine ⟨fun hf => ?_, fun hf t' ht' => ?_, fun m => ?_⟩
          · obtain ⟨ts', h, he, hh', hall⟩ := ih1 hf
            exact ⟨t :: ts', h, by simp [he], hh', fun t' ht' => by
              rcases List.mem_cons.mp ht' with rfl | ht'
              · exact ha
              · exact hall t' ht'⟩
          · rcases List.mem_cons.mp ht' with rfl | ht'
            · exact ha
            · exact ih2 hf t' ht'
          · simp only [List.length_cons, List.cons_append, List.append_assoc]
            rw [show ts.length + 1 + m = (ts.length + m) + 1 by omega, lexR_step hst, ih3 m]
        · simp

/-- **Parse order.** The first tokens of the `srcdoc` are napplet tokens that create no
element, then a `<head>` start tag (the napplet's or the injected one), then the CSP
`<meta>`, then the bootstrap `<script>` start tag; after them come exactly the bootstrap
text, the injected `</script>`, and the rest of the napplet's bytes. -/
theorem parse_order (z : Code) (csp boot : String) :
    ∃ ts h p q, (∀ t ∈ ts, t.allowed = true) ∧ h.isHead = true ∧ stripBom z = p ++ q ∧
      lexR (ts.length + 3) (buildCodes z csp boot) =
        (ts ++ [h, .startTag (ascii "meta") (cspMeta csp), .startTag (ascii "script") scriptOpen],
         codes boot ++ scriptClose ++ q) := by
  have hb := split_bytes ((stripBom z).length + 1) (stripBom z)
  simp only [buildCodes]
  have hl := split_lex ((stripBom z).length + 1) (stripBom z)
  generalize split ((stripBom z).length + 1) (stripBom z) = res at hl hb ⊢
  obtain ⟨toks, p, q, f⟩ := res
  have hx : ∀ b ∈ (inject csp boot f ++ q).head?, isWs b = false := by
    cases f <;> simp [inject, headOpen, cspMeta, metaOpen, ascii, isWs]
  obtain ⟨h1, h2, h3⟩ := hl _ hx
  simp only at h1 h2 h3 hb
  rw [List.append_assoc]
  cases f with
  | true =>
    obtain ⟨ts, h, rfl, hh, hall⟩ := h1 rfl
    refine ⟨ts, h, p, q, hall, hh, hb, ?_⟩
    have := h3 2
    simp only [List.length_append, List.length_singleton] at this
    rw [show ts.length + 3 = ts.length + 1 + 2 by omega, this]
    simp only [inject, List.nil_append, ↓reduceIte, List.append_assoc]
    rw [lexR_step (lex_meta csp _), lexR_step (lex_script _)]
    simp [lexR]
  | false =>
    refine ⟨toks, .startTag (ascii "head") headOpen, p, q, h2 rfl, by decide, hb, ?_⟩
    rw [h3 3]
    simp only [inject, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rw [lexR_step (lex_head _), lexR_step (lex_meta csp _), lexR_step (lex_script _)]
    simp [lexR]

/-- The CSP comes first: the token form of `parse_order`. -/
theorem csp_first (z : Code) (csp boot : String) :
    ∃ ts h, (∀ t ∈ ts, t.allowed = true) ∧ h.isHead = true ∧
      lexN (ts.length + 3) (buildCodes z csp boot) =
        ts ++ [h, .startTag (ascii "meta") (cspMeta csp), .startTag (ascii "script") scriptOpen] := by
  obtain ⟨ts, h, p, q, h1, h2, -, h4⟩ := parse_order z csp boot
  exact ⟨ts, h, h1, h2, by simp [lexN, h4]⟩

/-! ## Script data -/

/-- An appropriate end tag in script data: `</script` (any case) then whitespace, `/` or `>`. -/
def closeAtL : Code → Bool
  | 60 :: 47 :: a :: b :: c :: d :: e :: f :: g :: _ =>
    lower a == 115 && lower b == 99 && lower c == 114 && lower d == 105 && lower e == 112 &&
      lower f == 116 && (isWs g || g == 47 || g == 62)
  | _ => false

def closeAt (z : Code) : Bool := closeAtL (z.take 9)

/-- `<!--`, which enters the script data escaped states. -/
def escAtL : Code → Bool
  | [60, 33, 45, 45] => true
  | _ => false

def escAt (z : Code) : Bool := escAtL (z.take 4)

/-- Script data after a `<script>` start tag (HTML tokenizer script data state): the text
and the rest from the end tag on. `none` when `<!--` comes first: the escaped states,
which this model does not follow. -/
def scriptData : Code → Option (Code × Code)
  | [] => some ([], [])
  | c :: r =>
    if closeAt (c :: r) then some ([], c :: r)
    else if escAt (c :: r) then none
    else (scriptData r).map fun p => (c :: p.1, p.2)

/-- Script text that cannot end or escape early, even where it meets the injected
`</script>`. -/
def safeText (b : Code) : Bool :=
  (List.range b.length).all fun i =>
    !closeAt ((b ++ scriptClose).drop i) && !escAt ((b ++ scriptClose).drop i)

theorem closeAt_app {x : Code} (y : Code) (h : 9 ≤ x.length) : closeAt (x ++ y) = closeAt x := by
  simp only [closeAt, List.take_append_of_le_length h]

theorem escAt_app {x : Code} (y : Code) (h : 4 ≤ x.length) : escAt (x ++ y) = escAt x := by
  simp only [escAt, List.take_append_of_le_length h]

theorem scriptClose_eq : scriptClose = [60, 47, 115, 99, 114, 105, 112, 116, 62] := by decide

theorem scriptData_safe : ∀ (b w : Code),
    (∀ i < b.length, closeAt ((b ++ scriptClose).drop i) = false ∧ escAt ((b ++ scriptClose).drop i) = false) →
    scriptData (b ++ scriptClose ++ w) = some (b, scriptClose ++ w)
  | [], w, _ => by
    rw [scriptClose_eq]; simp [scriptData, closeAt, closeAtL, lower, isWs]
  | c :: b, w, h => by
    have h0 := h 0 (by simp)
    simp only [List.drop_zero] at h0
    have hl : 9 ≤ (c :: b ++ scriptClose).length := by rw [scriptClose_eq]; simp
    have hc : closeAt (c :: b ++ scriptClose ++ w) = false := by
      rw [List.append_assoc, ← List.append_assoc (c :: b), closeAt_app w hl, h0.1]
    have he : escAt (c :: b ++ scriptClose ++ w) = false := by
      rw [List.append_assoc, ← List.append_assoc (c :: b), escAt_app w (by omega), h0.2]
    have ih := scriptData_safe b w (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa using this)
    simp only [List.cons_append] at hc he ⊢
    simp only [scriptData, hc, he, Bool.false_eq_true, ↓reduceIte]
    have ih' : scriptData (b ++ (scriptClose ++ w)) = some (b, scriptClose ++ w) := by
      rw [← List.append_assoc]; exact ih
    simp [ih']

theorem safeText_spec {b : Code} (h : safeText b = true) :
    ∀ i < b.length, closeAt ((b ++ scriptClose).drop i) = false ∧ escAt ((b ++ scriptClose).drop i) = false := by
  intro i hi
  simp only [safeText, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  exact h i hi

theorem lex_scriptClose (w : Code) :
    step (scriptClose ++ w) = some (.endTag (ascii "script"), scriptClose, w) := by
  rw [scriptClose_eq]
  simp [step, isWs, lt, opens, isAlpha, run, mδ, tagδ, label, nameOf, lower, ascii]

/-- **The bootstrap runs before any napplet script.** With `safeText` bootstrap text,
after the bootstrap `<script>` start tag the tokenizer reads exactly the bootstrap as the
script's text, then the injected `</script>` end tag, and what follows is the napplet's
remaining bytes. Every napplet byte before the insertion point is in an element-free token
(`parse_order`), so no napplet script precedes the bootstrap. -/
theorem bootstrap_first (z : Code) (csp boot : String) (hs : safeText (codes boot) = true) :
    ∃ ts h p q, (∀ t ∈ ts, t.allowed = true) ∧ h.isHead = true ∧ stripBom z = p ++ q ∧
      lexR (ts.length + 3) (buildCodes z csp boot) =
        (ts ++ [h, .startTag (ascii "meta") (cspMeta csp), .startTag (ascii "script") scriptOpen],
         codes boot ++ scriptClose ++ q) ∧
      scriptData (codes boot ++ scriptClose ++ q) = some (codes boot, scriptClose ++ q) ∧
      step (scriptClose ++ q) = some (.endTag (ascii "script"), scriptClose, q) := by
  obtain ⟨ts, h, p, q, h1, h2, h3, h4⟩ := parse_order z csp boot
  exact ⟨ts, h, p, q, h1, h2, h3, h4, scriptData_safe _ q (safeText_spec hs), lex_scriptClose q⟩

/-- Safe as the text of the injected `<script>` element (`safeText` of its UTF-8 bytes). -/
def scriptSafe (js : String) : Bool := safeText (codes js)

/-! ## The byte-level statements -/

theorem codes_bytes (b : Bytes) : (b.map UInt8.toNat).map Nat.toUInt8 = b := by
  induction b with
  | nil => rfl
  | cons x b ih => simp [ih]

/-- `buildSrcdoc` keeps the verified bytes (minus a leading BOM) and inserts the injected
bytes at one point. -/
theorem buildSrcdoc_bytes (b : Bytes) (csp boot : String) :
    ∃ p q f, stripBom (b.map UInt8.toNat) = p ++ q ∧
      buildSrcdoc b csp boot = (p ++ inject csp boot f ++ q).map Nat.toUInt8 := by
  obtain ⟨p, q, f, h1, h2⟩ := buildCodes_bytes (b.map UInt8.toNat) csp boot
  exact ⟨p, q, f, h1, by simp only [buildSrcdoc, h2]⟩

/-! ## Vectors (adversarial documents) -/

def ofStr (s : String) : Bytes := s.toUTF8.toList

def outStr (doc : String) : String :=
  String.fromUTF8! (ByteArray.mk (buildSrcdoc (ofStr doc) "CSP" "B").toArray)

/-- Structural check: after the allowed tokens come `<head>`, the CSP meta and the script. -/
def cspFirstB (doc csp : String) : Bool :=
  let toks := lexN 200 (buildCodes ((ofStr doc).map UInt8.toNat) csp "boot()")
  match toks.dropWhile Tok.allowed with
  | h :: m :: sc :: _ => h.isHead && m == .startTag (ascii "meta") (cspMeta csp) &&
      sc == .startTag (ascii "script") scriptOpen
  | _ => false

def injected : String := "<meta http-equiv=\"Content-Security-Policy\" content=\"CSP\"><script>B</script>"

#guard outStr "" == "<head>" ++ injected
#guard outStr "<!DOCTYPE html><html><head><title>x</title></head></html>" ==
  "<!DOCTYPE html><html><head>" ++ injected ++ "<title>x</title></head></html>"
-- uppercase tags and doctype
#guard outStr "<!doctype HTML>\n<HTML LANG=en>\n <HEAD>\n<TITLE>x</TITLE>" ==
  "<!doctype HTML>\n<HTML LANG=en>\n <HEAD>" ++ injected ++ "\n<TITLE>x</TITLE>"
-- a BOM is dropped (UTF-8 decoding drops it; in a srcdoc string it would be text)
#guard outStr "﻿<!doctype html><head>" == "<!doctype html><head>" ++ injected
-- no html, no head: the CSP comes before the napplet's first element
#guard outStr "<title>x</title><script>e()</script>" == "<head>" ++ injected ++ "<title>x</title><script>e()</script>"
-- a script before head
#guard outStr "<script>e()</script><head></head>" == "<head>" ++ injected ++ "<script>e()</script><head></head>"
-- meta charset and base before head
#guard outStr "<meta charset=utf-8><head>" == "<head>" ++ injected ++ "<meta charset=utf-8><head>"
#guard outStr "<base href=https://evil.example/><head>" == "<head>" ++ injected ++ "<base href=https://evil.example/><head>"
-- comments that end early: `--!>`, `<!-->`, `<!--->`
#guard outStr "<!-- x --!><script>e()</script><head>" == "<!-- x --!><head>" ++ injected ++ "<script>e()</script><head>"
#guard outStr "<!--><script>e()</script>" == "<!--><head>" ++ injected ++ "<script>e()</script>"
#guard outStr "<!---><script>e()</script>" == "<!---><head>" ++ injected ++ "<script>e()</script>"
-- comments that do not end where they seem to
#guard outStr "<!-- a -- > b --><head>" == "<!-- a -- > b --><head>" ++ injected
#guard outStr "<!--<!-- x --><head>" == "<!--<!-- x --><head>" ++ injected
-- `>` inside a quoted attribute value does not end the tag
#guard outStr "<html data-x=\"><script>e()</script>\"><head>" ==
  "<html data-x=\"><script>e()</script>\"><head>" ++ injected
#guard outStr "<html data-x='>'><HEAD data-y=\">\">" == "<html data-x='>'><HEAD data-y=\">\">" ++ injected
-- unterminated constructs: the injection comes before them
#guard outStr "<!-- never closed <script>e()</script>" == "<head>" ++ injected ++ "<!-- never closed <script>e()</script>"
#guard outStr "<html lang=\"en" == "<head>" ++ injected ++ "<html lang=\"en"
#guard outStr "<head lang=\"en" == "<head>" ++ injected ++ "<head lang=\"en"
-- declarations, bogus comments and `</>` create no element
#guard outStr "<?xml version=\"1.0\"?><!x><head>" == "<?xml version=\"1.0\"?><!x><head>" ++ injected
#guard outStr "</><head>" == "</><head>" ++ injected
-- an end tag or text before head stops the scan
#guard outStr "</p><head>" == "<head>" ++ injected ++ "</p><head>"
#guard outStr "hi<head>" == "<head>" ++ injected ++ "hi<head>"
#guard outStr "< head>" == "<head>" ++ injected ++ "< head>"
-- an attribute value containing a double quote is escaped
#guard cspFirstB "<head>" "a\"b&c"
#guard ["", "<!DOCTYPE html><html><head>", "﻿<html>", "<script>e()</script>",
  "<!-- x --!><script>", "<html data-x=\">\"><head>", "<!-- open", "<html", "</p>", "<HEAD/>",
  "<!DOCTYPE html PUBLIC \"-//W3C//DTD>\" \"x\"><head>"].all (cspFirstB · baselineCsp)

end Napplet.Srcdoc
