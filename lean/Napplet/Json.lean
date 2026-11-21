/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

/-!
# JSON values (RFC 8259)

Every NIP-5D message is one JSON object (NIP-5D §Wire Format). This module gives
the model a JSON value type, a parser and a printer, so the composed runtime can
take the exact JSON a napplet posts and produce the exact JSON the shell sends.

* `Json` is the value type. Objects keep member order and may hold repeated
  names, as text can. `Json.get?` returns the **last** member with a name, which
  is what `JSON.parse` in a browser does (modelling decision 29).
* Numbers are exact decimals `m × 10^e` in normal form (`Json.Num`), so `8.5`,
  `21000` and `0.25` round-trip without floating point. A shell that uses IEEE
  doubles agrees on every value the NAPs use (integers below 2^53 and short
  decimals).
* `Json.parse` accepts RFC 8259 text with surrounding whitespace.
  `Json.render` prints compact JSON with `JSON.stringify` escaping.
* `Json.canon` sorts object members by name and keeps the last of each name.
  Two JSON texts mean the same message exactly when their canonical forms are
  equal, which is how the end-to-end vectors compare output.

The structured-clone transport of the web projection carries these values
directly; nothing in the model depends on the text form except the vectors.
-/

namespace Napplet

/-- An exact JSON number `mant × 10^exp`. -/
structure Num where
  mant : Int
  exp : Int
  deriving DecidableEq, Repr, Inhabited

namespace Num

/-- Strip trailing decimal zeros from the mantissa; zero has exponent 0. -/
def normalize (n : Num) : Num :=
  go n.mant n.exp (n.mant.natAbs + 1)
where
  go (m e : Int) : Nat → Num
    | 0 => ⟨m, e⟩
    | fuel + 1 =>
      if m = 0 then ⟨0, 0⟩
      else if m % 10 = 0 then go (m / 10) (e + 1) fuel
      else ⟨m, e⟩

def ofInt (i : Int) : Num := normalize ⟨i, 0⟩
def ofNat (n : Nat) : Num := ofInt n

/-- The value as a natural number, if it is one. -/
def toNat? (n : Num) : Option Nat :=
  if n.mant < 0 then none
  else if n.exp ≥ 0 then some (n.mant.toNat * 10 ^ n.exp.toNat)
  else none

/-- The value as an integer, if it is one. -/
def toInt? (n : Num) : Option Int :=
  if n.exp ≥ 0 then some (n.mant * 10 ^ n.exp.toNat) else none

/-- `a ≤ b` on exact decimals. -/
def le (a b : Num) : Bool :=
  let e := min a.exp b.exp
  a.mant * 10 ^ (a.exp - e).toNat ≤ b.mant * 10 ^ (b.exp - e).toNat

end Num

/-- A JSON value. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Num)
  | str (s : String)
  | arr (xs : List Json)
  | obj (kvs : List (String × Json))
  deriving Repr, Inhabited

namespace Json

mutual
def decEq : (a b : Json) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool x, .bool y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .num x, .num y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .str x, .str y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .arr xs, .arr ys =>
    match decEqList xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .obj xs, .obj ys =>
    match decEqObj xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .null, .bool _ | .null, .num _ | .null, .str _ | .null, .arr _ | .null, .obj _
  | .bool _, .null | .bool _, .num _ | .bool _, .str _ | .bool _, .arr _ | .bool _, .obj _
  | .num _, .null | .num _, .bool _ | .num _, .str _ | .num _, .arr _ | .num _, .obj _
  | .str _, .null | .str _, .bool _ | .str _, .num _ | .str _, .arr _ | .str _, .obj _
  | .arr _, .null | .arr _, .bool _ | .arr _, .num _ | .arr _, .str _ | .arr _, .obj _
  | .obj _, .null | .obj _, .bool _ | .obj _, .num _ | .obj _, .str _ | .obj _, .arr _ =>
    isFalse (by intro e; cases e)
def decEqList : (a b : List Json) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | x :: xs, y :: ys =>
    match decEq x y, decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
def decEqObj : (a b : List (String × Json)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | (k, x) :: xs, (l, y) :: ys =>
    if hk : k = l then
      match decEq x y, decEqObj xs ys with
      | isTrue h1, isTrue h2 => isTrue (hk ▸ h1 ▸ h2 ▸ rfl)
      | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
      | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hk rfl)
end

instance : DecidableEq Json := decEq

/-! ### Construction and access -/

def nat (n : Nat) : Json := .num (Num.ofNat n)
def int (i : Int) : Json := .num (Num.ofInt i)
def strs (xs : List String) : Json := .arr (xs.map .str)

/-- Last member named `k` (browser `JSON.parse` semantics). -/
def lookup (kvs : List (String × Json)) (k : String) : Option Json :=
  kvs.foldl (fun acc p => if p.1 = k then some p.2 else acc) none

def get? (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => lookup kvs k
  | _ => none

def getStr? (j : Json) (k : String) : Option String :=
  match j.get? k with
  | some (.str s) => some s
  | _ => none

def isObj : Json → Bool
  | .obj _ => true
  | _ => false

/-- An object built from optional members; `none` members are omitted. -/
def mkObj (kvs : List (String × Option Json)) : Json :=
  .obj (kvs.filterMap fun p => p.2.map (p.1, ·))

/-- A NIP-5D envelope: `{"type": t, ...members}`. -/
def msg (t : String) (kvs : List (String × Option Json)) : Json :=
  mkObj (("type", some (.str t)) :: kvs)

/-! ### Canonical form -/

def insertKV (p : String × Json) : List (String × Json) → List (String × Json)
  | [] => [p]
  | q :: qs =>
    if p.1 = q.1 then p :: qs
    else if p.1 < q.1 then p :: q :: qs
    else q :: insertKV p qs

mutual
/-- Sort object members by name, keep the last of each name, recursively. -/
def canon : Json → Json
  | .arr xs => .arr (canonList xs)
  | .obj kvs => .obj (canonObj kvs [])
  | j => j
def canonList : List Json → List Json
  | [] => []
  | x :: xs => canon x :: canonList xs
def canonObj : List (String × Json) → List (String × Json) → List (String × Json)
  | [], acc => acc
  | (k, v) :: rest, acc => canonObj rest (insertKV (k, canon v) acc)
end

/-- Same message: equal canonical forms. -/
def same (a b : Json) : Bool := decide (canon a = canon b)

/-! ### Printing -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def escapeChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c = '\n' then ['\\', 'n']
  else if c = '\r' then ['\\', 'r']
  else if c = '\t' then ['\\', 't']
  else if c.toNat = 8 then ['\\', 'b']
  else if c.toNat = 12 then ['\\', 'f']
  else if c.toNat < 32 then
    ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

def renderStr (s : String) : String :=
  "\"" ++ String.ofList (s.toList.flatMap escapeChar) ++ "\""

def numRender (n : Num) : String :=
  if n.exp ≥ 0 then toString (n.mant * 10 ^ n.exp.toNat)
  else
    let digits := toString n.mant.natAbs
    let k := (-n.exp).toNat
    let padded := String.ofList (List.replicate (k + 1 - min (k + 1) digits.length) '0') ++ digits
    let ip := padded.take (padded.length - k)
    let fp := padded.drop (padded.length - k)
    (if n.mant < 0 then "-" else "") ++ ip.toString ++ "." ++ fp.toString

mutual
def render : Json → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .num n => numRender n
  | .str s => renderStr s
  | .arr xs => "[" ++ renderList xs ++ "]"
  | .obj kvs => "{" ++ renderObj kvs ++ "}"
def renderList : List Json → String
  | [] => ""
  | [x] => render x
  | x :: xs => render x ++ "," ++ renderList xs
def renderObj : List (String × Json) → String
  | [] => ""
  | [(k, v)] => renderStr k ++ ":" ++ render v
  | (k, v) :: kvs => renderStr k ++ ":" ++ render v ++ "," ++ renderObj kvs
end

instance : ToString Json := ⟨render⟩

/-! ### Parsing -/

def isWs (c : Char) : Bool := c = ' ' || c = '\n' || c = '\r' || c = '\t'

def skipWs : List Char → List Char
  | c :: cs => if isWs c then skipWs cs else c :: cs
  | [] => []

def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

def hex4? : List Char → Option (Nat × List Char)
  | a :: b :: c :: d :: rest => do
    let a ← hexVal? a; let b ← hexVal? b; let c ← hexVal? c; let d ← hexVal? d
    some (((a * 16 + b) * 16 + c) * 16 + d, rest)
  | _ => none

/-- Body of a string literal after the opening quote; `fuel` bounds the steps. -/
def parseStrBody : Nat → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | _ + 1, '"' :: rest, acc => some (String.ofList acc.reverse, rest)
  | fuel + 1, '\\' :: e :: rest, acc =>
    match e with
    | '"' => parseStrBody fuel rest ('"' :: acc)
    | '\\' => parseStrBody fuel rest ('\\' :: acc)
    | '/' => parseStrBody fuel rest ('/' :: acc)
    | 'b' => parseStrBody fuel rest (Char.ofNat 8 :: acc)
    | 'f' => parseStrBody fuel rest (Char.ofNat 12 :: acc)
    | 'n' => parseStrBody fuel rest ('\n' :: acc)
    | 'r' => parseStrBody fuel rest ('\r' :: acc)
    | 't' => parseStrBody fuel rest ('\t' :: acc)
    | 'u' =>
      match hex4? rest with
      | none => none
      | some (hi, rest') =>
        if 0xD800 ≤ hi ∧ hi < 0xDC00 then
          match rest' with
          | '\\' :: 'u' :: rest'' =>
            match hex4? rest'' with
            | some (lo, rest''') =>
              if 0xDC00 ≤ lo ∧ lo < 0xE000 then
                parseStrBody fuel rest''' (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) :: acc)
              else none
            | none => none
          | _ => none
        else if 0xDC00 ≤ hi ∧ hi < 0xE000 then none
        else parseStrBody fuel rest' (Char.ofNat hi :: acc)
    | _ => none
  | fuel + 1, c :: rest, acc => if c.toNat < 32 then none else parseStrBody fuel rest (c :: acc)

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def digitsVal (ds : List Char) : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

/-- RFC 8259 number. -/
def parseNum (cs : List Char) : Option (Num × List Char) :=
  let (neg, cs) := match cs with | '-' :: r => (true, r) | r => (false, r)
  let ip := cs.takeWhile isDigit
  let cs := cs.drop ip.length
  if ip.isEmpty || (ip.length > 1 && ip.head? = some '0') then none else
  let (fp, cs) := match cs with
    | '.' :: r => let f := r.takeWhile isDigit; (some f, r.drop f.length)
    | r => (none, r)
  if fp = some [] then none else
  let fd := fp.getD []
  let (ex, cs) : Option Int × List Char := match cs with
    | c :: r =>
      if c = 'e' || c = 'E' then
        let (eneg, r) := match r with | '-' :: r' => (true, r') | '+' :: r' => (false, r') | r' => (false, r')
        let ed := r.takeWhile isDigit
        if ed.isEmpty then (some 0, []) else
        (some (if eneg then -(digitsVal ed : Int) else digitsVal ed), r.drop ed.length)
      else (some 0, c :: r)
    | [] => (some 0, [])
  match ex with
  | none => none
  | some e =>
    -- an exponent marker with no digits leaves `cs = []` and is caught below
    let m : Int := digitsVal (ip ++ fd)
    some (Num.normalize ⟨if neg then -m else m, e - fd.length⟩, cs)

def parseLit (lit : List Char) (v : Json) (cs : List Char) : Option (Json × List Char) :=
  if cs.take lit.length = lit then some (v, cs.drop lit.length) else none

mutual
def parseValue : Nat → List Char → Option (Json × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match skipWs cs with
    | '{' :: rest => parseObj fuel (skipWs rest) []
    | '[' :: rest => parseArr fuel (skipWs rest) []
    | '"' :: rest => (parseStrBody (rest.length + 1) rest []).map fun (s, r) => (.str s, r)
    | 't' :: rest => parseLit "rue".toList (.bool true) rest
    | 'f' :: rest => parseLit "alse".toList (.bool false) rest
    | 'n' :: rest => parseLit "ull".toList .null rest
    | c :: rest => (parseNum (c :: rest)).map fun (n, r) => (.num n, r)
    | [] => none
def parseArr : Nat → List Char → List Json → Option (Json × List Char)
  | 0, _, _ => none
  | fuel + 1, cs, acc =>
    match cs, acc with
    | ']' :: rest, [] => some (.arr [], rest)
    | _, _ =>
      match parseValue fuel cs with
      | none => none
      | some (v, rest) =>
        match skipWs rest with
        | ',' :: rest' => parseArr fuel (skipWs rest') (v :: acc)
        | ']' :: rest' => some (.arr (v :: acc).reverse, rest')
        | _ => none
def parseObj : Nat → List Char → List (String × Json) → Option (Json × List Char)
  | 0, _, _ => none
  | fuel + 1, cs, acc =>
    match cs, acc with
    | '}' :: rest, [] => some (.obj [], rest)
    | '"' :: rest, _ =>
      match parseStrBody (rest.length + 1) rest [] with
      | none => none
      | some (k, rest) =>
        match skipWs rest with
        | ':' :: rest =>
          match parseValue fuel rest with
          | none => none
          | some (v, rest) =>
            match skipWs rest with
            | ',' :: rest' => parseObj fuel (skipWs rest') ((k, v) :: acc)
            | '}' :: rest' => some (.obj ((k, v) :: acc).reverse, rest')
            | _ => none
        | _ => none
    | _, _ => none
end

/-- Parse one complete JSON text. -/
def parse (s : String) : Option Json :=
  let cs := s.toList
  match parseValue (cs.length + 1) cs with
  | some (v, rest) => if skipWs rest = [] then some v else none
  | none => none

/-- Parse text that is known to be valid (test vectors); `null` otherwise. -/
def parse! (s : String) : Json := (parse s).getD .null

end Json

/-! ### Vectors -/

#guard Json.parse "{\"a\":1,\"b\":[true,null,\"x\"]}" ==
  some (.obj [("a", .nat 1), ("b", .arr [.bool true, .null, .str "x"])])
#guard (Json.parse "8.5").map Json.render == some "8.5"
#guard (Json.parse "21000").map Json.render == some "21000"
#guard (Json.parse "-0.25").map Json.render == some "-0.25"
#guard (Json.parse "1e3") == some (.nat 1000)
#guard (Json.parse "01") == none
#guard (Json.parse "1.") == none
#guard (Json.parse "\"\\u00e9\\ud83d\\ude00\"") == some (.str "é😀")
#guard (Json.parse "\"\\ud800\"") == none
#guard (Json.parse "[1,]") == none
#guard (Json.parse "{\"a\":1}x") == none
#guard (Json.parse " { } ") == some (.obj [])
#guard ((Json.parse "{\"k\":1,\"k\":2}").bind (·.get? "k")) == some (.nat 2)
#guard Json.same (Json.parse! "{\"a\":1,\"b\":2}") (Json.parse! "{\"b\":2,\"a\":1}")
#guard !Json.same (Json.parse! "{\"a\":1}") (Json.parse! "{\"a\":2}")
#guard Json.render (.str "a\"b\\c\nd") == "\"a\\\"b\\\\c\\nd\""
#guard Json.parse (Json.render (Json.parse! "{\"type\":\"x\",\"v\":[1,2.5,{\"q\":\"\\u0001\"}]}")) ==
  some (Json.parse! "{\"type\":\"x\",\"v\":[1,2.5,{\"q\":\"\\u0001\"}]}")

end Napplet
