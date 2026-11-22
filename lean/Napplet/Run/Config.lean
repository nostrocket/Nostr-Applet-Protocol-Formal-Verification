/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Config

/-!
# NAP-CONFIG runtime component

Upstream: `napplet/naps` PR #14, `naps/NAP-CONFIG.md` at `bed9cb5b`.

Wire (napplet → shell): `config.registerSchema {id, schema, version?}`, `config.get {id}`,
`config.subscribe {}`, `config.unsubscribe {}`, `config.openSettings {section?}`.
Wire (shell → napplet): `config.registerSchema.result {id, ok, code?, error?}`,
`config.values {id?, values}` (with `id` it answers `config.get`; without, it is a
subscription push), `config.schemaError {error, code}`.

The schema is decoded from JSON into `Schema`, which extends `NapConfig.Schema` with
everything the Core Subset admits: `number`, homogeneous arrays of primitives
(`items`, `minItems`, `maxItems`), `enum` on every primitive type and on arrays (whole
value), nested objects with `required` and their own `default` objects, a boolean or
schema-valued `additionalProperties` (undeclared members are never delivered), and the
annotations (`title`,
`description`, `format`, `enumDescriptions`, `x-napplet-secret`, `x-napplet-section`,
`x-napplet-order`, `deprecationMessage`, `markdownDescription`, `$schema`, `$version`).
Annotations are checked for type and otherwise passed to the host's settings UI in the
raw schema. Forbidden keywords map to `ref-not-allowed` (`$ref`, `$defs`,
`definitions`), `pattern-not-allowed` (`pattern`) and `invalid-schema` (combinators,
conditionals, `patternProperties`, `propertyNames`, `dependencies`,
`dependentSchemas`, `unevaluatedProperties`, tuple `items`, and any other keyword
outside the Core Subset other than `x-napplet-*`). A Core constraint on a type it does
not apply to (`minimum` on a string, `minItems` on an object, ...) must be well-typed and
is ignored, as in JSON Schema. A property with `x-napplet-secret: true` and a `default`
is `secret-with-default` whatever its type.

Values are JSON. Persisted values and the registered schema are keyed by the identity
scope (`NapStorage.scopeFor cx.storage .shared`: manifest key and artifact hash) and
outlive the endpoint; only subscriptions are per endpoint.

Malformed requests: `config.registerSchema` with a string `id` but no `schema`, or a
`version` that is not a non-negative integer, gets
`config.registerSchema.result {id, ok: false, code: "invalid-schema", error: "invalid request"}`
(the result envelope requires `ok` and `code`, so `errorReply` is not used); without a
string `id` nothing is sent. `config.get` without a string `id`, and
`config.openSettings` with a non-string `section`, are dropped.
-/

/-! ## Host operations

All in domain `config`.

* Effect `openSettings {window, section?, schema, values}`: open the shell's own settings
  UI for the napplet in `window` (a JSON number). `section` is present only when it is
  declared by some property's `x-napplet-section`; otherwise the UI opens at its default
  entry. `schema` is the registered schema JSON (render with the NAP-CONFIG SHOULDs:
  group by `x-napplet-section`, sort by `x-napplet-order` then key, show
  `deprecationMessage`, render `markdownDescription` as markdown and never as HTML,
  `format` only as a widget hint); `values` is the current delivered snapshot, absent if
  required properties are unresolved. The host SHOULD honour the request only when the
  napplet has (or would have) focus and SHOULD rate-limit it; it MUST mask
  `x-napplet-secret: true` fields, MUST NOT show a default for them, and SHOULD keep
  their values out of logs. Only sent when a schema is registered for the scope.
* Event `edited {window, values}`: the user committed the settings of the napplet in
  `window` (debounced, recommended ~100 ms). `values` is the full settings object (not a
  diff). The runtime drops undeclared members, persists the result for the napplet's
  scope if it yields a valid snapshot (otherwise the commit is ignored), and pushes
  `config.values` to every subscribed endpoint of that scope. The host validates input
  against the schema in its UI; this event is the only way values are ever written
  (the shell is the sole writer).

Persistence: `St.schemas` and `St.values` are persistent (keyed by scope); the host keeps
them across reloads. Secret values MAY be kept in a hardened store.
-/

namespace Napplet.Run.Config

open NapConfig (ErrCode)
open NapStorage (Scope scopeFor)

def codeName : ErrCode → String
  | .invalidSchema => "invalid-schema" | .versionConflict => "version-conflict"
  | .unsupportedDraft => "unsupported-draft" | .refNotAllowed => "ref-not-allowed"
  | .patternNotAllowed => "pattern-not-allowed" | .secretWithDefault => "secret-with-default"
  | .schemaTooDeep => "schema-too-deep" | .noSchema => "no-schema"

/-! ### JSON helpers -/

def optOf {α : Type} (o : Option Json) (f : Json → Option α) : Option (Option α) :=
  match o with
  | none => some none
  | some v => (f v).map some

theorem get_mkObj_cons (k k' : String) (o : Option Json) (rest : List (String × Option Json)) :
    (Json.mkObj ((k', o) :: rest)).get? k = ((Json.mkObj rest).get? k).or (if k' = k then o else none) := by
  cases o with
  | none => simp [Json.mkObj, Json.get?]
  | some v =>
    simp only [Json.mkObj, Json.get?, List.filterMap_cons, Option.map_some, Json.lookup]
    split <;> simp_all

theorem get_mkObj_nil (k : String) : (Json.mkObj []).get? k = none := rfl

@[simp] theorem optOf_str (o : Option String) : optOf (o.map .str) Json.asStr? = some o := by
  cases o <;> rfl
@[simp] theorem optOf_nat (o : Option Nat) : optOf (o.map Json.nat) Json.asNat? = some o := by
  cases o <;> simp [optOf]

/-! ### Requests -/

inductive Req where
  | registerSchema (id : String) (schema : Json) (version : Option Nat)
  | get (id : String)
  | subscribe
  | unsubscribe
  | openSettings (sect : Option String)
  deriving DecidableEq, Repr

def resultOk (id : String) : Json :=
  Json.msg "config.registerSchema.result" [("id", some (.str id)), ("ok", some (.bool true))]

def resultErr (id : String) (c : ErrCode) (error : String) : Json :=
  Json.msg "config.registerSchema.result"
    [("id", some (.str id)), ("ok", some (.bool false)), ("code", some (.str (codeName c))),
     ("error", some (.str error))]

def decode (j : Json) : Decoded Req :=
  match j.getStr? "type" with
  | some "config.registerSchema" =>
    match reqId? j with
    | none => .reject []
    | some id =>
      match j.get? "schema", optOf (j.get? "version") Json.asNat? with
      | some sc, some v => .ok (.registerSchema id sc v)
      | _, _ => .reject [resultErr id .invalidSchema "invalid request"]
  | some "config.get" =>
    match reqId? j with
    | some id => .ok (.get id)
    | none => .reject []
  | some "config.subscribe" => .ok .subscribe
  | some "config.unsubscribe" => .ok .unsubscribe
  | some "config.openSettings" =>
    match optOf (j.get? "section") Json.asStr? with
    | some sec => .ok (.openSettings sec)
    | none => .reject []
  | _ => .unknown

def encodeReq : Req → Json
  | .registerSchema id sc v => Json.msg "config.registerSchema"
      [("id", some (.str id)), ("schema", some sc), ("version", v.map Json.nat)]
  | .get id => Json.msg "config.get" [("id", some (.str id))]
  | .subscribe => Json.msg "config.subscribe" []
  | .unsubscribe => Json.msg "config.unsubscribe" []
  | .openSettings sec => Json.msg "config.openSettings" [("section", sec.map .str)]

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r <;> simp only [decode, encodeReq, reqId?, Json.getStr?, Json.msg, get_mkObj_cons,
    get_mkObj_nil] <;> simp

/-! ### Schemas -/

inductive Prim where
  | string | number | integer | boolean
  deriving DecidableEq, Repr

def primOf? : String → Option Prim
  | "string" => some .string | "number" => some .number | "integer" => some .integer
  | "boolean" => some .boolean | _ => none

/-- A primitive schema (a property, or the `items` of an array). -/
structure Leaf where
  ty : Prim
  enum : Option (List Json) := none
  minimum : Option Num := none
  maximum : Option Num := none
  minLength : Option Nat := none
  maxLength : Option Nat := none
  deriving DecidableEq, Repr

mutual
/-- A Core Subset schema node. `sect` is `x-napplet-section`. -/
inductive Schema where
  | leaf (l : Leaf) (dflt : Option Json) (secret : Bool) (sect : Option String)
  /-- A homogeneous array of primitives. `enum` lists the permitted whole array values
  (JSON Schema `enum` compares the instance as a whole). -/
  | arr (item : Leaf) (minItems maxItems : Option Nat) (enum : Option (List Json))
      (dflt : Option Json) (sect : Option String)
  | obj (props : Props) (required : List String) (dflt : Option Json) (sect : Option String)
inductive Props where
  | nil
  | cons (key : String) (s : Schema) (rest : Props)
end

def Props.ofList : List (String × Schema) → Props
  | [] => .nil
  | (k, s) :: r => .cons k s (Props.ofList r)

def Props.toList : Props → List (String × Schema)
  | .nil => []
  | .cons k s r => (k, s) :: r.toList

mutual
/-- Object nesting depth (as `NapConfig.Schema.depth`: a root with only primitive
properties has depth 1). -/
def Schema.depth : Schema → Nat
  | .obj ps _ _ _ => ps.depth + 1
  | _ => 0
def Props.depth : Props → Nat
  | .nil => 0
  | .cons _ s r => max s.depth r.depth
end

mutual
def Schema.secretDefault : Schema → Bool
  | .leaf _ (some _) true _ => true
  | .obj ps _ _ _ => ps.secretDefault
  | _ => false
def Props.secretDefault : Props → Bool
  | .nil => false
  | .cons _ s r => s.secretDefault || r.secretDefault
end

mutual
/-- Every `x-napplet-section` declared in the schema. -/
def Schema.sections : Schema → List String
  | .leaf _ _ _ sec | .arr _ _ _ _ _ sec => sec.toList
  | .obj ps _ _ sec => sec.toList ++ ps.sections
def Props.sections : Props → List String
  | .nil => []
  | .cons _ s r => s.sections ++ r.sections
end

/-! ### Validation -/

def Leaf.typeOk (ty : Prim) : Json → Bool
  | .str _ => ty == .string
  | .num n => ty == .number || (ty == .integer && decide (0 ≤ n.exp))
  | .bool _ => ty == .boolean
  | _ => false

/-- A primitive value against a leaf: type, `enum`, `minimum`/`maximum`,
`minLength`/`maxLength` (in Unicode code points, as JSON Schema counts). -/
def Leaf.ok (l : Leaf) (v : Json) : Bool :=
  Leaf.typeOk l.ty v && l.enum.all (·.contains v) &&
  match v with
  | .num n => l.minimum.all (Num.le · n) && l.maximum.all (Num.le n ·)
  | .str s => l.minLength.all (· ≤ s.length) && l.maxLength.all (s.length ≤ ·)
  | _ => true

def arrOk (it : Leaf) (mn mx : Option Nat) (en : Option (List Json)) : Json → Bool
  | .arr xs => mn.all (· ≤ xs.length) && mx.all (xs.length ≤ ·) && xs.all it.ok &&
      en.all (·.contains (.arr xs))
  | _ => false

def reqOk (req : List String) (kvs : List (String × Json)) : Bool :=
  req.all fun k => kvs.any (·.1 == k)

mutual
/-- Validity of a delivered value. Objects hold only declared, valid members and every
`required` member (undeclared members are never delivered, at any level). -/
def Schema.valid : Schema → Json → Bool
  | .leaf l _ _ _, v => l.ok v
  | .arr it mn mx en _ _, v => arrOk it mn mx en v
  | .obj ps req _ _, v =>
    match v with
    | .obj kvs => kvs.all (fun kv => ps.member kv.1 kv.2) && reqOk req kvs
    | _ => false
/-- Some declaration of `k` accepts `v`. -/
def Props.member : Props → String → Json → Bool
  | .nil, _, _ => false
  | .cons k s r, k', v => (k == k' && s.valid v) || r.member k' v
end

/-! ### Default resolution -/

def firstOk (ok : Json → Bool) : List Json → Option Json
  | [] => none
  | v :: vs => if ok v then some v else firstOk ok vs

mutual
/-- Resolve one property from its persisted value `p` and the values its ancestors'
`default` objects supply (`anc`, nearest first): a valid persisted value, else its own
valid `default`, else the first valid ancestor value, else nothing (NAP-CONFIG
§Default-resolution rule). A secret resolves only from a persisted value. An object
resolves member-wise and exists when some candidate object exists or a member resolved,
and all its `required` members resolved. -/
def Schema.resolve : Schema → Option Json → List Json → Option Json
  | .leaf l d sec _, p, anc =>
    if sec then p.filter l.ok else firstOk l.ok (p.toList ++ d.toList ++ anc)
  | .arr it mn mx en d _, p, anc => firstOk (arrOk it mn mx en) (p.toList ++ d.toList ++ anc)
  | .obj ps req d _, p, anc =>
    let kvs := ps.resolve p (d.toList ++ anc)
    if reqOk req kvs && (!kvs.isEmpty || (p.toList ++ d.toList ++ anc).any Json.isObj) then
      some (.obj kvs)
    else none
def Props.resolve : Props → Option Json → List Json → List (String × Json)
  | .nil, _, _ => []
  | .cons k s r, p, anc =>
    match s.resolve (p.bind (·.get? k)) (anc.filterMap (·.get? k)) with
    | some v => (k, v) :: r.resolve p anc
    | none => r.resolve p anc
end

/-- The delivered `values` object for a root schema `{properties, required, default}`
and the scope's persisted object. `none` when a required property is unresolved. -/
def rootValues (ps : Props) (req : List String) (d : Option Json) (p : Option Json) : Option Json :=
  let kvs := ps.resolve p d.toList
  if reqOk req kvs then some (.obj kvs) else none

mutual
/-- Drop persisted members the schema does not declare (orphans), at every level. -/
def Schema.prune : Schema → Json → Json
  | .obj ps _ _ _, .obj kvs => .obj (ps.prune (.obj kvs))
  | _, v => v
def Props.prune : Props → Json → List (String × Json)
  | .nil, _ => []
  | .cons k s r, v =>
    match v.get? k with
    | some x => (k, s.prune x) :: r.prune v
    | none => r.prune v
end


/-! ### Schema decoding -/

abbrev Err := ErrCode × String

def kwMsg (k : String) : String := "JSON Schema `" ++ k ++ "` keyword is not permitted in the Core Subset"

def invalid (m : String) : Err := (.invalidSchema, m)

def rootMsg : String := "schema root must be of type `object`"

def depthMsg : String := "schema nesting exceeds the depth limit (4)"

/-- Keywords of the Core Subset and the standardized annotations. -/
def allowedKeys : List String :=
  ["$schema", "$version", "type", "properties", "required", "items", "additionalProperties",
   "default", "title", "description", "enum", "enumDescriptions", "minimum", "maximum",
   "minLength", "maxLength", "minItems", "maxItems", "format", "deprecationMessage",
   "markdownDescription"]

/-- Explicit exclusions of NAP-CONFIG v1 (besides `$ref`/`$defs`/`definitions`/`pattern`). -/
def excludedKeys : List String :=
  ["oneOf", "anyOf", "allOf", "not", "if", "then", "else", "patternProperties", "propertyNames",
   "dependencies", "dependentSchemas", "unevaluatedProperties", "$dynamicRef"]

def keyError (k : String) : Option Err :=
  if k = "$ref" ∨ k = "$defs" ∨ k = "definitions" then some (.refNotAllowed, kwMsg k)
  else if k = "pattern" then some (.patternNotAllowed, kwMsg k)
  else if k ∈ excludedKeys then some (.invalidSchema, kwMsg k)
  else if k ∈ allowedKeys ∨ k.startsWith "x-napplet-" then none
  else some (invalid ("`" ++ k ++ "` is outside the NAP-CONFIG Core Subset"))

/-- `$schema` values accepted: draft-07, 2019-09 and 2020-12 meta-schemas. -/
def supportedDrafts : List String :=
  ["http://json-schema.org/draft-07/schema#", "http://json-schema.org/draft-07/schema",
   "https://json-schema.org/draft-07/schema#", "https://json-schema.org/draft-07/schema",
   "https://json-schema.org/draft/2019-09/schema", "https://json-schema.org/draft/2019-09/schema#",
   "https://json-schema.org/draft/2020-12/schema", "https://json-schema.org/draft/2020-12/schema#",
   "http://json-schema.org/draft/2019-09/schema", "http://json-schema.org/draft/2020-12/schema"]

def natField (j : Json) (k : String) : Except Err (Option Nat) :=
  match j.get? k with
  | none => .ok none
  | some v =>
    match v.asNat? with
    | some n => .ok (some n)
    | none => .error (invalid ("`" ++ k ++ "` must be a non-negative integer"))

def numField (j : Json) (k : String) : Except Err (Option Num) :=
  match j.get? k with
  | none => .ok none
  | some (.num n) => .ok (some n)
  | some _ => .error (invalid ("`" ++ k ++ "` must be a number"))

def absent (j : Json) (ks : List String) (what : String) : Except Err Unit :=
  match ks.find? fun k => (j.get? k).isSome with
  | some k => .error (invalid ("`" ++ k ++ "` does not apply to " ++ what))
  | none => .ok ()

/-- Annotation types (NAP-CONFIG Potentialities); unknown `x-napplet-*` keys are opaque. -/
def annotationsOk (j : Json) : Except Err Unit := do
  for k in ["title", "description", "format", "x-napplet-section", "deprecationMessage",
            "markdownDescription"] do
    match j.get? k with
    | none | some (.str _) => pure ()
    | some _ => throw (invalid ("`" ++ k ++ "` must be a string"))
  match j.get? "x-napplet-secret" with
  | none | some (.bool _) => pure ()
  | some _ => throw (invalid "`x-napplet-secret` must be a boolean")
  match j.get? "x-napplet-order" with
  | none => pure ()
  | some (.num n) => if n.mant < 0 then throw (invalid "`x-napplet-order` must be non-negative")
  | some _ => throw (invalid "`x-napplet-order` must be a number")
  match j.get? "enumDescriptions" with
  | none => pure ()
  | some v =>
    match v.asStrs?, j.get? "enum" with
    | some ds, some (.arr es) =>
      if ds.length ≠ es.length then throw (invalid "`enumDescriptions` must parallel `enum`")
    | _, _ => throw (invalid "`enumDescriptions` must parallel `enum`")

/-- The Core constraints must be well-typed wherever they appear, even on a type they do
not apply to (where they are then ignored). -/
def constraintsOk (j : Json) : Except Err Unit := do
  let _ ← numField j "minimum"
  let _ ← numField j "maximum"
  for k in ["minLength", "maxLength", "minItems", "maxItems"] do
    let _ ← natField j k
  pure ()

def leafOf (j : Json) (ty : Prim) : Except Err Leaf := do
  absent j ["items", "properties", "required", "additionalProperties"] "a primitive type"
  -- Core constraints that do not apply to `ty` are well-typed but ignored, as JSON Schema
  -- ignores them (NAP-CONFIG: `minimum`/`maximum` "apply to" numbers, `minLength`/
  -- `maxLength` to strings, `minItems`/`maxItems` to arrays).
  constraintsOk j
  let numeric := ty == .number || ty == .integer
  let minimum ← if numeric then numField j "minimum" else pure none
  let maximum ← if numeric then numField j "maximum" else pure none
  let minLength ← if ty == .string then natField j "minLength" else pure none
  let maxLength ← if ty == .string then natField j "maxLength" else pure none
  let enum ← match j.get? "enum" with
    | none => pure none
    | some (.arr es) =>
      if !es.isEmpty && es.all (Leaf.typeOk ty) then pure (some es)
      else throw (invalid "`enum` must be a non-empty array of values of the declared type")
    | some _ => throw (invalid "`enum` must be an array")
  pure { ty, enum, minimum, maximum, minLength, maxLength }

/-- Keep the last member of each name (browser `JSON.parse`). -/
def dedupLast : List (String × Json) → List (String × Json)
  | [] => []
  | (k, v) :: rest => if rest.any (·.1 == k) then dedupLast rest else (k, v) :: dedupLast rest

/-- Decode one schema node; `fuel` bounds nesting (running out is `schema-too-deep`). -/
def decodeNode : Nat → Bool → Json → Except Err Schema
  | 0, _, _ => .error (.schemaTooDeep, depthMsg)
  | fuel + 1, root, j => do
    let kvs ← match j with
      | .obj kvs => pure kvs
      | _ => throw (invalid "a schema must be an object")
    match kvs.findSome? fun kv => keyError kv.1 with
    | some e => throw e
    | none => pure ()
    if !root && ((j.get? "$schema").isSome || (j.get? "$version").isSome) then
      throw (invalid "`$schema` and `$version` are only valid at the schema root")
    annotationsOk j
    let secret := j.get? "x-napplet-secret" == some (.bool true)
    let dflt := j.get? "default"
    let sect := j.getStr? "x-napplet-section"
    -- NAP-CONFIG: a property with both `x-napplet-secret: true` and `default` is rejected
    -- with `secret-with-default`, whatever its type.
    if secret && dflt.isSome then
      throw (.secretWithDefault, "`x-napplet-secret` property declares a `default`")
    match j.getStr? "type" with
    | some "object" =>
      if secret then throw (invalid "`x-napplet-secret` applies only to strings")
      absent j ["items", "enum"] "type `object`"
      constraintsOk j
      let props ← match j.get? "properties" with
        | none => pure []
        | some (.obj pkvs) => pure (dedupLast pkvs)
        | some _ => throw (invalid "`properties` must be an object")
      -- A schema-valued `additionalProperties` must itself be a Core Subset schema. It is
      -- accepted, but undeclared members are never delivered (or persisted), at any level:
      -- dropping them keeps every delivered object valid under JSON Schema, which constrains
      -- only additional members that are present, and follows NAP-CONFIG's rule that
      -- settings "must not accrete unknown properties silently".
      match j.get? "additionalProperties" with
      | none | some (.bool _) => pure ()
      | some ap@(.obj _) => let _ ← decodeNode fuel false ap
      | some _ => throw (invalid "`additionalProperties` must be a boolean or a schema")
      let req ← match j.get? "required" with
        | none => pure []
        | some v =>
          match v.asStrs? with
          | some ks =>
            if ks.all (fun k => props.any (·.1 == k)) then pure ks
            else throw (invalid "`required` names an undeclared property")
          | none => throw (invalid "`required` must be an array of strings")
      let ps ← props.mapM fun kv => do
        let s ← decodeNode fuel false kv.2
        pure (kv.1, s)
      pure (.obj (Props.ofList ps) req dflt sect)
    | some "array" =>
      if secret then throw (invalid "`x-napplet-secret` applies only to strings")
      absent j ["properties", "required", "additionalProperties"] "type `array`"
      constraintsOk j
      let item ← match j.get? "items" with
        | some (.arr _) => throw (invalid "tuple-typed `items` are not in the Core Subset")
        | some it =>
          match ← decodeNode fuel false it with
          | .leaf l _ _ _ => pure l
          | _ => throw (invalid "arrays may contain primitives only")
        | none => throw (invalid "`items` must be one homogeneous schema")
      let mn ← natField j "minItems"
      let mx ← natField j "maxItems"
      let en ← match j.get? "enum" with
        | none => pure none
        | some (.arr es) =>
          if !es.isEmpty && es.all (fun e => match e with
              | .arr xs => xs.all (Leaf.typeOk item.ty) | _ => false) then pure (some es)
          else throw (invalid "`enum` must be a non-empty array of arrays of the item type")
        | some _ => throw (invalid "`enum` must be an array")
      pure (.arr item mn mx en dflt sect)
    | some t =>
      match primOf? t with
      | some ty =>
        if secret && ty != .string then throw (invalid "`x-napplet-secret` applies only to strings")
        let l ← leafOf j ty
        pure (.leaf l dflt secret sect)
      | none => throw (invalid ("unsupported type `" ++ t ++ "`"))
    | none => throw (invalid "a schema must declare one `type`")

/-- Whole-tree checks after decoding (NAP-CONFIG §Depth Limit, secret rule). -/
def checkTree (s : Schema) : Except Err Schema :=
  if s.depth > 4 then .error (.schemaTooDeep, depthMsg)
  else if s.secretDefault then .error (.secretWithDefault, "`x-napplet-secret` property declares a `default`")
  else .ok s

/-- An accepted registration. `raw` is the schema as the napplet sent it. -/
structure Reg where
  raw : Json
  props : Props
  required : List String
  dflt : Option Json
  sect : Option String
  version : Option Nat

def Reg.tree (r : Reg) : Schema := .obj r.props r.required r.dflt r.sect

/-- Root checks, in the order of the kehto reference validator: an object root of type
`object`, a supported `$schema`, an integer `$version`. -/
def rootCheck (j : Json) : Except Err (Option Nat) :=
  if !j.isObj || j.getStr? "type" != some "object" then .error (invalid rootMsg)
  else
    match j.get? "$schema" with
    | some (.str d) =>
      if d ∉ supportedDrafts then .error (.unsupportedDraft, "unsupported JSON Schema draft") else
      match j.get? "$version" with
      | none => .ok none
      | some v => match v.asNat? with
        | some n => .ok (some n)
        | none => .error (invalid "`$version` must be a non-negative integer")
    | some _ => .error (.unsupportedDraft, "unsupported JSON Schema draft")
    | none =>
      match j.get? "$version" with
      | none => .ok none
      | some v => match v.asNat? with
        | some n => .ok (some n)
        | none => .error (invalid "`$version` must be a non-negative integer")

/-- `config.registerSchema`: decode and check `schema`; `version` (or `$version`) must not
move backwards from the scope's current registration (`version-conflict`). -/
def register (j : Json) (version : Option Nat) (prior : Option Reg) : Except Err Reg :=
  match rootCheck j with
  | .error e => .error e
  | .ok sv =>
    let v := version.orElse fun _ => sv
    match decodeNode 6 true j with
    | .error e => .error e
    | .ok s =>
      match checkTree s with
      | .error e => .error e
      | .ok (.obj ps req d sec) =>
        match prior.bind (·.version), v with
        | some old, some new =>
          if new < old then .error (.versionConflict, "schema version cannot move backwards")
          else .ok ⟨j, ps, req, d, sec, v⟩
        | _, _ => .ok ⟨j, ps, req, d, sec, v⟩
      | .ok _ => .error (invalid rootMsg)

/-! ### Component -/

structure St where
  /-- Registered schema per identity scope (persistent). -/
  schemas : Scope → Option Reg
  /-- Persisted values per identity scope (persistent; written only from user edits and
  orphan removal). -/
  values : Scope → Option Json
  /-- Endpoints with a live `config.subscribe`. -/
  subs : List PortId
  /-- Scopes with a registered schema, in first-registration order. -/
  schemaKeys : List Scope := []
  /-- Scopes with persisted values, in first-write order. -/
  valueKeys : List Scope := []

def St.init : St := ⟨fun _ => none, fun _ => none, [], [], []⟩

def addKey (keys : List Scope) (sc : Scope) : List Scope :=
  if keys.contains sc then keys else keys ++ [sc]

/-- NAP-CONFIG §Identity Scope: publisher/kind/`d` (or event id) plus artifact hash. -/
def scopeOf (c : Ctx) : Scope := scopeFor c.storage .shared

def snapshot (reg : Reg) (p : Option Json) : Option Json := rootValues reg.props reg.required reg.dflt p

def valuesMsg (id : Option String) (v : Json) : Json :=
  Json.msg "config.values" [("id", id.map .str), ("values", some v)]

def schemaErrorMsg (c : ErrCode) (error : String) : Json :=
  Json.msg "config.schemaError" [("error", some (.str error)), ("code", some (.str (codeName c)))]

/-- The answer to `config.get` (with `id`) or the initial `config.subscribe` push. -/
def deliver (reg? : Option Reg) (p : Option Json) (id : Option String) : Json :=
  match reg? with
  | none => schemaErrorMsg .noSchema "no configuration schema is registered"
  | some reg =>
    match snapshot reg p with
    | some v => valuesMsg id v
    | none => schemaErrorMsg .invalidSchema "configuration requires valid values before delivery"

/-- `config.values` pushes to every subscribed endpoint of scope `sc`. -/
def push (w : World) (s : St) (sc : Scope) : List Eff :=
  match s.schemas sc with
  | none => []
  | some reg =>
    match snapshot reg (s.values sc) with
    | none => []
    | some v =>
      (w.live.filter fun c => s.subs.contains c.port && decide (scopeOf c = sc)).map fun c =>
        .send c.port (valuesMsg none v)

def pruneRoot (ps : Props) (v : Json) : Json := .obj (ps.prune v)

def handle (_h : Host) (w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .registerSchema id schema version =>
    let sc := scopeOf cx
    match register schema version (s.schemas sc) with
    | .error (c, m) =>
      -- NAP-CONFIG §API: "The shell pushes `config.schemaError` messages when it rejects a
      -- `registerSchema` call"; the correlated result carries the same code and error.
      (s, [.send cx.port (resultErr id c m), .send cx.port (schemaErrorMsg c m)])
    | .ok reg =>
      let s' := { s with schemas := upd s.schemas sc (some reg),
                         values := upd s.values sc ((s.values sc).map (pruneRoot reg.props)),
                         schemaKeys := addKey s.schemaKeys sc }
      (s', .send cx.port (resultOk id) :: push w s' sc)
  | .get id => (s, [.send cx.port (deliver (s.schemas (scopeOf cx)) (s.values (scopeOf cx)) (some id))])
  | .subscribe =>
    ({ s with subs := if s.subs.contains cx.port then s.subs else cx.port :: s.subs },
     [.send cx.port (deliver (s.schemas (scopeOf cx)) (s.values (scopeOf cx)) none)])
  | .unsubscribe => ({ s with subs := s.subs.filter (· != cx.port) }, [])
  | .openSettings sec =>
    match s.schemas (scopeOf cx) with
    | none => (s, [])
    | some reg =>
      (s, [.effect (.nap .config "openSettings" (Json.mkObj
        [("window", some (Json.nat cx.window)),
         ("section", (sec.filter fun x => reg.tree.sections.contains x).map .str),
         ("schema", some reg.raw), ("values", snapshot reg (s.values (scopeOf cx)))]))])

def onReply (_h : Host) (_w : World) (s : St) (_n : Nat) (_r : Reply) : St × List Eff := (s, [])

/-- A committed settings edit from the host. -/
def edited (w : World) (s : St) (args : Json) : St × List Eff :=
  match (args.get? "window").bind Json.asNat?, args.get? "values" with
  | some win, some v =>
    match w.live.find? (·.window == win) with
    | none => (s, [])
    | some c =>
      let sc := scopeOf c
      match s.schemas sc with
      | none => (s, [])
      | some reg =>
        let p := pruneRoot reg.props v
        match snapshot reg (some p) with
        | none => (s, [])
        | some _ =>
          let s' := { s with values := upd s.values sc (some p), valueKeys := addKey s.valueKeys sc }
          (s', push w s' sc)
  | _, _ => (s, [])

def onEvent (_h : Host) (w : World) (s : St) : HostEvent → St × List Eff
  | .nap .config "edited" args => edited w s args
  | _ => (s, [])

def drop (s : St) (p : PortId) : St × List Eff := ({ s with subs := s.subs.filter (· != p) }, [])

def mentions (s : St) (p : PortId) : Bool := s.subs.contains p


/-! ### Properties: values -/

theorem firstOk_ok {ok : Json → Bool} : ∀ {l : List Json} {v : Json}, firstOk ok l = some v → ok v = true
  | [], _, h => by simp [firstOk] at h
  | x :: xs, v, h => by
    simp only [firstOk] at h
    split at h
    · cases h; assumption
    · exact firstOk_ok h

mutual
/-- Every resolved value validates against its schema. -/
theorem Schema.resolve_valid : ∀ (s : Schema) (p : Option Json) (anc : List Json) (v : Json),
    s.resolve p anc = some v → s.valid v = true
  | .leaf l d sec _, p, anc, v, h => by
    simp only [Schema.resolve] at h
    simp only [Schema.valid]
    split at h
    · cases p with
      | none => simp at h
      | some x =>
        simp only [Option.filter] at h
        split at h
        · cases h; assumption
        · simp at h
    · exact firstOk_ok h
  | .arr it mn mx en d _, p, anc, v, h => by
    simp only [Schema.resolve] at h
    simp only [Schema.valid]
    exact firstOk_ok h
  | .obj ps req d _, p, anc, v, h => by
    simp only [Schema.resolve] at h
    split at h
    · rename_i hc
      cases h
      simp only [Schema.valid, Bool.and_eq_true, List.all_eq_true]
      simp only [Bool.and_eq_true] at hc
      exact ⟨fun kv hkv => Props.resolve_member ps p _ kv hkv, hc.1⟩
    · simp at h
/-- Every resolved member is a declared property whose schema accepts it. -/
theorem Props.resolve_member : ∀ (ps : Props) (p : Option Json) (anc : List Json) (kv : String × Json),
    kv ∈ ps.resolve p anc → ps.member kv.1 kv.2 = true
  | .nil, _, _, _, h => by simp [Props.resolve] at h
  | .cons k s r, p, anc, kv, h => by
    simp only [Props.resolve] at h
    split at h
    · rename_i v hv
      rcases List.mem_cons.mp h with rfl | h
      · simp [Props.member, Schema.resolve_valid s _ _ v hv]
      · simp [Props.member, Props.resolve_member r p anc kv h]
    · simp [Props.member, Props.resolve_member r p anc kv h]
end

/-- Only declared properties are delivered (top-level `additionalProperties` is false,
and orphaned persisted properties drop out). -/
theorem Props.resolve_declared : ∀ (ps : Props) (p : Option Json) (anc : List Json) (kv : String × Json),
    kv ∈ ps.resolve p anc → kv.1 ∈ ps.toList.map Prod.fst
  | .nil, _, _, _, h => by simp [Props.resolve] at h
  | .cons k s r, p, anc, kv, h => by
    simp only [Props.resolve] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · simp [Props.toList]
      · simp only [Props.toList, List.map_cons, List.mem_cons]
        exact .inr (Props.resolve_declared r p anc kv h)
    · simp only [Props.toList, List.map_cons, List.mem_cons]
      exact .inr (Props.resolve_declared r p anc kv h)

/-- A secret property that the user never set is never delivered, whatever the
defaults (NAP-CONFIG Tier 0: no default, not delivered until explicitly set). -/
theorem Props.secret_unset : ∀ (ps : Props) (p : Option Json) (anc : List Json) (k : String)
    (l : Leaf) (d : Option Json) (sect : Option String),
    (∀ s, (k, s) ∈ ps.toList → s = .leaf l d true sect) → p.bind (·.get? k) = none →
    ∀ v, (k, v) ∉ ps.resolve p anc
  | .nil, _, _, _, _, _, _, _, _, _, h => by simp [Props.resolve] at h
  | .cons k' s r, p, anc, k, l, d, sect, hs, hp, v, h => by
    simp only [Props.resolve] at h
    have ih := Props.secret_unset r p anc k l d sect
      (fun s' hs' => hs s' (by simp [Props.toList, hs'])) hp v
    split at h
    · rename_i v' hv'
      rcases List.mem_cons.mp h with he | h
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [hs s (by simp [Props.toList]), hp] at hv'
        simp [Schema.resolve] at hv'
      · exact ih h
    · exact ih h

/-- A valid persisted value wins over every default. -/
theorem default_resolution (l : Leaf) (d : Option Json) (sec : Bool) (sect : Option String)
    (anc : List Json) {x : Json} (hx : l.ok x = true) :
    (Schema.leaf l d sec sect).resolve (some x) anc = some x := by
  cases sec <;> simp [Schema.resolve, firstOk, Option.filter, hx]

/-- Without a persisted value, a property's own valid `default` comes before any
ancestor's value. -/
theorem own_default_first (l : Leaf) (dv : Json) (sect : Option String) (anc : List Json)
    (hd : l.ok dv = true) : (Schema.leaf l (some dv) false sect).resolve none anc = some dv := by
  simp [Schema.resolve, firstOk, hd]

theorem rootValues_valid {ps : Props} {req : List String} {d p : Option Json} {v : Json}
    (sect : Option String) (h : rootValues ps req d p = some v) : (Schema.obj ps req d sect).valid v = true := by
  simp only [rootValues] at h
  split at h
  · rename_i hc
    cases h
    simp only [Schema.valid, Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun kv hkv => Props.resolve_member ps p _ kv hkv, hc⟩
  · simp at h

/-- Every delivered snapshot validates against the registered schema. -/
theorem snapshot_valid {reg : Reg} {p : Option Json} {v : Json} (h : snapshot reg p = some v) :
    reg.tree.valid v = true := rootValues_valid _ h

/-- Every delivered snapshot holds only declared properties. -/
theorem snapshot_declared {reg : Reg} {p : Option Json} {v : Json} (h : snapshot reg p = some v) :
    ∃ kvs, v = .obj kvs ∧ ∀ kv ∈ kvs, kv.1 ∈ reg.props.toList.map Prod.fst := by
  simp only [snapshot, rootValues] at h
  split at h
  · cases h
    exact ⟨_, rfl, fun kv hkv => Props.resolve_declared _ _ _ kv hkv⟩
  · simp at h

theorem valuesMsg_ne_schemaError (id : Option String) (v : Json) (c : ErrCode) (e : String) :
    valuesMsg id v ≠ schemaErrorMsg c e := by
  cases id <;> simp [valuesMsg, schemaErrorMsg, Json.msg, Json.mkObj]

theorem valuesMsg_inj {id id' : Option String} {v v' : Json} (h : valuesMsg id v = valuesMsg id' v') :
    id = id' ∧ v = v' := by
  cases id <;> cases id' <;> simp_all [valuesMsg, Json.msg, Json.mkObj]

/-- A `config.values` answer carries the registered schema's snapshot, which is valid. -/
theorem deliver_values {reg? : Option Reg} {p : Option Json} {id id' : Option String} {v : Json}
    (h : deliver reg? p id = valuesMsg id' v) :
    ∃ reg, reg? = some reg ∧ snapshot reg p = some v ∧ id' = id ∧ reg.tree.valid v = true := by
  unfold deliver at h
  split at h
  · exact absurd h.symm (valuesMsg_ne_schemaError _ _ _ _)
  · rename_i reg
    split at h
    · rename_i v' hv'
      obtain ⟨rfl, rfl⟩ := valuesMsg_inj h
      exact ⟨reg, rfl, hv', rfl, snapshot_valid hv'⟩
    · exact absurd h.symm (valuesMsg_ne_schemaError _ _ _ _)

/-- Pushes go only to subscribed endpoints of the scope, with the scope's valid snapshot. -/
theorem push_spec {w : World} {s : St} {sc : Scope} {q : PortId} {m : Json}
    (h : Eff.send q m ∈ push w s sc) :
    ∃ reg v, s.schemas sc = some reg ∧ snapshot reg (s.values sc) = some v ∧
      m = valuesMsg none v ∧ reg.tree.valid v = true ∧
      ∃ c ∈ w.live, c.port = q ∧ q ∈ s.subs ∧ scopeOf c = sc := by
  unfold push at h
  split at h
  · simp at h
  · rename_i reg hreg
    split at h
    · simp at h
    · rename_i v hv
      simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, List.contains_iff_mem,
        decide_eq_true_eq, Eff.send.injEq] at h
      obtain ⟨c, ⟨hc, hsub, hsc⟩, rfl, rfl⟩ := h
      exact ⟨reg, v, hreg, hv, rfl, snapshot_valid hv, c, hc, rfl, hsub, hsc⟩

/-! ### Properties: registration -/

theorem checkTree_ok {s s' : Schema} (h : checkTree s = .ok s') :
    s' = s ∧ s.depth ≤ 4 ∧ s.secretDefault = false := by
  unfold checkTree at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h1 h2
      cases h
      exact ⟨rfl, by omega, by simpa using h2⟩

/-- An accepted schema is an object root in the Core Subset with depth at most 4 and no
secret with a default (`NapConfig.register_accepts_only_core`). -/
theorem register_accepts_only_core {j : Json} {v : Option Nat} {prior : Option Reg} {reg : Reg}
    (h : register j v prior = .ok reg) :
    reg.raw = j ∧ reg.tree.depth ≤ 4 ∧ reg.tree.secretDefault = false := by
  unfold register at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hct
        obtain ⟨rfl, hd, hs⟩ := checkTree_ok hct
        dsimp only at h
        split at h
        · split at h
          · simp at h
          · cases h; exact ⟨rfl, hd, hs⟩
        · cases h; exact ⟨rfl, hd, hs⟩
      · simp at h

/-! ### Properties: requests -/

/-- `config.get` and `config.subscribe` before any schema answer `no-schema`. -/
theorem no_schema_error (h : Host) (w : World) (cx : Ctx) (s : St) (hs : s.schemas (scopeOf cx) = none)
    (r : Req) (hr : r = .subscribe ∨ ∃ id, r = .get id) :
    (handle h w cx s r).2 = [.send cx.port (schemaErrorMsg .noSchema "no configuration schema is registered")] := by
  rcases hr with rfl | ⟨id, rfl⟩ <;> simp [handle, deliver, hs]

/-- Every `config.values` a request sends carries a valid snapshot of the requester's
own scope (`NapConfig.handle_values_valid`). -/
theorem handle_values_valid (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (id : Option String) (v : Json) (hm : Eff.send q (valuesMsg id v) ∈ (handle h w cx s r).2) :
    ∃ sc reg, (handle h w cx s r).1.schemas sc = some reg ∧ reg.tree.valid v = true ∧
      snapshot reg ((handle h w cx s r).1.values sc) = some v := by
  cases r with
  | registerSchema rid schema version =>
    simp only [handle] at hm ⊢
    split at hm
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Eff.send.injEq] at hm
      rcases hm with hm | hm
      · exact absurd hm.2 (by simp [valuesMsg, resultErr, Json.msg, Json.mkObj])
      · exact absurd hm.2 (by cases id <;> simp [valuesMsg, schemaErrorMsg, Json.msg, Json.mkObj])
    · rcases List.mem_cons.mp hm with hm | hm
      · simp only [Eff.send.injEq] at hm
        exact absurd hm.2 (by cases id <;> simp [valuesMsg, resultOk, Json.msg, Json.mkObj])
      · obtain ⟨reg, v', hreg, hv, he, hval, -⟩ := push_spec hm
        obtain ⟨-, rfl⟩ := valuesMsg_inj he
        exact ⟨_, reg, hreg, hval, hv⟩
  | get gid =>
    simp only [handle, List.mem_singleton, Eff.send.injEq] at hm ⊢
    obtain ⟨reg, hreg, hv, -, hval⟩ := deliver_values hm.2.symm
    exact ⟨_, reg, hreg, hval, hv⟩
  | subscribe =>
    simp only [handle, List.mem_singleton, Eff.send.injEq] at hm ⊢
    obtain ⟨reg, hreg, hv, -, hval⟩ := deliver_values hm.2.symm
    exact ⟨_, reg, hreg, hval, hv⟩
  | unsubscribe => simp [handle] at hm
  | openSettings sec =>
    simp only [handle] at hm
    split at hm <;> simp at hm

/-- A request touches persisted state only in the requester's own scope. -/
theorem handle_isolated (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) {sc : Scope}
    (hsc : sc ≠ scopeOf cx) :
    (handle h w cx s r).1.values sc = s.values sc ∧ (handle h w cx s r).1.schemas sc = s.schemas sc := by
  cases r with
  | registerSchema rid schema version =>
    simp only [handle]
    split
    · exact ⟨rfl, rfl⟩
    · simp [upd, hsc]
  | openSettings sec => simp only [handle]; split <;> exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

/-- The shell is the sole writer: no request writes a value. `config.registerSchema` may
only drop orphaned members (`pruneRoot`); every other request leaves values alone. -/
theorem sole_writer (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) :
    (handle h w cx s r).1.values = s.values ∨
      ∃ ps, (handle h w cx s r).1.values =
        upd s.values (scopeOf cx) ((s.values (scopeOf cx)).map (pruneRoot ps)) := by
  cases r with
  | registerSchema rid schema version =>
    simp only [handle]
    split
    · exact .inl rfl
    · exact .inr ⟨_, rfl⟩
  | openSettings sec => simp only [handle]; split <;> exact .inl rfl
  | _ => exact .inl rfl

/-! ### Properties: endpoint state -/

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := by
  simp [drop, mentions]

theorem drop_mentions (s : St) (p q : PortId) (h : mentions (drop s p).1 q = true) :
    mentions s q = true := by
  simp only [drop, mentions, List.contains_iff_mem, List.mem_filter] at h ⊢
  exact h.1

theorem handle_mentions (h : Host) (w : World) (cx : Ctx) (s : St) (r : Req) (q : PortId)
    (hcx : cx ∈ w.live) (hm : mentions (handle h w cx s r).1 q = true) :
    mentions s q = true ∨ w.bound q := by
  cases r with
  | registerSchema rid schema version =>
    simp only [handle] at hm
    split at hm
    · exact .inl hm
    · exact .inl hm
  | get => exact .inl hm
  | subscribe =>
    simp only [handle, mentions] at hm ⊢
    split at hm
    · exact .inl hm
    · simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hm
      rcases hm with rfl | hm
      · exact .inr ⟨cx, hcx, rfl⟩
      · exact .inl hm
  | unsubscribe =>
    simp only [handle, mentions, List.contains_iff_mem, List.mem_filter] at hm ⊢
    exact .inl hm.1
  | openSettings sec =>
    simp only [handle] at hm
    split at hm <;> exact .inl hm

theorem onReply_mentions (h : Host) (w : World) (s : St) (n : Nat) (rep : Reply) (q : PortId)
    (hm : mentions (onReply h w s n rep).1 q = true) : mentions s q = true ∨ w.bound q := .inl hm

theorem edited_subs (w : World) (s : St) (args : Json) : (edited w s args).1.subs = s.subs := by
  unfold edited
  split
  · split
    · rfl
    · dsimp only
      split
      · rfl
      · split <;> rfl
  · rfl

theorem onEvent_mentions (h : Host) (w : World) (s : St) (e : HostEvent) (q : PortId)
    (hm : mentions (onEvent h w s e).1 q = true) : mentions s q = true ∨ w.bound q := by
  apply Or.inl
  unfold onEvent at hm
  split at hm
  · simpa [mentions, edited_subs] using hm
  · exact hm


/-! ### Vectors (upstream examples) -/

def sampleHost : Host :=
  { crypto := ⟨fun _ => "", fun _ => true⟩, verifyEvent := fun _ => true,
    sniff := fun _ => "application/octet-stream", rasterize := fun _ => none,
    looksCiphertext := fun _ => false, encryptedWith := fun _ => none, transform := id }

def sampleCtx : Ctx :=
  { port := 5, window := 2, identity := { dTag := some "clock", artifactHash := "aa", publisher := "pk" },
    exposed := [.config], inst := 0 }

/-- Another napplet: same `d`, different publisher, so a different scope. -/
def otherCtx : Ctx :=
  { port := 6, window := 3, identity := { dTag := some "clock", artifactHash := "aa", publisher := "pk2" },
    exposed := [.config], inst := 0 }

def sampleWorld : World := { now := 0, live := [sampleCtx, otherCtx], user := "" }

def run (j : Json) (s : St := .init) (cx : Ctx := sampleCtx) : St × List Eff :=
  match decode j with
  | .ok r => handle sampleHost sampleWorld cx s r
  | .reject rs => (s, rs.map (.send cx.port))
  | .unknown => (s, [])

def edit (s : St) (args : String) : St × List Eff :=
  onEvent sampleHost sampleWorld s (.nap .config "edited" (Json.parse! args))

def sentTo (p : PortId) (es : List Eff) : List Json := es.filterMap fun e =>
  match e with
  | .send q m => if q = p then some m else none
  | _ => none

def one (es : List Eff) (expected : String) : Bool :=
  match sentTo 5 es with
  | [m] => Json.same m (Json.parse! expected)
  | _ => false

/-- A rejected registration: the correlated result, then the `config.schemaError` push
with the same code and error. -/
def two (es : List Eff) (expected : String) : Bool :=
  match sentTo 5 es with
  | [m, e] => Json.same m (Json.parse! expected) &&
      Json.same e (Json.msg "config.schemaError" [("error", m.get? "error"), ("code", m.get? "code")])
  | _ => false

def dec? (j : Json) : Option Req :=
  match decode j with
  | .ok r => some r
  | _ => none

def r1 := "{ \"type\": \"config.registerSchema\", \"id\": \"r1\", \"schema\": { \"$schema\": \"http://json-schema.org/draft-07/schema#\", \"type\": \"object\", \"properties\": { \"theme\": { \"type\": \"string\", \"enum\": [\"light\", \"dark\"], \"default\": \"dark\" } } }, \"version\": 1 }"
def r2 := "{ \"type\": \"config.registerSchema\", \"id\": \"r2\", \"schema\": { \"type\": \"object\", \"properties\": { \"username\": { \"type\": \"string\", \"pattern\": \"^[a-z]+$\" } } } }"

-- decode of every upstream request example
#guard dec? (Json.parse! r1) matches some (.registerSchema "r1" _ (some 1))
#guard dec? (Json.parse! r2) matches some (.registerSchema "r2" _ none)
#guard dec? (Json.parse! "{ \"type\": \"config.get\", \"id\": \"g1\" }") == some (.get "g1")
#guard dec? (Json.parse! "{ \"type\": \"config.subscribe\" }") == some .subscribe
#guard dec? (Json.parse! "{ \"type\": \"config.unsubscribe\" }") == some .unsubscribe
#guard dec? (Json.parse! "{ \"type\": \"config.openSettings\", \"section\": \"notifications\" }") == some (.openSettings (some "notifications"))
#guard decode (Json.parse! "{ \"type\": \"config.set\", \"id\": \"x\", \"values\": {} }") matches .unknown
#guard match decode (Json.parse! "{ \"type\": \"config.registerSchema\", \"id\": \"r9\", \"schema\": {}, \"version\": -1 }") with
  | .reject [m] => Json.same m (Json.parse! "{ \"type\": \"config.registerSchema.result\", \"id\": \"r9\", \"ok\": false, \"code\": \"invalid-schema\", \"error\": \"invalid request\" }")
  | _ => false
#guard decode (Json.parse! "{ \"type\": \"config.get\" }") matches .reject []

-- Register schema (success) and (rejection)
def reg1 := run (Json.parse! r1)
#guard one reg1.2 "{ \"type\": \"config.registerSchema.result\", \"id\": \"r1\", \"ok\": true }"
#guard two (run (Json.parse! r2)).2 "{ \"type\": \"config.registerSchema.result\", \"id\": \"r2\", \"ok\": false, \"code\": \"pattern-not-allowed\", \"error\": \"JSON Schema `pattern` keyword is not permitted in the Core Subset\" }"

-- Get values
#guard one (run (Json.parse! "{ \"type\": \"config.get\", \"id\": \"g1\" }") reg1.1).2
  "{ \"type\": \"config.values\", \"id\": \"g1\", \"values\": { \"theme\": \"dark\" } }"
-- Subscribe + initial snapshot
def subd := run (Json.parse! "{ \"type\": \"config.subscribe\" }") reg1.1
#guard one subd.2 "{ \"type\": \"config.values\", \"values\": { \"theme\": \"dark\" } }"
-- Push update after user changes a value
def light := edit subd.1 "{\"window\": 2, \"values\": {\"theme\": \"light\"}}"
#guard one light.2 "{ \"type\": \"config.values\", \"values\": { \"theme\": \"light\" } }"
-- an invalid edit (not in `enum`) falls back to the default
#guard one (edit subd.1 "{\"window\": 2, \"values\": {\"theme\": \"blue\", \"extra\": 1}}").2
  "{ \"type\": \"config.values\", \"values\": { \"theme\": \"dark\" } }"
-- Unsubscribe: no more pushes
def unsubd := run (Json.parse! "{ \"type\": \"config.unsubscribe\" }") light.1
#guard unsubd.2 == [] && (edit unsubd.1 "{\"window\": 2, \"values\": {\"theme\": \"dark\"}}").2 == []
-- The other napplet (same `d`, other publisher) sees no schema and no values
#guard match sentTo 6 (run (Json.parse! "{ \"type\": \"config.get\", \"id\": \"g2\" }") light.1 otherCtx).2 with
  | [m] => Json.same m (Json.parse! "{ \"type\": \"config.schemaError\", \"code\": \"no-schema\", \"error\": \"no configuration schema is registered\" }")
  | _ => false

-- Open settings with section deep-link (only a declared section is passed on)
#guard match (run (Json.parse! "{ \"type\": \"config.openSettings\", \"section\": \"notifications\" }") reg1.1).2 with
  | [.effect (.nap .config "openSettings" a)] => a.get? "section" == none && a.get? "window" == some (Json.nat 2)
  | _ => false
def withSection := run (Json.parse! "{ \"type\": \"config.registerSchema\", \"id\": \"r3\", \"schema\": { \"type\": \"object\", \"properties\": { \"alerts\": { \"type\": \"boolean\", \"default\": true, \"x-napplet-section\": \"notifications\" } } } }")
#guard match (run (Json.parse! "{ \"type\": \"config.openSettings\", \"section\": \"notifications\" }") withSection.1).2 with
  | [.effect (.nap .config "openSettings" a)] =>
    a.get? "section" == some (.str "notifications") && a.get? "values" == some (Json.parse! "{\"alerts\": true}")
  | _ => false

-- Schema errors
#guard two (run (Json.parse! "{ \"type\": \"config.registerSchema\", \"id\": \"e1\", \"schema\": { \"type\": \"string\" } }")).2
  "{ \"type\": \"config.registerSchema.result\", \"id\": \"e1\", \"ok\": false, \"code\": \"invalid-schema\", \"error\": \"schema root must be of type `object`\" }"
#guard one (run (Json.parse! "{ \"type\": \"config.get\", \"id\": \"g0\" }")).2
  "{ \"type\": \"config.schemaError\", \"code\": \"no-schema\", \"error\": \"no configuration schema is registered\" }"
def codeOf (es : List Eff) : Option String :=
  match sentTo 5 es with
  | m :: _ => m.getStr? "code"
  | _ => none
def regCode (schema : String) : Option String :=
  codeOf (run (Json.parse! ("{ \"type\": \"config.registerSchema\", \"id\": \"e\", \"schema\": " ++ schema ++ " }"))).2
#guard regCode "{ \"type\": \"object\", \"properties\": { \"a\": { \"$ref\": \"#/definitions/x\" } } }" == some "ref-not-allowed"
#guard regCode "{ \"type\": \"object\", \"definitions\": {} }" == some "ref-not-allowed"
#guard regCode "{ \"type\": \"object\", \"properties\": { \"a\": { \"oneOf\": [] } } }" == some "invalid-schema"
#guard regCode "{ \"type\": \"object\", \"properties\": { \"a\": { \"type\": \"array\", \"items\": [{ \"type\": \"string\" }] } } }" == some "invalid-schema"
#guard regCode "{ \"type\": \"object\", \"properties\": { \"t\": { \"type\": \"string\", \"x-napplet-secret\": true, \"default\": \"x\" } } }" == some "secret-with-default"
#guard regCode "{ \"$schema\": \"http://json-schema.org/draft-04/schema#\", \"type\": \"object\" }" == some "unsupported-draft"
#guard regCode "{ \"type\": \"object\", \"properties\": { \"a\": { \"type\": \"object\", \"properties\": { \"b\": { \"type\": \"object\", \"properties\": { \"c\": { \"type\": \"object\", \"properties\": { \"d\": { \"type\": \"object\" } } } } } } } } }" == some "schema-too-deep"
#guard regCode "{ \"type\": \"object\", \"properties\": { \"a\": { \"type\": \"object\", \"properties\": { \"b\": { \"type\": \"object\", \"properties\": { \"c\": { \"type\": \"object\" } } } } } } }" == none
#guard regCode "{ \"type\": \"object\", \"properties\": { \"n\": { \"type\": \"number\", \"multipleOf\": 2 } } }" == some "invalid-schema"
#guard regCode "{ \"type\": \"object\", \"properties\": { \"n\": { \"type\": \"number\", \"format\": \"x\", \"x-napplet-order\": 1, \"x-napplet-future\": {} } } }" == none
-- `version` may not move backwards
#guard codeOf (run (Json.parse! "{ \"type\": \"config.registerSchema\", \"id\": \"r0\", \"schema\": { \"type\": \"object\" }, \"version\": 0 }") reg1.1).2 == some "version-conflict"

-- A secret is delivered only once the user set it; ancestor defaults never supply it
def secretReg := run (Json.parse! "{ \"type\": \"config.registerSchema\", \"id\": \"s\", \"schema\": { \"type\": \"object\", \"default\": { \"token\": \"t0\" }, \"properties\": { \"token\": { \"type\": \"string\", \"x-napplet-secret\": true }, \"n\": { \"type\": \"integer\", \"minimum\": 1 } } } }")
def secretSub := run (Json.parse! "{ \"type\": \"config.subscribe\" }") secretReg.1
#guard one secretSub.2 "{ \"type\": \"config.values\", \"values\": {} }"
#guard one (edit secretSub.1 "{\"window\": 2, \"values\": {\"token\": \"abc\", \"n\": 0}}").2
  "{ \"type\": \"config.values\", \"values\": { \"token\": \"abc\" } }"

-- Nested objects, ancestor defaults, arrays and `required`
def nested := run (Json.parse! "{ \"type\": \"config.registerSchema\", \"id\": \"n\", \"schema\": { \"type\": \"object\", \"required\": [\"display\"], \"properties\": { \"display\": { \"type\": \"object\", \"default\": { \"size\": 12 }, \"properties\": { \"size\": { \"type\": \"integer\", \"maximum\": 40 }, \"font\": { \"type\": \"string\", \"default\": \"serif\" } } }, \"tags\": { \"type\": \"array\", \"items\": { \"type\": \"string\", \"maxLength\": 3 }, \"maxItems\": 2, \"default\": [\"a\"] } } } }")
#guard one (run (Json.parse! "{ \"type\": \"config.get\", \"id\": \"g\" }") nested.1).2
  "{ \"type\": \"config.values\", \"id\": \"g\", \"values\": { \"display\": { \"size\": 12, \"font\": \"serif\" }, \"tags\": [\"a\"] } }"
def nestedSub := run (Json.parse! "{ \"type\": \"config.subscribe\" }") nested.1
#guard one (edit nestedSub.1 "{\"window\": 2, \"values\": {\"display\": {\"size\": 50, \"font\": \"mono\"}, \"tags\": [\"x\", \"y\", \"z\"]}}").2
  "{ \"type\": \"config.values\", \"values\": { \"display\": { \"size\": 12, \"font\": \"mono\" }, \"tags\": [\"a\"] } }"

-- C2: a secret with a default is `secret-with-default` whatever its type
#guard regCode "{ \"type\": \"object\", \"properties\": { \"n\": { \"type\": \"integer\", \"x-napplet-secret\": true, \"default\": 1 } } }" == some "secret-with-default"
#guard regCode "{ \"type\": \"object\", \"properties\": { \"o\": { \"type\": \"object\", \"x-napplet-secret\": true, \"default\": {} } } }" == some "secret-with-default"
#guard regCode "{ \"type\": \"object\", \"properties\": { \"a\": { \"type\": \"array\", \"items\": { \"type\": \"string\" }, \"x-napplet-secret\": true, \"default\": [] } } }" == some "secret-with-default"
-- a non-string secret without a default is still `invalid-schema`
#guard regCode "{ \"type\": \"object\", \"properties\": { \"n\": { \"type\": \"integer\", \"x-napplet-secret\": true } } }" == some "invalid-schema"

-- C3: Core keywords on a type they do not apply to are ignored, not rejected
#guard regCode "{ \"type\": \"object\", \"minimum\": 0, \"properties\": { \"s\": { \"type\": \"string\", \"minimum\": 1, \"minItems\": 2 }, \"n\": { \"type\": \"integer\", \"maxLength\": 3 }, \"b\": { \"type\": \"boolean\", \"maximum\": 1 }, \"a\": { \"type\": \"array\", \"items\": { \"type\": \"number\" }, \"minLength\": 1 } } }" == none
-- ... but must still be well-typed
#guard regCode "{ \"type\": \"object\", \"properties\": { \"s\": { \"type\": \"string\", \"minimum\": \"x\" } } }" == some "invalid-schema"
-- an ignored constraint does not constrain: `minimum` on a string
def ignoredMin := run (Json.parse! "{ \"type\": \"config.registerSchema\", \"id\": \"m\", \"schema\": { \"type\": \"object\", \"properties\": { \"s\": { \"type\": \"string\", \"minimum\": 5, \"default\": \"x\" } } } }")
#guard one (run (Json.parse! "{ \"type\": \"config.get\", \"id\": \"g\" }") ignoredMin.1).2
  "{ \"type\": \"config.values\", \"id\": \"g\", \"values\": { \"s\": \"x\" } }"
-- `enum` on an array: whole-value comparison
def arrEnum := run (Json.parse! "{ \"type\": \"config.registerSchema\", \"id\": \"ae\", \"schema\": { \"type\": \"object\", \"properties\": { \"tags\": { \"type\": \"array\", \"items\": { \"type\": \"string\" }, \"enum\": [[\"a\"], [\"a\", \"b\"]], \"default\": [\"a\"] } } } }")
#guard one arrEnum.2 "{ \"type\": \"config.registerSchema.result\", \"id\": \"ae\", \"ok\": true }"
def arrEnumSub := run (Json.parse! "{ \"type\": \"config.subscribe\" }") arrEnum.1
#guard one (edit arrEnumSub.1 "{\"window\": 2, \"values\": {\"tags\": [\"b\"]}}").2
  "{ \"type\": \"config.values\", \"values\": { \"tags\": [\"a\"] } }"
#guard one (edit arrEnumSub.1 "{\"window\": 2, \"values\": {\"tags\": [\"a\", \"b\"]}}").2
  "{ \"type\": \"config.values\", \"values\": { \"tags\": [\"a\", \"b\"] } }"
#guard regCode "{ \"type\": \"object\", \"properties\": { \"t\": { \"type\": \"array\", \"items\": { \"type\": \"string\" }, \"enum\": [[1]] } } }" == some "invalid-schema"
-- schema-valued `additionalProperties`: accepted (and itself checked); undeclared members
-- are never delivered
def apSchema := run (Json.parse! "{ \"type\": \"config.registerSchema\", \"id\": \"ap\", \"schema\": { \"type\": \"object\", \"additionalProperties\": { \"type\": \"string\" }, \"properties\": { \"o\": { \"type\": \"object\", \"additionalProperties\": { \"type\": \"integer\" }, \"properties\": { \"k\": { \"type\": \"integer\", \"default\": 1 } } } } } }")
#guard one apSchema.2 "{ \"type\": \"config.registerSchema.result\", \"id\": \"ap\", \"ok\": true }"
def apSub := run (Json.parse! "{ \"type\": \"config.subscribe\" }") apSchema.1
#guard one (edit apSub.1 "{\"window\": 2, \"values\": {\"x\": \"y\", \"o\": {\"k\": 2, \"z\": 3}}}").2
  "{ \"type\": \"config.values\", \"values\": { \"o\": { \"k\": 2 } } }"
#guard regCode "{ \"type\": \"object\", \"additionalProperties\": { \"$ref\": \"#/x\" } }" == some "ref-not-allowed"
#guard regCode "{ \"type\": \"object\", \"additionalProperties\": 1 }" == some "invalid-schema"

-- Teardown drops the subscription only; values and schema stay with the scope
#guard mentions (drop subd.1 5).1 5 == false && ((drop subd.1 5).1.schemas (scopeOf sampleCtx)).isSome

end Napplet.Run.Config
