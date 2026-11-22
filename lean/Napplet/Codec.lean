/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Runtime

/-!
# JSON codecs for the runtime interface

The oracle (`napplet-oracle`) reads inputs and writes outputs as JSON, one value per
line. This file gives every type that crosses the runtime boundary an encoder
`enc… : α → Json` and a decoder `dec… : Json → Except String α`, and proves
`dec… (enc… a) = .ok a` for each (`@[simp]` lemmas `dec…_enc…`).

Formats:

* Records are objects with fixed member names. Optional members are omitted when absent.
* Inductive types are objects with a tag member `"t"` naming the constructor
  (`{"t": "create", "w": 1, ...}`).
* Bytes are standard base64 strings (RFC 4648, `Run.Resource.Base64`).
* Domains are their bare names (`"storage"`); call tags are `{"domain", "n"}`.
* NIP-01 events use NIP-01 member names (`created_at`).

The round trips are at the level of JSON values. Text round trips through
`Json.render` and `Json.parse` are checked on every trace by the oracle test.
-/

namespace Napplet.Codec

open _root_.Napplet.Runtime

abbrev Dec (α : Type) := Json → Except String α

@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl
@[simp] theorem pure_ok {ε α : Type} (a : α) : (pure a : Except ε α) = Except.ok a := rfl
@[simp] theorem map_ok {ε α β : Type} (a : α) (f : α → β) :
    (Except.ok a : Except ε α).map f = Except.ok (f a) := rfl

/-! ## Primitives -/

def field (j : Json) (k : String) : Except String Json :=
  match j.get? k with
  | some v => .ok v
  | none => .error ("missing member " ++ k)

def optField {α : Type} (j : Json) (k : String) (d : Dec α) : Except String (Option α) :=
  match j.get? k with
  | none => .ok none
  | some v => (d v).map some

def decStr : Dec String
  | .str s => .ok s
  | _ => .error "expected a string"

def decNat (j : Json) : Except String Nat :=
  match j.asNat? with
  | some n => .ok n
  | none => .error "expected a natural number"

def decBool : Dec Bool
  | .bool b => .ok b
  | _ => .error "expected a boolean"

def decJson : Dec Json := .ok

def decList {α : Type} (d : Dec α) : Dec (List α)
  | .arr xs => xs.mapM d
  | _ => .error "expected an array"

def encList {α : Type} (e : α → Json) (l : List α) : Json := .arr (l.map e)

/-- `null` for `none`. Only for types whose encoding is never `null`. -/
def decOpt {α : Type} (d : Dec α) : Dec (Option α)
  | .null => .ok none
  | j => (d j).map some

def encOpt {α : Type} (e : α → Json) : Option α → Json
  | none => .null
  | some a => e a

def encBytes (b : Bytes) : Json := .str (Run.Resource.Base64.encode b)

def decBytes : Dec Bytes
  | .str s =>
    match Run.Resource.Base64.decode? s with
    | some b => .ok b
    | none => .error "expected base64"
  | _ => .error "expected base64"

def encPair {α β : Type} (ea : α → Json) (eb : β → Json) (p : α × β) : Json := .arr [ea p.1, eb p.2]

def decPair {α β : Type} (da : Dec α) (db : Dec β) : Dec (α × β)
  | .arr [a, b] => do let x ← da a; let y ← db b; pure (x, y)
  | _ => .error "expected a pair"

@[simp] theorem decStr_str (s : String) : decStr (.str s) = .ok s := rfl
@[simp] theorem decBool_bool (b : Bool) : decBool (.bool b) = .ok b := rfl
@[simp] theorem decNat_nat (n : Nat) : decNat (Json.nat n) = .ok n := by simp [decNat]
@[simp] theorem decJson_eq (j : Json) : decJson j = .ok j := rfl
@[simp] theorem decBytes_enc (b : Bytes) : decBytes (encBytes b) = .ok b := by
  simp [decBytes, encBytes, Run.Resource.Base64.decode?_encode]

theorem decList_enc {α : Type} {d : Dec α} {e : α → Json} :
    ∀ (l : List α), (∀ x ∈ l, d (e x) = .ok x) → decList d (encList e l) = .ok l
  | [], _ => rfl
  | x :: l, h => by
    have hx := h x (by simp)
    have hl := decList_enc l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [decList, encList, List.map_cons, List.mapM_cons, hx] at hl ⊢
    rw [hl ] <;> try rfl

theorem decPair_enc {α β : Type} {da : Dec α} {db : Dec β} {ea : α → Json} {eb : β → Json}
    (p : α × β) (ha : da (ea p.1) = .ok p.1) (hb : db (eb p.2) = .ok p.2) :
    decPair da db (encPair ea eb p) = .ok p := by
  simp [decPair, encPair, ha, hb ] <;> try rfl

@[simp] theorem decList_str (l : List String) : decList decStr (encList .str l) = .ok l :=
  decList_enc l (fun _ _ => rfl)

@[simp] theorem decList_nat (l : List Nat) : decList decNat (encList Json.nat l) = .ok l :=
  decList_enc l (fun _ _ => decNat_nat _)

@[simp] theorem decList_strs (l : List (List String)) :
    decList (decList decStr) (encList (encList .str) l) = .ok l :=
  decList_enc l (fun _ _ => decList_str _)

/-! ## Domains, tags, identities -/

def decDomain (j : Json) : Except String Domain := do
  let s ← decStr j
  match Domain.ofName? s with
  | some d => pure d
  | none => .error ("unknown domain " ++ s)

def encDomain (d : Domain) : Json := .str d.name

@[simp] theorem decDomain_enc (d : Domain) : decDomain (encDomain d) = .ok d := by
  simp [decDomain, encDomain, Domain.ofName?_name ] <;> try rfl

@[simp] theorem decList_domain (l : List Domain) : decList decDomain (encList encDomain l) = .ok l :=
  decList_enc l (fun _ _ => decDomain_enc _)

def encTag (t : CallTag) : Json := .obj [("domain", encDomain t.domain), ("n", .nat t.n)]

def decTag (j : Json) : Except String CallTag := do
  let d ← field j "domain" >>= decDomain
  let n ← field j "n" >>= decNat
  pure ⟨d, n⟩

@[simp] theorem decTag_enc (t : CallTag) : decTag (encTag t) = .ok t := by
  simp [decTag, encTag, field, Json.get?, Json.lookup ] <;> try rfl

def encKind : ManifestKind → Json
  | .snapshot => .str "snapshot" | .root => .str "root" | .named => .str "named"

def decKind : Dec ManifestKind
  | .str "snapshot" => .ok .snapshot
  | .str "root" => .ok .root
  | .str "named" => .ok .named
  | _ => .error "expected a manifest kind"

@[simp] theorem decKind_enc (k : ManifestKind) : decKind (encKind k) = .ok k := by
  cases k <;> rfl

def encIdentity (i : Identity) : Json :=
  Json.mkObj [("d", i.dTag.map .str), ("hash", some (.str i.artifactHash)),
    ("publisher", some (.str i.publisher)), ("kind", some (encKind i.kind)),
    ("eventId", some (.str i.eventId))]

def decIdentity (j : Json) : Except String Identity := do
  let d ← optField j "d" decStr
  let h ← field j "hash" >>= decStr
  let p ← field j "publisher" >>= decStr
  let k ← field j "kind" >>= decKind
  let e ← field j "eventId" >>= decStr
  pure { dTag := d, artifactHash := h, publisher := p, kind := k, eventId := e }

@[simp] theorem decIdentity_enc (i : Identity) : decIdentity (encIdentity i) = .ok i := by
  obtain ⟨d, h, p, k, e⟩ := i
  cases d <;> simp [decIdentity, encIdentity, field, optField, Json.mkObj, Json.get?, Json.lookup] <;> try rfl

def encManifestError : ManifestError → Json
  | .badSignature => .obj [("t", .str "badSignature")]
  | .badKind => .obj [("t", .str "badKind")]
  | .xTagCount => .obj [("t", .str "xTagCount")]
  | .dTagCount => .obj [("t", .str "dTagCount")]
  | .emptyContent => .obj [("t", .str "emptyContent")]
  | .lineageOnNonSnapshot => .obj [("t", .str "lineageOnNonSnapshot")]
  | .hashMismatch => .obj [("t", .str "hashMismatch")]
  | .missingRequired n => .obj [("t", .str "missingRequired"), ("name", .str n)]

def decManifestError (j : Json) : Except String ManifestError := do
  let t ← field j "t" >>= decStr
  match t with
  | "badSignature" => pure .badSignature
  | "badKind" => pure .badKind
  | "xTagCount" => pure .xTagCount
  | "dTagCount" => pure .dTagCount
  | "emptyContent" => pure .emptyContent
  | "lineageOnNonSnapshot" => pure .lineageOnNonSnapshot
  | "hashMismatch" => pure .hashMismatch
  | "missingRequired" => do let n ← field j "name" >>= decStr; pure (.missingRequired n)
  | _ => .error ("unknown manifest error " ++ t)

@[simp] theorem decManifestError_enc (e : ManifestError) : decManifestError (encManifestError e) = .ok e := by
  cases e <;> simp [decManifestError, encManifestError, field, Json.get?, Json.lookup] <;> try rfl

/-! ## Events -/

def encManifestEvent (m : ManifestEvent) : Json :=
  .obj [("kind", .nat m.kind), ("pubkey", .str m.pubkey), ("content", .str m.content),
    ("tags", encList (fun t => encList .str (t.name :: t.values)) m.tags), ("id", .str m.id)]

def decTagM : Dec Tag
  | j => do
    let l ← decList decStr j
    match l with
    | n :: vs => pure ⟨n, vs⟩
    | [] => .error "empty tag"

def decManifestEvent (j : Json) : Except String ManifestEvent := do
  let k ← field j "kind" >>= decNat
  let p ← field j "pubkey" >>= decStr
  let c ← field j "content" >>= decStr
  let ts ← field j "tags" >>= decList decTagM
  let i ← field j "id" >>= decStr
  pure { kind := k, pubkey := p, content := c, tags := ts, id := i }

theorem decTagM_enc (t : Tag) : decTagM (encList .str (t.name :: t.values)) = .ok t := by
  simp only [decTagM, decList_str ] <;> try rfl

@[simp] theorem decManifestEvent_enc (m : ManifestEvent) : decManifestEvent (encManifestEvent m) = .ok m := by
  have := decList_enc (d := decTagM) (e := fun t => encList .str (t.name :: t.values)) m.tags
    (fun t _ => decTagM_enc t)
  simp [decManifestEvent, encManifestEvent, field, Json.get?, Json.lookup, this ] <;> try rfl

def encNostr (e : NostrEvent) : Json := e.toJson

def decNostr (j : Json) : Except String NostrEvent :=
  match NostrEvent.ofJson? j with
  | some e => .ok e
  | none => .error "expected a NIP-01 event"

@[simp] theorem decNostr_enc (e : NostrEvent) : decNostr (encNostr e) = .ok e := by
  simp [decNostr, encNostr]

def encUnsigned (e : UnsignedEvent) : Json := e.toJson

def decUnsigned (j : Json) : Except String UnsignedEvent := do
  let p ← field j "pubkey" >>= decStr
  let c ← field j "created_at" >>= decNat
  let k ← field j "kind" >>= decNat
  let ts ← match (← field j "tags").asTags? with
    | some ts => pure ts
    | none => .error "expected tags"
  let ct ← field j "content" >>= decStr
  pure { pubkey := p, createdAt := c, kind := k, tags := ts, content := ct }

@[simp] theorem decUnsigned_enc (e : UnsignedEvent) : decUnsigned (encUnsigned e) = .ok e := by
  simp [decUnsigned, encUnsigned, UnsignedEvent.toJson, field, Json.get?, Json.lookup ] <;> try rfl

/-! ## Host calls, replies, effects and events -/

def encEncryption (e : Encryption) : Json := .str e.name

def decEncryption (j : Json) : Except String Encryption := do
  let s ← decStr j
  match Encryption.ofName? s with
  | some e => pure e
  | none => .error "expected nip44 or nip04"

@[simp] theorem decEncryption_enc (e : Encryption) : decEncryption (encEncryption e) = .ok e := by
  cases e <;> rfl

def encCall : Call → Json
  | .sign ev => .obj [("t", .str "sign"), ("event", encUnsigned ev)]
  | .encrypt sc r p => .obj [("t", .str "encrypt"), ("scheme", encEncryption sc), ("recipient", .str r),
      ("plaintext", .str p)]
  | .decrypt sc ev => .obj [("t", .str "decrypt"), ("scheme", encEncryption sc), ("event", encNostr ev)]
  | .fetch u => .obj [("t", .str "fetch"), ("url", .str u)]
  | .prompt d k det => .obj [("t", .str "prompt"), ("domain", encDomain d), ("kind", .str k), ("details", det)]
  | .subscribe fs rs => Json.mkObj [("t", some (.str "subscribe")), ("filters", some (encList id fs)),
      ("relays", rs.map (encList .str))]
  | .publish ev rs => Json.mkObj [("t", some (.str "publish")), ("event", some (encNostr ev)),
      ("relays", rs.map (encList .str))]
  | .relayList p => .obj [("t", .str "relayList"), ("pubkey", .str p)]
  | .nap d op a => .obj [("t", .str "nap"), ("domain", encDomain d), ("op", .str op), ("args", a)]

def decCall (j : Json) : Except String Call := do
  let t ← field j "t" >>= decStr
  match t with
  | "sign" => do let e ← field j "event" >>= decUnsigned; pure (.sign e)
  | "encrypt" => do
    let sc ← field j "scheme" >>= decEncryption
    let r ← field j "recipient" >>= decStr
    let p ← field j "plaintext" >>= decStr
    pure (.encrypt sc r p)
  | "decrypt" => do
    let sc ← field j "scheme" >>= decEncryption
    let e ← field j "event" >>= decNostr
    pure (.decrypt sc e)
  | "fetch" => do let u ← field j "url" >>= decStr; pure (.fetch u)
  | "prompt" => do
    let d ← field j "domain" >>= decDomain
    let k ← field j "kind" >>= decStr
    let det ← field j "details"
    pure (.prompt d k det)
  | "subscribe" => do
    let fs ← field j "filters" >>= decList decJson
    let rs ← optField j "relays" (decList decStr)
    pure (.subscribe fs rs)
  | "publish" => do
    let e ← field j "event" >>= decNostr
    let rs ← optField j "relays" (decList decStr)
    pure (.publish e rs)
  | "relayList" => do let p ← field j "pubkey" >>= decStr; pure (.relayList p)
  | "nap" => do
    let d ← field j "domain" >>= decDomain
    let op ← field j "op" >>= decStr
    let a ← field j "args"
    pure (.nap d op a)
  | _ => .error ("unknown call " ++ t)

theorem decList_json (l : List Json) : decList decJson (encList id l) = .ok l :=
  decList_enc l (fun _ _ => rfl)

@[simp] theorem decCall_enc (c : Call) : decCall (encCall c) = .ok c := by
  cases c with
  | subscribe fs rs =>
    cases rs <;> simp [decCall, encCall, field, optField, Json.mkObj, Json.get?, Json.lookup,
      decList_json] <;> try rfl
  | publish ev rs =>
    cases rs <;> simp [decCall, encCall, field, optField, Json.mkObj, Json.get?, Json.lookup] <;> try rfl
  | _ => simp [decCall, encCall, field, Json.get?, Json.lookup] <;> try rfl

def encIp : NapResource.Ip → Json
  | .v4 a b c d => .obj [("v4", encList Json.nat [a, b, c, d])]
  | .v6 bs => .obj [("v6", encList Json.nat bs)]

def decIp (j : Json) : Except String NapResource.Ip :=
  match j.get? "v4", j.get? "v6" with
  | some v, _ => do
    let l ← decList decNat v
    match l with
    | [a, b, c, d] => pure (.v4 a b c d)
    | _ => .error "expected four octets"
  | none, some v => do let l ← decList decNat v; pure (.v6 l)
  | none, none => .error "expected an address"

@[simp] theorem decIp_enc (ip : NapResource.Ip) : decIp (encIp ip) = .ok ip := by
  cases ip <;> simp [decIp, encIp, Json.get?, Json.lookup] <;> try rfl

def encFetch (o : NapResource.FetchOutcome) : Json :=
  Json.mkObj [("hops", some (encList encIp o.hops)), ("body", o.body.map encBytes),
    ("timedOut", some (.bool o.timedOut)), ("upstreamType", some (.str o.upstreamType))]

def decFetch (j : Json) : Except String NapResource.FetchOutcome := do
  let hops ← field j "hops" >>= decList decIp
  let body ← optField j "body" decBytes
  let to ← field j "timedOut" >>= decBool
  let ut ← field j "upstreamType" >>= decStr
  pure { hops, body, timedOut := to, upstreamType := ut }

@[simp] theorem decFetch_enc (o : NapResource.FetchOutcome) : decFetch (encFetch o) = .ok o := by
  obtain ⟨hops, body, to, ut⟩ := o
  have := decList_enc (d := decIp) (e := encIp) hops (fun _ _ => decIp_enc _)
  cases body <;> simp [decFetch, encFetch, field, optField, Json.mkObj, Json.get?, Json.lookup, this] <;> try rfl

def encRelayEntry (r : RelayEntry) : Json :=
  .obj [("url", .str r.url), ("read", .bool r.read), ("write", .bool r.write)]

def decRelayEntry (j : Json) : Except String RelayEntry := do
  let u ← field j "url" >>= decStr
  let r ← field j "read" >>= decBool
  let w ← field j "write" >>= decBool
  pure ⟨u, r, w⟩

@[simp] theorem decRelayEntry_enc (r : RelayEntry) : decRelayEntry (encRelayEntry r) = .ok r := by
  simp [decRelayEntry, encRelayEntry, field, Json.get?, Json.lookup ] <;> try rfl

def encReply : Reply → Json
  | .signed e => Json.mkObj [("t", some (.str "signed")), ("event", e.map encNostr)]
  | .text s => Json.mkObj [("t", some (.str "text")), ("text", s.map .str)]
  | .fetched o => .obj [("t", .str "fetched"), ("outcome", encFetch o)]
  | .decision a c => Json.mkObj [("t", some (.str "decision")), ("allowed", some (.bool a)),
      ("choice", c.map .str)]
  | .event e r => .obj [("t", .str "event"), ("event", encNostr e), ("relay", .str r)]
  | .eose => .obj [("t", .str "eose")]
  | .closed r => Json.mkObj [("t", some (.str "closed")), ("reason", r.map .str)]
  | .published acks => .obj [("t", .str "published"),
      ("acks", encList (encPair .str .bool) acks)]
  | .relayList es => Json.mkObj [("t", some (.str "relayList")), ("entries", es.map (encList encRelayEntry))]
  | .json j => .obj [("t", .str "json"), ("json", j)]

def decReply (j : Json) : Except String Reply := do
  let t ← field j "t" >>= decStr
  match t with
  | "signed" => do let e ← optField j "event" decNostr; pure (.signed e)
  | "text" => do let s ← optField j "text" decStr; pure (.text s)
  | "fetched" => do let o ← field j "outcome" >>= decFetch; pure (.fetched o)
  | "decision" => do
    let a ← field j "allowed" >>= decBool
    let c ← optField j "choice" decStr
    pure (.decision a c)
  | "event" => do
    let e ← field j "event" >>= decNostr
    let r ← field j "relay" >>= decStr
    pure (.event e r)
  | "eose" => pure .eose
  | "closed" => do let r ← optField j "reason" decStr; pure (.closed r)
  | "published" => do
    let a ← field j "acks" >>= decList (decPair decStr decBool)
    pure (.published a)
  | "relayList" => do
    let es ← optField j "entries" (decList decRelayEntry)
    pure (.relayList es)
  | "json" => do let v ← field j "json"; pure (.json v)
  | _ => .error ("unknown reply " ++ t)

@[simp] theorem decReply_enc (r : Reply) : decReply (encReply r) = .ok r := by
  cases r with
  | signed e => cases e <;> simp [decReply, encReply, field, optField, Json.mkObj, Json.get?, Json.lookup] <;> try rfl
  | text s => cases s <;> simp [decReply, encReply, field, optField, Json.mkObj, Json.get?, Json.lookup] <;> try rfl
  | decision a c => cases c <;> simp [decReply, encReply, field, optField, Json.mkObj, Json.get?, Json.lookup] <;> try rfl
  | closed c => cases c <;> simp [decReply, encReply, field, optField, Json.mkObj, Json.get?, Json.lookup] <;> try rfl
  | published acks =>
    have := decList_enc (d := decPair decStr decBool) (e := encPair .str .bool) acks
      (fun p _ => decPair_enc p rfl rfl)
    simp [decReply, encReply, field, Json.get?, Json.lookup, this ] <;> try rfl
  | relayList es =>
    cases es with
    | none => simp [decReply, encReply, field, optField, Json.mkObj, Json.get?, Json.lookup ] <;> try rfl
    | some es =>
      have := decList_enc (d := decRelayEntry) (e := encRelayEntry) es (fun _ _ => decRelayEntry_enc _)
      simp [decReply, encReply, field, optField, Json.mkObj, Json.get?, Json.lookup, this ] <;> try rfl
  | _ => simp [decReply, encReply, field, Json.get?, Json.lookup] <;> try rfl

def encEffect : Effect → Json
  | .unsubscribe tag => .obj [("t", .str "unsubscribe"), ("tag", encTag tag)]
  | .cancel tag => .obj [("t", .str "cancel"), ("tag", encTag tag)]
  | .nap d op a => .obj [("t", .str "nap"), ("domain", encDomain d), ("op", .str op), ("args", a)]

def decEffect (j : Json) : Except String Effect := do
  let t ← field j "t" >>= decStr
  match t with
  | "unsubscribe" => do let g ← field j "tag" >>= decTag; pure (.unsubscribe g)
  | "cancel" => do let g ← field j "tag" >>= decTag; pure (.cancel g)
  | "nap" => do
    let d ← field j "domain" >>= decDomain
    let op ← field j "op" >>= decStr
    let a ← field j "args"
    pure (.nap d op a)
  | _ => .error ("unknown effect " ++ t)

@[simp] theorem decEffect_enc (e : Effect) : decEffect (encEffect e) = .ok e := by
  cases e <;> simp [decEffect, encEffect, field, Json.get?, Json.lookup] <;> try rfl

def encHostEvent : HostEvent → Json
  | .userChanged pk => .obj [("t", .str "userChanged"), ("pubkey", .str pk)]
  | .themeChanged th => Json.mkObj [("t", some (.str "themeChanged")), ("theme", th)]
  | .nap d ev a => .obj [("t", .str "nap"), ("domain", encDomain d), ("event", .str ev), ("args", a)]

def decHostEvent (j : Json) : Except String HostEvent := do
  let t ← field j "t" >>= decStr
  match t with
  | "userChanged" => do let p ← field j "pubkey" >>= decStr; pure (.userChanged p)
  | "themeChanged" => do let th ← optField j "theme" decJson; pure (.themeChanged th)
  | "nap" => do
    let d ← field j "domain" >>= decDomain
    let ev ← field j "event" >>= decStr
    let a ← field j "args"
    pure (.nap d ev a)
  | _ => .error ("unknown host event " ++ t)

@[simp] theorem decHostEvent_enc (e : HostEvent) : decHostEvent (encHostEvent e) = .ok e := by
  cases e with
  | themeChanged th =>
    cases th <;> simp [decHostEvent, encHostEvent, field, optField, Json.mkObj, Json.get?, Json.lookup] <;> try rfl
  | _ => simp [decHostEvent, encHostEvent, field, Json.get?, Json.lookup] <;> try rfl

/-! ## Inputs and outputs -/

def encInput : Runtime.Input → Json
  | .create w m b inst => .obj [("t", .str "create"), ("w", .nat w), ("manifest", encManifestEvent m),
      ("bytes", encBytes b), ("inst", .nat inst)]
  | .load w => .obj [("t", .str "load"), ("w", .nat w)]
  | .hello w ps => .obj [("t", .str "hello"), ("w", .nat w), ("ports", encList Json.nat ps)]
  | .windowMsg w => .obj [("t", .str "windowMsg"), ("w", .nat w)]
  | .portClosed p => .obj [("t", .str "portClosed"), ("port", .nat p)]
  | .grant p g => .obj [("t", .str "grant"), ("port", .nat p), ("grant", .str g)]
  | .message p m => .obj [("t", .str "message"), ("port", .nat p), ("msg", m)]
  | .reply tag r => .obj [("t", .str "reply"), ("tag", encTag tag), ("reply", encReply r)]
  | .event e => .obj [("t", .str "event"), ("event", encHostEvent e)]
  | .tick n => .obj [("t", .str "tick"), ("now", .nat n)]

def decInput (j : Json) : Except String Runtime.Input := do
  let t ← field j "t" >>= decStr
  match t with
  | "create" => do
    let w ← field j "w" >>= decNat
    let m ← field j "manifest" >>= decManifestEvent
    let b ← field j "bytes" >>= decBytes
    let i ← field j "inst" >>= decNat
    pure (.create w m b i)
  | "load" => do let w ← field j "w" >>= decNat; pure (.load w)
  | "hello" => do
    let w ← field j "w" >>= decNat
    let ps ← field j "ports" >>= decList decNat
    pure (.hello w ps)
  | "windowMsg" => do let w ← field j "w" >>= decNat; pure (.windowMsg w)
  | "portClosed" => do let p ← field j "port" >>= decNat; pure (.portClosed p)
  | "grant" => do
    let p ← field j "port" >>= decNat
    let g ← field j "grant" >>= decStr
    pure (.grant p g)
  | "message" => do
    let p ← field j "port" >>= decNat
    let m ← field j "msg"
    pure (.message p m)
  | "reply" => do
    let g ← field j "tag" >>= decTag
    let r ← field j "reply" >>= decReply
    pure (.reply g r)
  | "event" => do let e ← field j "event" >>= decHostEvent; pure (.event e)
  | "tick" => do let n ← field j "now" >>= decNat; pure (.tick n)
  | _ => .error ("unknown input " ++ t)

@[simp] theorem decInput_enc (i : Runtime.Input) : decInput (encInput i) = .ok i := by
  cases i <;> simp [decInput, encInput, field, Json.get?, Json.lookup] <;> try rfl

def encOutput : Runtime.Output → Json
  | .send p m => .obj [("t", .str "send"), ("port", .nat p), ("msg", m)]
  | .rejected w e => .obj [("t", .str "rejected"), ("w", .nat w), ("error", encManifestError e)]
  | .iframeCreated w id ex => .obj [("t", .str "iframeCreated"), ("w", .nat w),
      ("identity", encIdentity id), ("exposed", encList encDomain ex)]
  | .bound w p id => .obj [("t", .str "bound"), ("w", .nat w), ("port", .nat p),
      ("identity", encIdentity id)]
  | .closePort p => .obj [("t", .str "closePort"), ("port", .nat p)]
  | .removeFrame w => .obj [("t", .str "removeFrame"), ("w", .nat w)]
  | .call tag c => .obj [("t", .str "call"), ("tag", encTag tag), ("call", encCall c)]
  | .effect e => .obj [("t", .str "effect"), ("effect", encEffect e)]

def decOutput (j : Json) : Except String Runtime.Output := do
  let t ← field j "t" >>= decStr
  match t with
  | "send" => do
    let p ← field j "port" >>= decNat
    let m ← field j "msg"
    pure (.send p m)
  | "rejected" => do
    let w ← field j "w" >>= decNat
    let e ← field j "error" >>= decManifestError
    pure (.rejected w e)
  | "iframeCreated" => do
    let w ← field j "w" >>= decNat
    let id ← field j "identity" >>= decIdentity
    let ex ← field j "exposed" >>= decList decDomain
    pure (.iframeCreated w id ex)
  | "bound" => do
    let w ← field j "w" >>= decNat
    let p ← field j "port" >>= decNat
    let id ← field j "identity" >>= decIdentity
    pure (.bound w p id)
  | "closePort" => do let p ← field j "port" >>= decNat; pure (.closePort p)
  | "removeFrame" => do let w ← field j "w" >>= decNat; pure (.removeFrame w)
  | "call" => do
    let g ← field j "tag" >>= decTag
    let c ← field j "call" >>= decCall
    pure (.call g c)
  | "effect" => do let e ← field j "effect" >>= decEffect; pure (.effect e)
  | _ => .error ("unknown output " ++ t)

@[simp] theorem decOutput_enc (o : Runtime.Output) : decOutput (encOutput o) = .ok o := by
  cases o <;> simp [decOutput, encOutput, field, Json.get?, Json.lookup] <;> try rfl

end Napplet.Codec
