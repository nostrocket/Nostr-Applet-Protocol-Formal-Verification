/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Persist
import Napplet.Sha256
import Napplet.Test.Harness

/-!
# The oracle: configuration, host stand-ins and the trace loop

`napplet-oracle` (`OracleMain.lean`) reads newline-delimited JSON on standard input. The
first line is the session header; every later line is one `Runtime.Input`
(`Codec.encInput`). For each input it writes one line
`{"step": n, "outputs": [...]}` (`Codec.encOutput`), plus `"persisted"` when the header
asks for it. A line that does not decode gives `{"step": n, "error": "..."}` and changes
nothing. The oracle runs `Refine.step'` on the finite representation, so its memory
follows live state (`Refine.live_keys` and the other memory theorems).

## Header

```
{"config": {...}, "host": {...}, "restore": <Persisted>?, "emitPersisted": true?}
```

`restore` starts from `Persist.restore` (after `Persisted.check`) instead of `init'`.

## `config`: the finite form of `Runtime.Config`

Every member is optional and defaults to the model's default. Policy functions take these
finite forms (first matching rule wins, `"*"` matches anything):

* identity matcher `M`: `{"publisher"?, "d"?, "hash"?, "kind"?, "eventId"?, "catalogId"?}`;
  matches when every given member equals the identity's;
* `shell`: `{"supported": [domains], "strictRequired": bool, "policy": {"default": [domains],
  "rules": [{"match": M, "domains": [...]}]}, "undisclosed": same form}`; the policy
  defaults to every supported domain;
* `endpointName`: `[[window, name], ...]`; `inc.channelName`: `[[n, name], ...]`;
* identity predicates (`relay.canRead`, `relay.canWrite`, `outbox.canRead`,
  `outbox.canWrite`, `pow.canWrite`): `{"default": bool, "rules": [{"match": M, "allow": bool}]}`;
* `inc.subscribeAllowed` (catalog id, topic), `inc.openAllowed` (opener, target):
  `{"default": bool, "rules": [{"a": s, "b": s, "allow": bool}]}`;
* `cvm.acl` (catalog id, server, method): `{"default": bool, "rules": [{"napplet", "server",
  "method", "allow"}]}`;
* `display.permitted` (identity, display): `{"default": bool, "rules": [{"match": M,
  "display": s, "allow": bool}]}`;
* `value.maxAmount` (catalog id, rail): `{"default": n, "rules": [{"napplet", "rail", "max"}]}`;
* relay URL policies (`relay.scopedAllowed`, `outbox.allowed`): `{"allow": [urls],
  "deny": [urls]}` checked first, then `Net.relayAllowed`;
* `media.blockSource`: `{"blocked": [source JSON values]}`;
* `resource.mimeAllowed`: absent for `defaultMimeAllowed`, or `{"<scheme>": [mime essences]}`;
* `upload.policyFor`: `[{"key": manifest key, "policy": {"rails"?, "maxBytes"?, "mimeTypes"?}}]`;
* `notify.sanitize` is the identity.

## `host`: deterministic stand-ins for `Host`

* `"hash": "sha256"` (default) computes FIPS 180-4 SHA-256 in Lean (`Sha256.hash`);
  `"test"` uses the test harness's stand-in (`Test.fakeHash`), for replaying the model's
  own vectors.
* Signatures are not computed: the trace supplies them. `"verifySig"` and `"verifyEvent"`
  are `{"default": bool, "invalid": [event ids], "valid": [event ids]}` (default: valid).
* `"sniff": "magic"` (default) recognises PNG, JPEG, GIF, WebP and PDF by their leading
  bytes, otherwise `application/octet-stream`; `"test"` recognises PNG only.
* `rasterize` always fails (no SVG rasteriser); `transform` is the identity;
  `looksCiphertext` accepts NIP-04 shapes (`?iv=`); `"encryptedWith": {"nip04": [kinds],
  "nip44": [kinds]}` (default kind 4 is NIP-04); `"services": [names]`.
-/

namespace Napplet.Oracle

open _root_.Napplet.Runtime Codec

/-! ## Reading optional members -/

def opt {α : Type} (j : Json) (k : String) (d : Dec α) (dflt : α) : Except String α :=
  match j.get? k with
  | none => .ok dflt
  | some v => d v

def sub (j : Json) (k : String) : Json := (j.get? k).getD (.obj [])

/-- `"*"` or the value itself. -/
def pat (j : Json) (k : String) (v : String) : Bool :=
  match j.get? k with
  | none => true
  | some (.str "*") => true
  | some (.str s) => s == v
  | _ => false

def idMatch (m : Json) (id : Identity) : Bool :=
  (match m.getStr? "publisher" with | some p => p == id.publisher | none => true) &&
  (match m.getStr? "d" with | some d => id.dTag == some d | none => true) &&
  (match m.getStr? "hash" with | some h => h == id.artifactHash | none => true) &&
  (match m.get? "kind" with | some k => k == encKind id.kind | none => true) &&
  (match m.getStr? "eventId" with | some e => e == id.eventId | none => true) &&
  (match m.getStr? "catalogId" with | some c => c == id.catalogId | none => true)

def rules (j : Json) : List Json := ((j.get? "rules").bind Json.asArr?).getD []

def firstRule {α : Type} (j : Json) (ok : Json → Bool) (val : Json → Option α) (dflt : α) : α :=
  match (rules j).find? ok with
  | some r => (val r).getD dflt
  | none => dflt

def boolOf (j : Json) (k : String) (dflt : Bool) : Bool :=
  ((j.get? k).bind Json.asBool?).getD dflt

def idPred (j : Json) (dflt : Bool) : Identity → Bool := fun id =>
  firstRule j (fun r => idMatch (sub r "match") id) (fun r => (r.get? "allow").bind Json.asBool?)
    (boolOf j "default" dflt)

def domainsOf (j : Json) : Option (List Domain) :=
  match decList decDomain j with
  | .ok ds => some ds
  | .error _ => none

def idDomains (j : Json) (dflt : List Domain) : Identity → List Domain := fun id =>
  firstRule j (fun r => idMatch (sub r "match") id) (fun r => (r.get? "domains").bind domainsOf)
    (((j.get? "default").bind domainsOf).getD dflt)

def strPred2 (j : Json) (dflt : Bool) : String → String → Bool := fun a b =>
  firstRule j (fun r => pat r "a" a && pat r "b" b) (fun r => (r.get? "allow").bind Json.asBool?)
    (boolOf j "default" dflt)

def urlPolicy (j : Json) (base : String → Bool) : String → Bool := fun u =>
  if (((j.get? "deny").bind Json.asStrs?).getD []).contains u then false
  else if (((j.get? "allow").bind Json.asStrs?).getD []).contains u then true
  else base u

def natTable (j : Json) : Nat → Option String := fun n =>
  let rows := (j.asArr?).getD []
  rows.findSome? fun r => match r with
    | .arr [k, .str v] => if k.asNat? == some n then some v else none
    | _ => none

/-! ## Config -/

def schemeName : NapResource.Scheme → String
  | .https => "https" | .http => "http" | .data => "data" | .blossom => "blossom"
  | .hashtree => "hashtree" | .htree => "htree" | .nostr => "nostr"

def schemeOf? : String → Option NapResource.Scheme
  | "https" => some .https | "http" => some .http | "data" => some .data
  | "blossom" => some .blossom | "hashtree" => some .hashtree | "htree" => some .htree
  | "nostr" => some .nostr | _ => none

def displayType? : String → Option NapDisplay.DisplayType
  | "lcd" => some .lcd | "eink" => some .eink | "led-matrix" => some .ledMatrix
  | "other" => some .other | _ => none

def decDevice (j : Json) : Except String NapDisplay.DisplayDevice := do
  let id ← field j "id" >>= decStr
  let w ← field j "width" >>= decNat
  let h ← field j "height" >>= decNat
  let t ← field j "type" >>= decStr
  match displayType? t with
  | some ty => pure ⟨id, w, h, ty⟩
  | none => .error ("unknown display type " ++ t)

def decUploadRail (j : Json) : Except String NapUpload.Rail := do
  let s ← decStr j
  pure (match s with | "nip96" => .nip96 | "blossom" => .blossom | o => .other o)

def decRailCfg (j : Json) : Except String Run.Upload.RailCfg := do
  let r ← field j "rail" >>= decUploadRail
  let e ← opt j "enabled" decBool true
  let s ← optField j "server" decStr
  let rs ← opt j "returns" (decList decStr) []
  pure { rail := r, enabled := e, server := s, returns := rs }

def decNappletPolicy (j : Json) : Except String Run.Upload.NappletPolicy := do
  let r ← optField j "rails" (decList decUploadRail)
  let m ← optField j "maxBytes" decNat
  let t ← optField j "mimeTypes" (decList decStr)
  pure { rails := r, maxBytes := m, mimeTypes := t }

def decCombo (j : Json) : Except String NapKeys.Combo := do
  let k ← field j "key" >>= decStr
  pure { key := k, alt := boolOf j "alt" false, ctrl := boolOf j "ctrl" false,
         shift := boolOf j "shift" false, metaKey := boolOf j "meta" false }

def decAction (j : Json) : Except String NapMedia.Action := do
  let s ← decStr j
  match s with
  | "play" => pure .play | "pause" => pure .pause | "stop" => pure .stop | "next" => pure .next
  | "prev" => pure .prev | "seek" => pure .seek | "volume" => pure .volume
  | _ => .error ("unknown media action " ++ s)

def decAbsent (j : Json) : Except String Run.Intent.Absent := do
  let s ← decStr j
  match s with
  | "offerInstall" => pure .offerInstall | "notInstalled" => pure .notInstalled
  | "rejected" => pure .rejected | _ => .error ("unknown absent policy " ++ s)

def decConfig (j : Json) : Except String Config := do
  let sh := sub j "shell"
  let supported ← opt sh "supported" (decList decDomain) Test.allDomains
  let strict ← opt sh "strictRequired" decBool true
  let shellCfg : ShellConfig :=
    { supported, policy := idDomains (sub sh "policy") supported, strictRequired := strict,
      undisclosed := idDomains (sub sh "undisclosed") [] }
  let quota ← opt j "storageQuota" decNat NapStorage.defaultQuota
  let names := natTable (sub j "endpointName")
  -- INC
  let inc := sub j "inc"
  let incCfg : Run.Inc.Cfg :=
    { subscribeAllowed := strPred2 (sub inc "subscribeAllowed") true,
      openAllowed := strPred2 (sub inc "openAllowed") true,
      maxChannels := ((inc.get? "maxChannels").bind Json.asNat?).getD 32,
      channelName := natTable (sub inc "channelName") }
  -- INTENT
  let it := sub j "intent"
  let absent ← opt it "absent" decAbsent .notInstalled
  let intentCfg : Run.Intent.Cfg :=
    { hints := boolOf it "hints" true, confirmLaunch := boolOf it "confirmLaunch" true, absent }
  -- NOTIFY
  let no := sub j "notify"
  let controls ← opt no "controls" (decList decStr) ["toasts", "badges", "actions", "channels"]
  let notifyCfg : Run.Notify.Cfg :=
    { controls, requirePermission := boolOf no "requirePermission" true,
      rateWindow := ((no.get? "rateWindow").bind Json.asNat?).getD 60,
      rateMax := ((no.get? "rateMax").bind Json.asNat?).getD 30,
      urgentMax := ((no.get? "urgentMax").bind Json.asNat?).getD 3,
      badgeMax := ((no.get? "badgeMax").bind Json.asNat?).getD 9999 }
  -- DISPLAY
  let di := sub j "display"
  let devices ← opt di "devices" (decList decDevice) []
  let perm := sub di "permitted"
  let displayCfg : Run.Display.Cfg :=
    { devices,
      permitted := fun id d => firstRule perm (fun r => idMatch (sub r "match") id && pat r "display" d)
        (fun r => (r.get? "allow").bind Json.asBool?) (boolOf perm "default" false),
      maxBatch := ((di.get? "maxBatch").bind Json.asNat?).getD 4096 }
  -- KEYS
  let ke := sub j "keys"
  let reserved ← opt ke "browserReserved" (decList decCombo) Run.Keys.defaultBrowserReserved
  -- RELAY, OUTBOX
  let re := sub j "relay"
  let relayCfg : Run.Relay.Cfg :=
    { canRead := idPred (sub re "canRead") true, canWrite := idPred (sub re "canWrite") true,
      scopedAllowed := urlPolicy (sub re "scopedAllowed") Net.relayAllowed,
      relayHints := boolOf re "relayHints" true }
  let ob := sub j "outbox"
  let fallback ← opt ob "fallback" (decList decStr) []
  let outboxCfg : Run.Outbox.Cfg :=
    { canRead := idPred (sub ob "canRead") true, canWrite := idPred (sub ob "canWrite") true,
      allowed := urlPolicy (sub ob "allowed") Net.relayAllowed, fallback,
      relayHints := boolOf ob "relayHints" true }
  -- MEDIA
  let me := sub j "media"
  let forms ← opt me "sourceForms" (decList decStr) ["url", "blossomHash", "nostr"]
  let mctl ← opt me "controls" (decList decAction) Run.Media.allActions
  let blocked := (((sub me "blockSource").get? "blocked").bind Json.asArr?).getD []
  let mediaCfg : Run.Media.Cfg :=
    { maxSessions := ((me.get? "maxSessions").bind Json.asNat?).getD 16,
      shellPlayback := boolOf me "shellPlayback" true, autoplay := boolOf me "autoplay" true,
      sourceForms := forms, blockSource := fun s => blocked.contains s, controls := mctl }
  -- RESOURCE
  let rs := sub j "resource"
  let disabled ← opt rs "disabled" (decList decStr) []
  let mime := rs.get? "mimeAllowed"
  let resourceCfg : Run.Resource.Cfg :=
    { pol := { maxBytes := ((rs.get? "maxBytes").bind Json.asNat?).getD (10 * 1024 * 1024),
               maxRedirects := ((rs.get? "maxRedirects").bind Json.asNat?).getD 5,
               maxUrls := ((rs.get? "maxUrls").bind Json.asNat?).getD 100,
               httpEnabled := boolOf rs "httpEnabled" false,
               disabled := disabled.filterMap schemeOf? },
      quota := ((rs.get? "quota").bind Json.asNat?).getD (50 * 1024 * 1024),
      maxInFlight := ((rs.get? "maxInFlight").bind Json.asNat?).getD 10,
      timeoutSecs := ((rs.get? "timeoutSecs").bind Json.asNat?).getD 30,
      discloseInfo := boolOf rs "discloseInfo" true,
      discloseLimits := boolOf rs "discloseLimits" true,
      mimeAllowed := match mime with
        | none => Run.Resource.defaultMimeAllowed
        | some m => fun sc t =>
          (((m.get? (schemeName sc)).bind Json.asStrs?).getD []).contains (Run.Resource.mimeEssence t) }
  -- UPLOAD
  let up := sub j "upload"
  let rails ← opt up "rails" (decList decRailCfg) []
  let dr ← optField up "defaultRail" decUploadRail
  let mt ← optField up "mimeTypes" (decList decStr)
  let pols ← opt up "policyFor" (decList (fun e => do
      let k ← field e "key" >>= Persist.decKey
      let p ← field e "policy" >>= decNappletPolicy
      pure (k, p))) []
  let uploadCfg : Run.Upload.Cfg :=
    { rails, defaultRail := dr,
      maxBytes := ((up.get? "maxBytes").bind Json.asNat?).getD (100 * 1024 * 1024),
      mimeTypes := mt,
      syncMaxBytes := ((up.get? "syncMaxBytes").bind Json.asNat?).getD (1024 * 1024),
      maxActive := ((up.get? "maxActive").bind Json.asNat?).getD 4,
      authExpiry := ((up.get? "authExpiry").bind Json.asNat?).getD 300,
      discloseInfo := boolOf up "discloseInfo" true, nip94 := boolOf up "nip94" true,
      policyFor := fun k => (pols.find? (·.1 == k)).map (·.2) }
  -- LINK
  let li := sub j "link"
  let schemes ← opt li "allowedSchemes" (decList decStr) ["https", "http"]
  let lrules ← opt li "rules" (decList Persist.decRule) []
  let linkCfg : Run.Link.Cfg :=
    { allowedSchemes := schemes, rules := lrules, prompt := boolOf li "prompt" true,
      maxPrompts := ((li.get? "maxPrompts").bind Json.asNat?).getD 4 }
  -- VALUE
  let va := sub j "value"
  let vrails ← opt va "rails" (decList decStr) ["zap", "lnurl"]
  let rr ← opt va "receiptRelays" (decList decStr) []
  let val ← opt va "allowances" (decList Persist.decVA) []
  let ma := sub va "maxAmount"
  let valueCfg : Run.Value.Cfg :=
    { rails := vrails, receiptRelays := rr, disclosePreimage := boolOf va "disclosePreimage" false,
      allowances := val,
      maxAmount := fun n r => firstRule ma (fun x => pat x "napplet" n && pat x "rail" r)
        (fun x => (x.get? "max").bind Json.asNat?) (((ma.get? "default").bind Json.asNat?).getD 100000000) }
  -- CVM
  let cv := sub j "cvm"
  let kinds ← opt cv "kinds" (decList decNat) [11316, 11317, 11318, 11319, 11320]
  let cache ← opt cv "cache" (decList decStr) ["default", "reload", "no-store"]
  let cal ← opt cv "allowances" (decList Persist.decCA) []
  let acl := sub cv "acl"
  let cvmCfg : Run.Cvm.Cfg :=
    { maxTimeout := ((cv.get? "maxTimeout").bind Json.asNat?).getD NapCvm.maxTimeout, kinds,
      acl := fun n s m => firstRule acl (fun x => pat x "napplet" n && pat x "server" s && pat x "method" m)
        (fun x => (x.get? "allow").bind Json.asBool?) (boolOf acl "default" true),
      payments := boolOf cv "payments" false, registry := boolOf cv "registry" false, cache,
      allowances := cal }
  -- POW
  let pw := sub j "pow"
  let powCfg : Run.Pow.Cfg :=
    { maxTarget := ((pw.get? "maxTarget").bind Json.asNat?).getD 32,
      maxJobs := ((pw.get? "maxJobs").bind Json.asNat?).getD 32,
      maxConcurrent := ((pw.get? "maxConcurrent").bind Json.asNat?).getD 1,
      maxWorkers := ((pw.get? "maxWorkers").bind Json.asNat?).getD 4,
      publishConsent := boolOf pw "publishConsent" true,
      canWrite := idPred (sub pw "canWrite") true }
  pure { shell := shellCfg, storageQuota := quota, endpointName := names, incCfg, intentCfg,
         notifyCfg, displayCfg, keysCfg := { browserReserved := reserved }, relayCfg, outboxCfg,
         mediaCfg, resourceCfg, uploadCfg, linkCfg, valueCfg, cvmCfg, powCfg }

/-- The endpoint-name policy as a finite map (`RtState'.names`). -/
def decNames (j : Json) : FMap WindowId (Option String) :=
  let rows := ((sub j "endpointName").asArr?).getD []
  ⟨none, rows.filterMap fun r => match r with
    | .arr [k, .str v] => k.asNat?.map fun n => (n, some v)
    | _ => none⟩

/-! ## Host -/

def sniffMagic (b : Bytes) : String :=
  if b.take 8 = [0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a] then "image/png"
  else if b.take 4 = [0x89, 0x50, 0x4e, 0x47] then "image/png"
  else if b.take 3 = [0xff, 0xd8, 0xff] then "image/jpeg"
  else if b.take 4 = [0x47, 0x49, 0x46, 0x38] then "image/gif"
  else if b.take 4 = [0x52, 0x49, 0x46, 0x46] && (b.drop 8).take 4 = [0x57, 0x45, 0x42, 0x50] then "image/webp"
  else if b.take 5 = [0x25, 0x50, 0x44, 0x46, 0x2d] then "application/pdf"
  else "application/octet-stream"

def sigPred (j : Json) : String → Bool := fun id =>
  if (((j.get? "invalid").bind Json.asStrs?).getD []).contains id then false
  else if (((j.get? "valid").bind Json.asStrs?).getD []).contains id then true
  else boolOf j "default" true

def decHost (j : Json) : Except String Host := do
  let hash ← opt j "hash" decStr "sha256"
  let sha : Bytes → Hash ← match hash with
    | "sha256" => pure Sha256.hash
    | "test" => pure Test.fakeHash
    | _ => .error "host.hash must be \"sha256\" or \"test\""
  let sn ← opt j "sniff" decStr "magic"
  let sniff : Bytes → String ← match sn with
    | "magic" => pure sniffMagic
    | "test" => pure Test.testHost.sniff
    | _ => .error "host.sniff must be \"magic\" or \"test\""
  let vs := sub j "verifySig"
  let ve := sub j "verifyEvent"
  let enc := sub j "encryptedWith"
  let k04 := (((enc.get? "nip04").bind Json.asArr?).map (·.filterMap Json.asNat?)).getD [4]
  let k44 := (((enc.get? "nip44").bind Json.asArr?).map (·.filterMap Json.asNat?)).getD []
  let services ← opt j "services" (decList decStr) []
  pure { crypto := { sha256 := sha, verifySig := fun m => sigPred vs m.id },
         verifyEvent := fun e => sigPred ve e.id,
         sniff, rasterize := fun _ => none,
         looksCiphertext := Test.testHost.looksCiphertext,
         encryptedWith := fun e => if k04.contains e.kind then some .nip04
           else if k44.contains e.kind then some .nip44 else none,
         transform := id, services }

/-! ## Sessions -/

structure Session where
  host : Host
  cfg : Config
  state : Refine.RtState'
  emit : Bool
  step : Nat := 0

def decHeader (j : Json) : Except String Session := do
  let cfgJ := sub j "config"
  let cfg ← decConfig cfgJ
  let host ← decHost (sub j "host")
  let names := decNames cfgJ
  let st ← match j.get? "restore" with
    | none => pure (Refine.init' cfg names)
    | some pj => do
      let p ← Persist.decPersisted pj
      if p.check cfg then pure (Persist.restore cfg names p)
      else .error "restore: the persisted record fails Persisted.check"
  pure { host, cfg, state := st, emit := boolOf j "emitPersisted" false }

/-- One input line: the new session and the output line. -/
def feed (s : Session) (line : String) : Session × Json :=
  match Json.parse line with
  | none => ({ s with step := s.step + 1 }, Json.mkObj [("step", some (.nat s.step)), ("error", some (.str "invalid JSON"))])
  | some j =>
    match decInput j with
    | .error e => ({ s with step := s.step + 1 }, Json.mkObj [("step", some (.nat s.step)), ("error", some (.str e))])
    | .ok i =>
      let (st, outs) := Refine.step' s.host s.cfg s.state i
      let out := Json.mkObj [("step", some (.nat s.step)), ("outputs", some (encList encOutput outs)),
        ("persisted", if s.emit then some (Persist.encPersisted (Persist.persist st)) else none)]
      ({ s with state := st, step := s.step + 1 }, out)

/-- Run a whole trace text (header line, then inputs) to output text. Used by the trace
generator to produce expected outputs with the reference `Runtime.step` too. -/
def runText (lines : List String) : Except String (List String) := do
  match lines with
  | [] => .error "empty trace"
  | h :: rest =>
    let hj ← match Json.parse h with | some j => pure j | none => .error "header is not JSON"
    let s ← decHeader hj
    let (_, outs) := rest.foldl (fun (acc : Session × List String) l =>
      if l.all (fun c => c = ' ' || c = '\r' || c = '\t') then acc else
      let (s', o) := feed acc.1 l
      (s', acc.2 ++ [o.render])) (s, [])
    pure outs

end Napplet.Oracle
