/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Test.E2E
import Napplet.Oracle

/-!
# The end-to-end vectors as oracle traces

Each trace is a header (the oracle's finite configuration and host stand-ins) and the
inputs of one or more end-to-end vectors of `Test/E2E.lean`, in order. `napplet-tracegen`
writes `traces/<name>.in.ndjson` and, from the reference `Runtime.step`, the expected
`traces/<name>.out.ndjson`; CI runs `napplet-oracle` (which runs `Refine.step'`) on every
`.in` file and compares its output with the `.out` file byte for byte.

`e2eCfg` names the E2E configuration each header stands for. The generator checks that the
reference produces the same outputs under the decoded header as under that configuration,
so the traces replay the E2E vectors exactly.
-/

namespace Napplet.Test.Traces

open _root_.Napplet.Runtime

structure Trace where
  name : String
  header : String
  /-- The E2E configuration the header stands for, if the trace replays E2E vectors. -/
  e2eCfg : Option Config
  inputs : List Input

def testHeader : String :=
  "{\"config\":{\"display\":{\"devices\":[{\"id\":\"desk\",\"width\":800,\"height\":480,\"type\":\"eink\"}]," ++
  "\"permitted\":{\"default\":true}},\"upload\":{\"rails\":[{\"rail\":\"nip96\",\"server\":\"https://files.example.com/api/v2/media\",\"returns\":[\"https\"]}," ++
  "{\"rail\":\"blossom\",\"server\":\"https://blossom.example.com\",\"returns\":[\"https\",\"blossom\"]}],\"defaultRail\":\"nip96\"," ++
  "\"maxBytes\":104857600,\"mimeTypes\":[\"image/png\",\"image/jpeg\",\"application/pdf\"]}},\"host\":{\"hash\":\"test\",\"sniff\":\"test\"}}"

/-- `testHeader` with extra config members spliced in front. -/
def headerWith (extra : String) : String :=
  "{\"config\":{" ++ extra ++ "," ++ (testHeader.drop 11).toString

def tinyHeader : String := headerWith "\"storageQuota\":8"
def namedHeader : String :=
  headerWith "\"endpointName\":[[1,\"endpoint-music-controller\"],[2,\"endpoint-media-player\"]],\"inc\":{\"channelName\":[[0,\"c-abc\"]]}"
def regHeader : String := headerWith "\"cvm\":{\"registry\":true}"
def checkHeader : String :=
  headerWith "\"shell\":{\"policy\":{\"rules\":[{\"match\":{\"d\":\"chess\"},\"domains\":[\"theme\"]}]}}"

def boot (w : WindowId) (p : PortId) (d : String) : List Input :=
  bootInputs w p d (d.toList.map fun c => c.toNat.toUInt8)

def msg (p : PortId) (t : String) : Input := .message p (Json.parse! t)

/-- Outputs of the last input, by the reference machine under `cfg`. -/
def lastOuts (cfg : Config) (is : List Input) : List Runtime.Output :=
  match is.reverse with
  | [] => []
  | i :: pre => (Runtime.step testHost cfg (runAll testHost cfg (.init cfg) pre.reverse).1 i).2

def tagOf (os : List Runtime.Output) (dflt : CallTag) : CallTag :=
  ((calls os).head?.map (·.1)).getD dflt

def s1 : List Input := boot 1 7 "my-napplet"
def sU : List Input := s1 ++ [.event (.userChanged "def...")]
def sAB : List Input := boot 1 7 "social-feed" ++ boot 2 8 "profile-viewer"
def sCat : List Input := sAB ++
  [.event (.nap .intent "catalog" (Json.parse! catalogText)),
   .event (.nap .intent "default" (Json.parse! ("{\"archetype\":\"profile\",\"handler\":\"" ++ viewerId ++ "\"}")))]

def mk (name : String) (inputs : List Input) : Trace := ⟨name, testHeader, some testCfg, inputs⟩

def upload : List Input :=
  let p0 := sU ++ [msg 7 "{ \"type\": \"upload.upload\", \"id\": \"u1\", \"request\": { \"rail\": \"nip96\", \"data\": [137, 80, 78, 71], \"mimeType\": \"image/png\", \"filename\": \"photo.png\" } }"]
  let p1 := p0 ++ [.reply (tagOf (lastOuts testCfg p0) ⟨.upload, 999⟩) (.decision true none)]
  let p2 := match calls (lastOuts testCfg p1) with
    | [(t, .sign u)] => p1 ++ [.reply t (.signed (some (signAs u)))]
    | _ => p1
  match calls (lastOuts testCfg p2) with
  | [(t, _)] => p2 ++ [.reply t (.json (Json.parse!
      ("{\"ok\":true,\"url\":\"https://files.example.com/abc123.png\",\"sha256\":\"" ++ shaUp ++ "\",\"size\":4,\"mimeType\":\"image/png\"}")))]
  | _ => p2

def outbox : List Input :=
  let p := sU ++ [msg 7 "{ \"type\": \"outbox.publish\", \"id\": \"p2\", \"event\": { \"kind\": 1, \"content\": \"hi\", \"tags\": [] }, \"options\": { \"toOutbox\": false, \"relays\": [\"wss://relay.example.com\"] } }"]
  p ++ (calls (lastOuts testCfg p)).map (fun (t, _) => Input.reply t (.signed (some evO))) ++
    [.reply ⟨.outbox, 1⟩ (.published [("wss://relay.example.com", true)])]

def askAll : List Input :=
  let base := s1 ++ [.event (.userChanged "ab12cd..."), msg 7 "{ \"type\": \"identity.getPublicKey\", \"id\": \"q1\" }"]
  let qs : List (String × String) :=
    [("{ \"type\": \"identity.getProfile\", \"id\": \"q2\" }", "{ \"profile\": { \"name\": \"Alice\", \"about\": \"Nostr dev\", \"picture\": \"https://...\" } }"),
     ("{ \"type\": \"identity.getProfile\", \"id\": \"q3\" }", "{ \"profile\": null }"),
     ("{ \"type\": \"identity.getRelays\", \"id\": \"q5\" }", "{ \"relays\": { \"wss://relay.example.com\": { \"read\": true, \"write\": true }, \"wss://readonly.example.com\": { \"read\": true, \"write\": false } } }"),
     ("{ \"type\": \"identity.getList\", \"id\": \"q6\", \"listType\": \"bookmarks\" }", "{ \"entries\": [\"note1abc...\", \"note1def...\"] }"),
     ("{ \"type\": \"identity.getMutes\", \"id\": \"q7\" }", "{ \"pubkeys\": [\"spam1...\", \"spam2...\"] }"),
     ("{ \"type\": \"identity.getZaps\", \"id\": \"q8\" }", "{ \"zaps\": [{ \"eventId\": \"ev1...\", \"sender\": \"ab12...\", \"amount\": 21000, \"content\": \"Great post!\" }] }"),
     ("{ \"type\": \"identity.getBadges\", \"id\": \"q9\" }", "{ \"badges\": [{ \"id\": \"badge1...\", \"name\": \"Early Adopter\", \"awardedBy\": \"cd34...\" }] }")]
  let withQs := qs.foldl (fun acc (q, a) =>
    let p := acc ++ [msg 7 q]
    p ++ [.reply (tagOf (lastOuts testCfg p) ⟨.identity, 99⟩) (.json (Json.parse! a))]) base
  withQs ++ [.event (.userChanged "")]

def launch : List Input :=
  let p := sCat ++ [msg 7 ("{ \"type\": \"intent.launch\", \"id\": \"l1\", \"target\": { \"address\": \"35129:" ++ publisher ++ ":profile-viewer\" } }")]
  p ++ [.reply (tagOf (lastOuts testCfg p) ⟨.intent, 999⟩) (.decision true none)]

def valueSend : List Input :=
  let p := sU ++ [msg 7 ("{ \"type\": \"value.send\", \"id\": \"s2\", \"request\": " ++ valueReq ++ " }")]
  p ++ [.reply (tagOf (lastOuts testCfg p) ⟨.value, 999⟩) (.decision false none)]

def registry : List Input :=
  let p := (bootInputs 1 7 "my-napplet" [109]) ++
    [msg 7 "{ \"type\": \"cvm.registry.describe\", \"id\": \"s1\", \"selector\": { \"family\": \"relatr\" } }"]
  match calls (lastOuts regCfg p) with
  | [_, (t, _)] => p ++ [.reply t (.json (Json.parse! "{\"entry\": { \"family\": \"relatr\", \"schemaHashes\": [\"a7f3d9...\"], \"selected\": { \"pubkey\": \"65a334...\", \"relays\": [\"wss://relay.example.com\"] }, \"tools\": [ { \"name\": \"search_profiles\", \"schemaHash\": \"a7f3d9...\", \"inputSchema\": { \"type\": \"object\", \"properties\": { \"q\": { \"type\": \"string\" } }, \"required\": [\"q\"] } } ] }}"))]
  | _ => p

def all : List Trace := [
  mk "nip5d" (s1 ++ [msg 8 "{ \"type\": \"storage.get\", \"id\": \"a1\", \"key\": \"theme\" }",
    msg 7 "{ \"type\": \"storage.clear\", \"id\": \"x\" }", msg 7 "{ \"type\": \"nosuch.thing\", \"id\": \"x\" }",
    .hello 1 [9]]),
  mk "shell" (s1 ++ [msg 7 "{ \"type\": \"shell.ready\" }", msg 7 "{ \"type\": \"shell.ready\" }",
    msg 7 "{ \"type\": \"shell.check\", \"id\": \"c3\", \"manifest\": { \"kind\": 1 } }"]),
  mk "storage" (s1 ++ [msg 7 "{ \"type\": \"storage.get\", \"id\": \"a2\", \"key\": \"missing-key\" }",
    msg 7 "{ \"type\": \"storage.set\", \"id\": \"b2\", \"key\": \"theme\", \"value\": \"light\" }",
    msg 7 "{ \"type\": \"storage.get\", \"id\": \"a1\", \"key\": \"theme\" }",
    msg 7 "{ \"type\": \"storage.keys\", \"id\": \"d4\" }",
    msg 7 "{ \"type\": \"storage.get\", \"id\": \"a3\", \"key\": \"theme\", \"scope\": \"instance\" }"] ++
    bootInputs 2 8 "other" [1, 2, 3] ++
    [msg 8 "{ \"type\": \"storage.get\", \"id\": \"a1\", \"key\": \"theme\" }",
     msg 7 "{ \"type\": \"storage.remove\", \"id\": \"c3\", \"key\": \"theme\" }",
     msg 7 "{ \"type\": \"storage.set\", \"id\": \"b9\", \"key\": \"theme\" }"]),
  mk "storage-examples" (s1 ++ [msg 7 "{ \"type\": \"storage.set\", \"id\": \"b1\", \"key\": \"theme\", \"value\": \"dark\" }",
    msg 7 "{ \"type\": \"storage.get\", \"id\": \"a1\", \"key\": \"theme\" }",
    msg 7 "{ \"type\": \"storage.set\", \"id\": \"b3\", \"key\": \"language\", \"value\": \"en\" }",
    msg 7 "{ \"type\": \"storage.keys\", \"id\": \"d4\" }"]),
  ⟨"storage-quota", tinyHeader, some tinyCfg, bootInputs 1 7 "my-napplet" [1] ++
    [msg 7 "{ \"type\": \"storage.set\", \"id\": \"b2\", \"key\": \"theme\", \"value\": \"light\" }"]⟩,
  mk "theme" (s1 ++ [msg 7 "{ \"type\": \"theme.get\", \"id\": \"t1\" }",
    .event (.themeChanged (some (Json.parse! themeText))), msg 7 "{ \"type\": \"theme.get\", \"id\": \"t2\" }"]),
  mk "theme-full" (s1 ++ [.event (.themeChanged (some (Json.parse! themeFull))),
    msg 7 "{ \"type\": \"theme.get\", \"id\": \"t1\" }", .event (.themeChanged (some (Json.parse! ghDark)))]),
  mk "identity" (s1 ++ [msg 7 "{ \"type\": \"identity.getPublicKey\", \"id\": \"q1b\" }",
    .event (.userChanged "ab12cd"), msg 7 "{ \"type\": \"identity.getPublicKey\", \"id\": \"q1\" }",
    msg 7 "{ \"type\": \"identity.getFollows\", \"id\": \"q4\" }",
    .reply ⟨.identity, 0⟩ (.json (Json.parse! "{ \"pubkeys\": [\"ab12...\", \"cd34...\", \"ef56...\"] }"))]),
  mk "identity-teardown" (s1 ++ [.event (.userChanged "ab12cd"),
    msg 7 "{ \"type\": \"identity.getFollows\", \"id\": \"q4\" }", .portClosed 7,
    .reply ⟨.identity, 0⟩ (.json (Json.parse! "{ \"pubkeys\": [] }"))]),
  mk "identity-examples" askAll,
  mk "inc" (sAB ++ [msg 7 "{ \"type\": \"inc.channel.open\", \"id\": \"ch1\", \"target\": \"endpoint-media-player\" }",
    msg 8 "{ \"type\": \"inc.subscribe\", \"id\": \"a1\", \"topic\": \"napplet:profile/open\" }",
    msg 7 "{ \"type\": \"inc.emit\", \"topic\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } }"]),
  mk "inc-channel" (sAB ++ [msg 7 "{ \"type\": \"inc.channel.open\", \"id\": \"ch1\", \"target\": \"endpoint-2\" }",
    msg 7 "{ \"type\": \"inc.channel.emit\", \"channelId\": \"c-0\", \"payload\": { \"command\": \"play\", \"track\": 3 } }",
    .portClosed 7]),
  ⟨"inc-named", namedHeader, some namedCfg,
    bootInputs 1 7 "music-controller" [1] ++ bootInputs 2 8 "media-player" [2] ++
    [msg 7 "{ \"type\": \"inc.channel.open\", \"id\": \"ch1\", \"target\": \"endpoint-media-player\" }",
     msg 7 "{ \"type\": \"inc.channel.emit\", \"channelId\": \"c-abc\", \"payload\": { \"command\": \"play\", \"track\": 3 } }",
     msg 8 "{ \"type\": \"inc.channel.emit\", \"channelId\": \"c-abc\", \"payload\": { \"status\": \"playing\", \"track\": 3 } }",
     msg 7 "{ \"type\": \"inc.channel.close\", \"channelId\": \"c-abc\" }"]⟩,
  mk "intent" (sCat ++ [msg 7 "{ \"type\": \"intent.available\", \"id\": \"a1\", \"archetype\": \"profile\" }",
    msg 7 "{ \"type\": \"intent.invoke\", \"id\": \"i1\", \"request\": { \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } } }",
    msg 7 "{ \"type\": \"intent.invoke\", \"id\": \"i2\", \"request\": { \"archetype\": \"emoji-list\", \"action\": \"open\", \"convention\": \"napplet:emoji-list/open\" } }",
    msg 7 ("{ \"type\": \"intent.launch\", \"id\": \"l3\", \"target\": { \"address\": \"35129:" ++ publisher ++ ":chess\" } }"),
    .event (.nap .intent "replay" (Json.parse! "{ \"window\": 2, \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } }")),
    .event (.nap .intent "replay" (Json.parse! "{ \"window\": 1, \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\" }"))]),
  mk "intent-launch" launch,
  mk "intent-launch-teardown" (sCat ++ [msg 7 ("{ \"type\": \"intent.launch\", \"id\": \"l1\", \"target\": { \"address\": \"35129:" ++ publisher ++ ":profile-viewer\" } }"), .portClosed 7]),
  mk "notify" (s1 ++ [msg 7 "{ \"type\": \"notify.send\", \"id\": \"n3\", \"title\": \"x\" }",
    msg 7 "{ \"type\": \"notify.permission.request\", \"id\": \"p1\" }",
    .reply ⟨.notify, 0⟩ (.decision true none),
    msg 7 "{ \"type\": \"notify.send\", \"id\": \"n1\", \"title\": \"New message\", \"body\": \"Alice: hey!\", \"priority\": \"normal\" }",
    .event (.nap .notify "clicked" (Json.parse! "{\"notificationId\":\"shell-0\"}"))]),
  mk "display" (s1 ++ [msg 7 "{ \"type\": \"display.list\", \"id\": \"d1\" }",
    msg 7 "{ \"type\": \"display.push\", \"id\": \"d2\", \"displayId\": \"desk\", \"pixels\": [{ \"x\": 0, \"y\": 0, \"bytes\": [255, 0, 0] }, { \"x\": 1, \"y\": 0, \"bytes\": [0, 255, 0] }] }",
    msg 7 "{ \"type\": \"display.push\", \"id\": \"d3\", \"displayId\": \"nope\", \"pixels\": [{ \"x\": 0, \"y\": 0, \"bytes\": [255, 0, 0] }] }"]),
  mk "keys" (s1 ++ [msg 7 "{ \"type\": \"keys.registerAction\", \"id\": \"r1\", \"action\": { \"id\": \"editor.save\", \"label\": \"Save\", \"defaultKey\": \"Ctrl+S\" } }",
    msg 7 "{ \"type\": \"keys.forward\", \"key\": \"s\", \"code\": \"KeyS\", \"ctrl\": true, \"alt\": false, \"shift\": false, \"meta\": false }",
    msg 7 "{ \"type\": \"keys.registerAction\", \"id\": \"r1\", \"action\": { \"id\": \"editor.save\", \"label\": \"Save\" } }",
    .portClosed 7]),
  mk "relay-subscribe" (sU ++ [msg 7 "{ \"type\": \"relay.subscribe\", \"id\": \"a1\", \"subId\": \"sub-1\", \"filters\": [{ \"kinds\": [1], \"limit\": 50 }] }",
    .reply ⟨.relay, 0⟩ (.event ev1 "wss://relay.example.com"), .reply ⟨.relay, 0⟩ .eose,
    msg 7 "{ \"type\": \"relay.close\", \"id\": \"d4\", \"subId\": \"sub-1\" }"]),
  mk "relay-publish" (sU ++ [msg 7 "{ \"type\": \"relay.publish\", \"id\": \"b2\", \"event\": { \"kind\": 1, \"content\": \"hello world\", \"tags\": [], \"created_at\": 1234567890 } }",
    .reply ⟨.relay, 0⟩ (.signed (some evPub)), .reply ⟨.relay, 1⟩ (.published [("wss://relay.example.com", true)])]),
  mk "relay-ciphertext" (sU ++ [msg 7 "{ \"type\": \"relay.publish\", \"id\": \"b3\", \"event\": { \"kind\": 4, \"content\": \"Zm9v?iv=YmFy\" } }",
    msg 7 "{ \"type\": \"relay.publishEncrypted\", \"id\": \"f6\", \"event\": { \"kind\": 4, \"content\": \"secret message\", \"tags\": [[\"p\", \"recipient...\"]], \"created_at\": 1234567890 }, \"recipient\": \"recipient...\", \"encryption\": \"nip44\" }"]),
  mk "relay-query" (sU ++ [msg 7 "{ \"type\": \"relay.query\", \"id\": \"c3\", \"filters\": [{ \"authors\": [\"def...\"], \"kinds\": [0], \"limit\": 1 }] }",
    .reply ⟨.relay, 0⟩ (.event ev0 "wss://relay.example.com"), .reply ⟨.relay, 0⟩ .eose]),
  mk "outbox" outbox,
  mk "media" (s1 ++ [msg 7 "{ \"type\": \"media.session.create\", \"id\": \"m1\", \"owner\": \"napplet\", \"sessionId\": \"s1\", \"metadata\": { \"title\": \"Episode 12\", \"artist\": \"Alice\", \"mediaType\": \"audio\" } }",
    msg 7 "{ \"type\": \"media.session.destroy\", \"sessionId\": \"nope\" }",
    msg 7 "{ \"type\": \"media.session.destroy\", \"sessionId\": \"s1\" }"]),
  mk "config" (s1 ++ [msg 7 "{ \"type\": \"config.get\", \"id\": \"g0\" }",
    msg 7 "{ \"type\": \"config.registerSchema\", \"id\": \"r2\", \"schema\": { \"type\": \"object\", \"properties\": { \"username\": { \"type\": \"string\", \"pattern\": \"^[a-z]+$\" } } } }",
    msg 7 "{ \"type\": \"config.registerSchema\", \"id\": \"e1\", \"schema\": { \"type\": \"string\" } }",
    msg 7 cfgSchema, msg 7 "{ \"type\": \"config.get\", \"id\": \"g1\" }", msg 7 "{ \"type\": \"config.subscribe\" }",
    .event (.nap .config "edited" (Json.parse! "{\"window\":1,\"values\":{\"theme\":\"light\"}}"))]),
  mk "resource-data" (s1 ++ [msg 7 "{ \"type\": \"resource.bytes\", \"id\": \"r1\", \"url\": \"data:application/octet-stream;base64,AAEC/w==\" }"]),
  mk "resource-fetch" (s1 ++ [msg 7 "{ \"type\": \"resource.bytes\", \"id\": \"r2\", \"url\": \"https://example.com/a.bin\" }",
    .reply ⟨.resource, 0⟩ (.fetched ⟨[.v4 93 184 216 34], some [0, 1, 2, 255], false, "text/html"⟩)]),
  mk "resource-redirect" (s1 ++ [msg 7 "{ \"type\": \"resource.bytes\", \"id\": \"r2\", \"url\": \"https://example.com/a.bin\" }",
    .reply ⟨.resource, 0⟩ (.fetched ⟨[.v4 93 184 216 34, .v4 169 254 169 254], some [0], false, ""⟩)]),
  mk "resource-cancel" (s1 ++ [msg 7 "{ \"type\": \"resource.bytes\", \"id\": \"r2\", \"url\": \"https://example.com/a.bin\" }",
    msg 7 "{ \"type\": \"resource.cancel\", \"id\": \"r2\" }",
    .reply ⟨.resource, 0⟩ (.fetched ⟨[.v4 93 184 216 34], some [0], false, ""⟩)]),
  mk "upload-info" (s1 ++ [msg 7 "{ \"type\": \"upload.info\", \"id\": \"i1\" }"]),
  mk "upload" upload,
  mk "upload-refused" (let p := sU ++ [msg 7 "{ \"type\": \"upload.upload\", \"id\": \"u1\", \"request\": { \"rail\": \"nip96\", \"data\": [137, 80, 78, 71], \"mimeType\": \"image/png\", \"filename\": \"photo.png\" } }"]
    p ++ [.reply (tagOf (lastOuts testCfg p) ⟨.upload, 999⟩) (.decision false none)]),
  mk "link" (s1 ++ [msg 7 "{ \"type\": \"link.open\", \"id\": \"l2\", \"url\": \"file:///etc/passwd\" }",
    msg 7 "{ \"type\": \"link.open\", \"id\": \"l1\", \"url\": \"https://example.com/post/123\", \"options\": { \"label\": \"Read the post\" } }",
    .reply ⟨.link, 0⟩ (.decision true none)]),
  mk "link-denied" (s1 ++ [msg 7 "{ \"type\": \"link.open\", \"id\": \"l1\", \"url\": \"https://example.com/post/123\", \"options\": { \"label\": \"Read the post\" } }",
    .reply ⟨.link, 0⟩ (.decision false none)]),
  mk "value" (sU ++ [msg 7 ("{ \"type\": \"value.quote\", \"id\": \"q1\", \"request\": " ++ valueReq ++ " }"),
    .reply ⟨.value, 0⟩ (.json (Json.parse! "{\"feesMsat\":10,\"expiresAt\":1234567999}"))]),
  mk "value-send-refused" valueSend,
  mk "cvm" (sU ++ [msg 7 "{ \"type\": \"cvm.discover\", \"id\": \"d1\", \"query\": { \"search\": \"relay\", \"limit\": 5 } }",
    .reply ⟨.cvm, 1⟩ (.json (Json.parse! "{\"servers\":[{\"pubkey\":\"65a334\",\"name\":\"Relay tools\"}]}")),
    msg 7 "{ \"type\": \"cvm.registry.list\", \"id\": \"l1\" }"]),
  ⟨"cvm-registry", regHeader, some regCfg, registry⟩,
  mk "pow" (sU ++ [msg 7 "{ \"type\": \"pow.mine\", \"id\": \"m1\", \"jobId\": \"job-1\", \"template\": { \"kind\": 1, \"content\": \"gm\", \"tags\": [] }, \"target\": 21, \"options\": { \"workers\": 4, \"priority\": 0 } }",
    msg 7 "{ \"type\": \"pow.mine\", \"id\": \"m2\", \"jobId\": \"job-1\", \"template\": { \"kind\": 1, \"content\": \"gm\" }, \"target\": 21 }",
    .reply ⟨.pow, 1⟩ (.json (Json.parse! "{\"nonce\":\"1099148\",\"hashes\":4980000,\"elapsedMs\":12100}"))]),
  ⟨"shell-check", checkHeader, some checkCfg, bootInputs 1 7 "my-napplet" [1] ++
    [msg 7 ("{ \"type\": \"shell.check\", \"id\": \"c1\", \"manifest\": " ++ chessManifest ", [\"R\", \"relay\"]" ++ " }"),
     msg 7 ("{ \"type\": \"shell.check\", \"id\": \"c2\", \"manifest\": " ++ chessManifest ", [\"R\", \"theme\"], [\"O\", \"relay\"]" ++ " }")]⟩
]

/-! ### Traces beyond the E2E vectors -/

/-- Real SHA-256 (the oracle's default host): a manifest whose `x` is the artifact's
SHA-256 loads; one whose `x` is not is rejected with `hashMismatch`. -/
def shaTrace : Trace :=
  let bytes := Sha256.ofString "<!doctype html><title>hi</title>"
  let good : ManifestEvent := ⟨35129, publisher, "hi", [⟨"d", ["hi"]⟩, ⟨"x", [Sha256.hash bytes]⟩], hexOf 1⟩
  let bad : ManifestEvent := ⟨35129, publisher, "hi", [⟨"d", ["hi"]⟩, ⟨"x", [Sha256.hash []]⟩], hexOf 2⟩
  ⟨"sha256", "{\"config\":{},\"host\":{}}", none,
    [.create 1 good bytes 1, .load 1, .hello 1 [7], .create 2 bad bytes 2,
     msg 7 "{ \"type\": \"shell.ready\" }"]⟩

/-- A restored session: the stored value is there, nothing else is. -/
def restoreTrace : Trace :=
  let bytes : Bytes := "my-napplet".toList.map fun c => c.toNat.toUInt8
  let sc : NapStorage.Scope := ⟨.named publisher "my-napplet", fakeHash bytes, none⟩
  let p : Persist.Persisted := ⟨[(sc, [("theme", "dark")])], [], [], [], [], [], [], []⟩
  let hdr := "{\"config\":{},\"host\":{\"hash\":\"test\",\"sniff\":\"test\"},\"restore\":" ++
    (Persist.encPersisted p).render ++ "}"
  ⟨"restore", hdr, none,
    [.portClosed 7, msg 7 "{ \"type\": \"storage.get\", \"id\": \"a0\", \"key\": \"theme\" }"] ++ s1 ++
    [msg 7 "{ \"type\": \"storage.get\", \"id\": \"a1\", \"key\": \"theme\" }",
     msg 7 "{ \"type\": \"storage.set\", \"id\": \"b1\", \"key\": \"lang\", \"value\": \"en\" }",
     msg 7 "{ \"type\": \"storage.keys\", \"id\": \"k1\" }"]⟩

def extra : List Trace := [shaTrace, restoreTrace]

/-- The input lines of a trace (header, then one encoded input per line). -/
def inLines (t : Trace) : List String :=
  t.header :: t.inputs.map fun i => (Codec.encInput i).render

/-- Expected output lines, from the reference `Runtime.step` under the decoded header. -/
def expected (t : Trace) : Except String (List String) := do
  let hj ← match Json.parse t.header with | some j => pure j | none => .error "header is not JSON"
  let s ← Oracle.decHeader hj
  -- `abs` of the oracle's start is `RtState.init` or `RtState.restore` (`abs_init'`, `abs_restore`)
  let (_, lines, _) := t.inputs.foldl (fun (acc : RtState × List String × Nat) i =>
    let (st, outs) := Runtime.step s.host s.cfg acc.1 i
    let out := Json.mkObj [("step", some (.nat acc.2.2)), ("outputs", some (Codec.encList Codec.encOutput outs))]
    (st, acc.2.1 ++ [out.render], acc.2.2 + 1)) (Refine.abs s.state, [], 0)
  pure lines

/-- The reference outputs under the E2E configuration and the test host, as JSON lines. -/
def e2eLines (t : Trace) (cfg : Config) : List String :=
  let (_, lines, _) := t.inputs.foldl (fun (acc : RtState × List String × Nat) i =>
    let (st, outs) := Runtime.step testHost cfg acc.1 i
    let out := Json.mkObj [("step", some (.nat acc.2.2)), ("outputs", some (Codec.encList Codec.encOutput outs))]
    (st, acc.2.1 ++ [out.render], acc.2.2 + 1)) (RtState.init cfg, [], 0)
  lines

end Napplet.Test.Traces
