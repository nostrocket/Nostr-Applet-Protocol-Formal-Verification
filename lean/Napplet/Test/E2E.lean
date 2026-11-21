/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Test.Harness

/-!
# End-to-end vectors through `Runtime.step`

Each vector boots napplets through NIP-5D, posts upstream example JSON on the
bound port and checks the JSON the composed runtime sends back. Example texts are
copied from the NAP specs at the SHAs listed in `lean/README.md`.
-/

namespace Napplet.Test

open _root_.Napplet.Runtime

def s1 : RtState := booted [(1, 7, "my-napplet")]

/-! ### NIP-5D -/

-- the napplet is bound on port 7
#guard (s1.shell.bindings 7).isSome
-- JSON on an unbound port: nothing
#guard (post s1 8 "{ \"type\": \"storage.get\", \"id\": \"a1\", \"key\": \"theme\" }").2 == []
-- unknown type: silently ignored
#guard (post s1 7 "{ \"type\": \"storage.clear\", \"id\": \"x\" }").2 == []
#guard (post s1 7 "{ \"type\": \"nosuch.thing\", \"id\": \"x\" }").2 == []
-- a second hello tears the frame down: close the port, remove the frame
#guard (Runtime.step testHost testCfg s1 (.hello 1 [9])).2 == [.closePort 7, .removeFrame 1]

/-! ### NAP-SHELL -/

#guard sendsAre 7 (post s1 7 "{ \"type\": \"shell.ready\" }").2
  ["{ \"type\": \"shell.init\", \"capabilities\": { \"domains\": [\"shell\", \"intent\", \"inc\", \"theme\", \"identity\", \"relay\", \"storage\", \"keys\", \"media\", \"notify\", \"resource\", \"config\", \"upload\", \"value\", \"outbox\", \"cvm\", \"link\", \"pow\", \"display\"] }, \"services\": [] }"]
#guard (post (post s1 7 "{ \"type\": \"shell.ready\" }").1 7 "{ \"type\": \"shell.ready\" }").2 == []

/-! ### NAP-STORAGE -/

#guard sendsAre 7 (post s1 7 "{ \"type\": \"storage.get\", \"id\": \"a2\", \"key\": \"missing-key\" }").2
  ["{ \"type\": \"storage.get.result\", \"id\": \"a2\", \"value\": null }"]

def sSet := (post s1 7 "{ \"type\": \"storage.set\", \"id\": \"b2\", \"key\": \"theme\", \"value\": \"light\" }")
#guard sendsAre 7 sSet.2 ["{ \"type\": \"storage.set.result\", \"id\": \"b2\" }"]
#guard sendsAre 7 (post sSet.1 7 "{ \"type\": \"storage.get\", \"id\": \"a1\", \"key\": \"theme\" }").2
  ["{ \"type\": \"storage.get.result\", \"id\": \"a1\", \"value\": \"light\" }"]
#guard sendsAre 7 (post sSet.1 7 "{ \"type\": \"storage.keys\", \"id\": \"d4\" }").2
  ["{ \"type\": \"storage.keys.result\", \"id\": \"d4\", \"keys\": [\"theme\"] }"]
#guard sendsAre 7 (post sSet.1 7 "{ \"type\": \"storage.remove\", \"id\": \"c3\", \"key\": \"theme\" }").2
  ["{ \"type\": \"storage.remove.result\", \"id\": \"c3\" }"]
-- instance scope is separate from shared scope
#guard sendsAre 7 (post sSet.1 7 "{ \"type\": \"storage.get\", \"id\": \"a3\", \"key\": \"theme\", \"scope\": \"instance\" }").2
  ["{ \"type\": \"storage.get.result\", \"id\": \"a3\", \"value\": null }"]
-- another napplet (different d, different bytes) does not see it
def s2 : RtState := (runAll testHost testCfg sSet.1 (bootInputs 2 8 "other" [1, 2, 3])).1
#guard sendsAre 8 (post s2 8 "{ \"type\": \"storage.get\", \"id\": \"a1\", \"key\": \"theme\" }").2
  ["{ \"type\": \"storage.get.result\", \"id\": \"a1\", \"value\": null }"]
-- a malformed request with an id gets an error result
#guard sendsAre 7 (post s1 7 "{ \"type\": \"storage.set\", \"id\": \"b9\", \"key\": \"theme\" }").2
  ["{ \"type\": \"storage.set.result\", \"id\": \"b9\", \"error\": \"invalid request\" }"]

/-! ### NAP-THEME -/

#guard sendsAre 7 (post s1 7 "{ \"type\": \"theme.get\", \"id\": \"t1\" }").2
  ["{ \"type\": \"theme.get.result\", \"id\": \"t1\", \"error\": \"no active theme\" }"]

def themeText : String := "{ \"colors\": { \"background\": \"#ffffff\", \"text\": \"#333333\", \"primary\": \"#0066cc\" } }"
def sTheme := Runtime.step testHost testCfg s1 (.event (.themeChanged (some (Json.parse! themeText))))
#guard sendsAre 7 sTheme.2 ["{ \"type\": \"theme.changed\", \"theme\": " ++ themeText ++ " }"]
#guard sendsAre 7 (post sTheme.1 7 "{ \"type\": \"theme.get\", \"id\": \"t2\" }").2
  ["{ \"type\": \"theme.get.result\", \"id\": \"t2\", \"theme\": " ++ themeText ++ " }"]

/-! ### NAP-IDENTITY -/

#guard sendsAre 7 (post s1 7 "{ \"type\": \"identity.getPublicKey\", \"id\": \"q1b\" }").2
  ["{ \"type\": \"identity.getPublicKey.result\", \"id\": \"q1b\", \"pubkey\": \"\" }"]

def sUser := Runtime.step testHost testCfg s1 (.event (.userChanged "ab12cd"))
#guard sendsAre 7 sUser.2 ["{ \"type\": \"identity.changed\", \"pubkey\": \"ab12cd\" }"]
#guard sendsAre 7 (post sUser.1 7 "{ \"type\": \"identity.getPublicKey\", \"id\": \"q1\" }").2
  ["{ \"type\": \"identity.getPublicKey.result\", \"id\": \"q1\", \"pubkey\": \"ab12cd\" }"]

def sFollows := post sUser.1 7 "{ \"type\": \"identity.getFollows\", \"id\": \"q4\" }"
#guard (calls sFollows.2).length == 1
def sFollowsDone := Runtime.step testHost testCfg sFollows.1
  (.reply ⟨.identity, 0⟩ (.json (Json.parse! "{ \"pubkeys\": [\"ab12...\", \"cd34...\", \"ef56...\"] }")))
#guard sendsAre 7 sFollowsDone.2
  ["{ \"type\": \"identity.getFollows.result\", \"id\": \"q4\", \"pubkeys\": [\"ab12...\", \"cd34...\", \"ef56...\"] }"]
-- a reply after teardown does nothing
#guard (Runtime.step testHost testCfg (Runtime.step testHost testCfg sFollows.1 (.portClosed 7)).1
  (.reply ⟨.identity, 0⟩ (.json (Json.parse! "{ \"pubkeys\": [] }")))).2 == []

/-! ### NAP-INC -/

def sAB : RtState := booted [(1, 7, "social-feed"), (2, 8, "profile-viewer")]

def sSub := post sAB 8 "{ \"type\": \"inc.subscribe\", \"id\": \"a1\", \"topic\": \"napplet:profile/open\" }"
#guard sendsAre 8 sSub.2 ["{ \"type\": \"inc.subscribe.result\", \"id\": \"a1\" }"]
def sEmit := post sSub.1 7 "{ \"type\": \"inc.emit\", \"topic\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } }"
#guard sendsAre 8 sEmit.2
  ["{ \"type\": \"inc.event\", \"topic\": \"napplet:profile/open\", \"sender\": \"endpoint-1\", \"payload\": { \"pubkey\": \"abc123...\" } }"]
#guard sentTo 7 sEmit.2 == []

def sOpen := post sAB 7 "{ \"type\": \"inc.channel.open\", \"id\": \"ch1\", \"target\": \"endpoint-2\" }"
#guard sendsAre 8 sOpen.2 ["{ \"type\": \"inc.channel.opened\", \"channelId\": \"c-0\", \"peer\": \"endpoint-1\" }"]
#guard sendsAre 7 sOpen.2 ["{ \"type\": \"inc.channel.open.result\", \"id\": \"ch1\", \"channelId\": \"c-0\", \"peer\": \"endpoint-2\" }"]
#guard sendsAre 8 (post sOpen.1 7 "{ \"type\": \"inc.channel.emit\", \"channelId\": \"c-0\", \"payload\": { \"command\": \"play\", \"track\": 3 } }").2
  ["{ \"type\": \"inc.channel.event\", \"channelId\": \"c-0\", \"sender\": \"endpoint-1\", \"payload\": { \"command\": \"play\", \"track\": 3 } }"]
-- the opener's window goes away: the peer gets "peer destroyed"
#guard sendsAre 8 (Runtime.step testHost testCfg sOpen.1 (.portClosed 7)).2
  ["{ \"type\": \"inc.channel.closed\", \"channelId\": \"c-0\", \"reason\": \"peer destroyed\" }"]
#guard sendsAre 7 (post sAB 7 "{ \"type\": \"inc.channel.open\", \"id\": \"ch1\", \"target\": \"endpoint-media-player\" }").2
  ["{ \"type\": \"inc.channel.open.result\", \"id\": \"ch1\", \"error\": \"target not found\" }"]

/-! ### NAP-INTENT -/

def viewerId : String := "nip5d:35129:" ++ publisher ++ ":profile-viewer"
def catalogText : String :=
  "{\"entries\":[{\"id\":\"" ++ viewerId ++ "\",\"title\":\"Profile Viewer\",\"z\":[\"profile\"],\"i\":[[\"napplet:profile/open\",\"pubkey\"]]}]}"
def sCat := runAll testHost testCfg sAB
  [.event (.nap .intent "catalog" (Json.parse! catalogText)),
   .event (.nap .intent "default" (Json.parse! ("{\"archetype\":\"profile\",\"handler\":\"" ++ viewerId ++ "\"}")))]

#guard sendsAre 7 (post sCat.1 7 "{ \"type\": \"intent.available\", \"id\": \"a1\", \"archetype\": \"profile\" }").2
  ["{ \"type\": \"intent.available.result\", \"id\": \"a1\", \"availability\": { \"archetype\": \"profile\", \"available\": true, \"candidates\": [{ \"id\": \"" ++ viewerId ++ "\", \"title\": \"Profile Viewer\", \"actions\": [\"open\"], \"conventions\": [\"napplet:profile/open\"], \"contracts\": [{ \"convention\": \"napplet:profile/open\", \"params\": [\"pubkey\"] }], \"isDefault\": true }], \"hasDefault\": true } }"]

def sInv := post sCat.1 7 "{ \"type\": \"intent.invoke\", \"id\": \"i1\", \"request\": { \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } } }"
#guard sendsAre 7 sInv.2
  ["{ \"type\": \"intent.invoke.result\", \"id\": \"i1\", \"result\": { \"ok\": true, \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"handler\": \"" ++ viewerId ++ "\" } }"]
#guard sendsAre 8 sInv.2
  ["{ \"type\": \"intent.deliver\", \"delivery\": { \"sender\": \"nip5d:35129:" ++ publisher ++ ":social-feed\", \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } } }"]
#guard sendsAre 7 (post sCat.1 7 "{ \"type\": \"intent.invoke\", \"id\": \"i2\", \"request\": { \"archetype\": \"emoji-list\", \"action\": \"open\", \"convention\": \"napplet:emoji-list/open\" } }").2
  ["{ \"type\": \"intent.invoke.result\", \"id\": \"i2\", \"result\": { \"ok\": false, \"error\": \"no handler\" } }"]

/-! ### NAP-NOTIFY -/

def sPerm := post s1 7 "{ \"type\": \"notify.permission.request\", \"id\": \"p1\" }"
#guard sendsAre 7 sPerm.2 ["{ \"type\": \"notify.controls\", \"controls\": [\"toasts\", \"badges\", \"actions\", \"channels\"] }"]
#guard (calls sPerm.2).length == 1
def sGranted := Runtime.step testHost testCfg sPerm.1 (.reply ⟨.notify, 0⟩ (.decision true none))
#guard sendsAre 7 sGranted.2 ["{ \"type\": \"notify.permission.result\", \"id\": \"p1\", \"granted\": true }"]
def sNote := post sGranted.1 7 "{ \"type\": \"notify.send\", \"id\": \"n1\", \"title\": \"New message\", \"body\": \"Alice: hey!\", \"priority\": \"normal\" }"
#guard sendsAre 7 sNote.2 ["{ \"type\": \"notify.send.result\", \"id\": \"n1\", \"notificationId\": \"shell-0\" }"]
#guard sendsAre 7 (Runtime.step testHost testCfg sNote.1 (.event (.nap .notify "clicked" (Json.parse! "{\"notificationId\":\"shell-0\"}")))).2
  ["{ \"type\": \"notify.clicked\", \"notificationId\": \"shell-0\" }"]
-- before permission: refused, nothing created
#guard sendsAre 7 (post s1 7 "{ \"type\": \"notify.send\", \"id\": \"n3\", \"title\": \"x\" }").2
  ["{ \"type\": \"notify.controls\", \"controls\": [\"toasts\", \"badges\", \"actions\", \"channels\"] }",
   "{ \"type\": \"notify.send.result\", \"id\": \"n3\", \"error\": \"permission denied\" }"]

/-! ### NAP-DISPLAY -/

#guard sendsAre 7 (post s1 7 "{ \"type\": \"display.list\", \"id\": \"d1\" }").2
  ["{ \"type\": \"display.list.result\", \"id\": \"d1\", \"displays\": [{ \"id\": \"desk\", \"width\": 800, \"height\": 480, \"type\": \"eink\" }] }"]
#guard sendsAre 7 (post s1 7 "{ \"type\": \"display.push\", \"id\": \"d2\", \"displayId\": \"desk\", \"pixels\": [{ \"x\": 0, \"y\": 0, \"bytes\": [255, 0, 0] }, { \"x\": 1, \"y\": 0, \"bytes\": [0, 255, 0] }] }").2
  ["{ \"type\": \"display.push.result\", \"id\": \"d2\" }"]
#guard sendsAre 7 (post s1 7 "{ \"type\": \"display.push\", \"id\": \"d3\", \"displayId\": \"nope\", \"pixels\": [{ \"x\": 0, \"y\": 0, \"bytes\": [255, 0, 0] }] }").2
  ["{ \"type\": \"display.push.result\", \"id\": \"d3\", \"error\": \"not-found\" }"]

/-! ### NAP-KEYS -/

def sKey := post s1 7 "{ \"type\": \"keys.registerAction\", \"id\": \"r1\", \"action\": { \"id\": \"editor.save\", \"label\": \"Save\", \"defaultKey\": \"Ctrl+S\" } }"
#guard sendsAre 7 sKey.2
  ["{ \"type\": \"keys.registerAction.result\", \"id\": \"r1\", \"actionId\": \"editor.save\", \"binding\": \"Ctrl+S\" }",
   "{ \"type\": \"keys.bindings\", \"bindings\": [{ \"actionId\": \"editor.save\", \"key\": \"Ctrl+S\" }] }"]
#guard sendsAre 7 (post sKey.1 7 "{ \"type\": \"keys.forward\", \"key\": \"s\", \"code\": \"KeyS\", \"ctrl\": true, \"alt\": false, \"shift\": false, \"meta\": false }").2
  ["{ \"type\": \"keys.action\", \"actionId\": \"editor.save\" }"]
-- the same combo cannot be bound twice
#guard sendsAre 7 (post sKey.1 7 "{ \"type\": \"keys.registerAction\", \"id\": \"r1\", \"action\": { \"id\": \"editor.save\", \"label\": \"Save\" } }").2
  ["{ \"type\": \"keys.registerAction.result\", \"id\": \"r1\", \"actionId\": \"editor.save\", \"error\": \"duplicate action ID\" }"]
-- teardown drops the bindings: the next napplet on the port starts clean
#guard (Runtime.mentions (Runtime.step testHost testCfg sKey.1 (.portClosed 7)).1 7) == false

/-! ### NAP-RELAY -/

def sU : RtState := (Runtime.step testHost testCfg s1 (.event (.userChanged "def..."))).1

def ev1 : NostrEvent := (NostrEvent.ofJson? (Json.parse! "{ \"id\": \"abc...\", \"pubkey\": \"def...\", \"kind\": 1, \"content\": \"hello\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }")).get!

def sRSub := post sU 7 "{ \"type\": \"relay.subscribe\", \"id\": \"a1\", \"subId\": \"sub-1\", \"filters\": [{ \"kinds\": [1], \"limit\": 50 }] }"
#guard (calls sRSub.2).map (·.1) == [⟨.relay, 0⟩]
def sREv := runAll testHost testCfg sRSub.1
  [.reply ⟨.relay, 0⟩ (.event ev1 "wss://relay.example.com"), .reply ⟨.relay, 0⟩ .eose]
#guard sendsAre 7 sREv.2
  ["{ \"type\": \"relay.event\", \"subId\": \"sub-1\", \"result\": { \"event\": { \"id\": \"abc...\", \"pubkey\": \"def...\", \"kind\": 1, \"content\": \"hello\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }, \"sidecar\": { \"relayHints\": [\"wss://relay.example.com\"] } } }",
   "{ \"type\": \"relay.eose\", \"subId\": \"sub-1\" }"]

def evPub : NostrEvent := { id := "abc...", pubkey := "def...", createdAt := 1234567890, kind := 1, tags := [], content := "hello world", sig := "ghi..." }
def sRPub := post sU 7 "{ \"type\": \"relay.publish\", \"id\": \"b2\", \"event\": { \"kind\": 1, \"content\": \"hello world\", \"tags\": [], \"created_at\": 1234567890 } }"
#guard match calls sRPub.2 with
  | [(_, .sign u)] => u == { pubkey := "def...", createdAt := 1234567890, kind := 1, tags := [], content := "hello world" }
  | _ => false
def sRPubDone := runAll testHost testCfg sRPub.1
  [.reply ⟨.relay, 0⟩ (.signed (some evPub)), .reply ⟨.relay, 1⟩ (.published [("wss://relay.example.com", true)])]
#guard sendsAre 7 sRPubDone.2
  ["{ \"type\": \"relay.publish.result\", \"id\": \"b2\", \"ok\": true, \"event\": { \"id\": \"abc...\", \"pubkey\": \"def...\", \"kind\": 1, \"content\": \"hello world\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"ghi...\" }, \"eventId\": \"abc...\" }"]
-- napplet-supplied ciphertext is never signed
#guard (calls (post sU 7 "{ \"type\": \"relay.publish\", \"id\": \"b3\", \"event\": { \"kind\": 4, \"content\": \"Zm9v?iv=YmFy\" } }").2).isEmpty
-- publishEncrypted: the shell encrypts first (NIP-44 default)
#guard match calls (post sU 7 "{ \"type\": \"relay.publishEncrypted\", \"id\": \"f6\", \"event\": { \"kind\": 4, \"content\": \"secret message\", \"tags\": [[\"p\", \"recipient...\"]], \"created_at\": 1234567890 }, \"recipient\": \"recipient...\", \"encryption\": \"nip44\" }").2 with
  | [(_, .encrypt .nip44 "recipient..." "secret message")] => true
  | _ => false
def sRQ := post sU 7 "{ \"type\": \"relay.query\", \"id\": \"c3\", \"filters\": [{ \"authors\": [\"def...\"], \"kinds\": [0], \"limit\": 1 }] }"
def ev0 : NostrEvent := { id := "xyz...", pubkey := "def...", createdAt := 1234567890, kind := 0, tags := [], content := "{...}", sig := "..." }
#guard sendsAre 7 (runAll testHost testCfg sRQ.1 [.reply ⟨.relay, 0⟩ (.event ev0 "wss://relay.example.com"), .reply ⟨.relay, 0⟩ .eose]).2
  ["{ \"type\": \"relay.query.result\", \"id\": \"c3\", \"events\": [{ \"event\": { \"id\": \"xyz...\", \"pubkey\": \"def...\", \"kind\": 0, \"content\": \"{...}\", \"tags\": [], \"created_at\": 1234567890, \"sig\": \"...\" }, \"sidecar\": { \"relayHints\": [\"wss://relay.example.com\"] } }] }"]
#guard sendsAre 7 (post sRSub.1 7 "{ \"type\": \"relay.close\", \"id\": \"d4\", \"subId\": \"sub-1\" }").2
  ["{ \"type\": \"relay.closed\", \"subId\": \"sub-1\" }"]

/-! ### NAP-OUTBOX -/

def sOP := post sU 7 "{ \"type\": \"outbox.publish\", \"id\": \"p2\", \"event\": { \"kind\": 1, \"content\": \"hi\", \"tags\": [] }, \"options\": { \"toOutbox\": false, \"relays\": [\"wss://relay.example.com\"] } }"
def evO : NostrEvent := { id := "ev2...", pubkey := "def...", createdAt := 0, kind := 1, tags := [], content := "hi", sig := "s" }
def sOPDone := runAll testHost testCfg sOP.1
  ((calls sOP.2).map (fun (t, _) => Input.reply t (.signed (some evO))) ++ [.reply ⟨.outbox, 1⟩ (.published [("wss://relay.example.com", true)])])
#guard sendsAre 7 sOPDone.2
  ["{ \"type\": \"outbox.publish.result\", \"id\": \"p2\", \"ok\": true, \"event\": { \"id\": \"ev2...\", \"pubkey\": \"def...\", \"created_at\": 0, \"kind\": 1, \"tags\": [], \"content\": \"hi\", \"sig\": \"s\" }, \"eventId\": \"ev2...\", \"relays\": { \"wss://relay.example.com\": true } }"]

/-! ### NAP-MEDIA -/

def sMed := post s1 7 "{ \"type\": \"media.session.create\", \"id\": \"m1\", \"owner\": \"napplet\", \"sessionId\": \"s1\", \"metadata\": { \"title\": \"Episode 12\", \"artist\": \"Alice\", \"mediaType\": \"audio\" } }"
#guard (sentTo 7 sMed.2).head?.map (Json.same · (Json.parse! "{ \"type\": \"media.session.create.result\", \"id\": \"m1\", \"sessionId\": \"s1\", \"owner\": \"napplet\" }")) == some true
#guard sendsAre 7 (post sMed.1 7 "{ \"type\": \"media.session.destroy\", \"sessionId\": \"s1\" }").2
  ["{ \"type\": \"media.session.ended\", \"sessionId\": \"s1\", \"reason\": \"destroyed\" }"]
-- unknown session ids are silently ignored
#guard (sentTo 7 (post sMed.1 7 "{ \"type\": \"media.session.destroy\", \"sessionId\": \"nope\" }").2).isEmpty

/-! ### NAP-CONFIG -/

def cfgSchema : String := "{ \"type\": \"config.registerSchema\", \"id\": \"r1\", \"schema\": { \"$schema\": \"http://json-schema.org/draft-07/schema#\", \"type\": \"object\", \"properties\": { \"theme\": { \"type\": \"string\", \"enum\": [\"light\", \"dark\"], \"default\": \"dark\" } } }, \"version\": 1 }"
#guard sendsAre 7 (post s1 7 "{ \"type\": \"config.get\", \"id\": \"g0\" }").2
  ["{ \"type\": \"config.schemaError\", \"code\": \"no-schema\", \"error\": \"no configuration schema is registered\" }"]
def sReg := post s1 7 cfgSchema
#guard sendsAre 7 sReg.2 ["{ \"type\": \"config.registerSchema.result\", \"id\": \"r1\", \"ok\": true }"]
#guard sendsAre 7 (post sReg.1 7 "{ \"type\": \"config.get\", \"id\": \"g1\" }").2
  ["{ \"type\": \"config.values\", \"id\": \"g1\", \"values\": { \"theme\": \"dark\" } }"]
def sCSub := post sReg.1 7 "{ \"type\": \"config.subscribe\" }"
#guard sendsAre 7 sCSub.2 ["{ \"type\": \"config.values\", \"values\": { \"theme\": \"dark\" } }"]
#guard sendsAre 7 (Runtime.step testHost testCfg sCSub.1 (.event (.nap .config "edited" (Json.parse! "{\"window\":1,\"values\":{\"theme\":\"light\"}}")))).2
  ["{ \"type\": \"config.values\", \"values\": { \"theme\": \"light\" } }"]
#guard sendsAre 7 (post s1 7 "{ \"type\": \"config.registerSchema\", \"id\": \"r2\", \"schema\": { \"type\": \"object\", \"properties\": { \"username\": { \"type\": \"string\", \"pattern\": \"^[a-z]+$\" } } } }").2
  ["{ \"type\": \"config.registerSchema.result\", \"id\": \"r2\", \"ok\": false, \"code\": \"pattern-not-allowed\", \"error\": \"JSON Schema `pattern` keyword is not permitted in the Core Subset\" }"]

/-! ### NAP-RESOURCE -/

#guard sendsAre 7 (post s1 7 "{ \"type\": \"resource.bytes\", \"id\": \"r1\", \"url\": \"data:application/octet-stream;base64,AAEC/w==\" }").2
  ["{ \"type\": \"resource.bytes.result\", \"id\": \"r1\", \"blob\": \"AAEC/w==\", \"mime\": \"application/octet-stream\" }"]
def sFetch := post s1 7 "{ \"type\": \"resource.bytes\", \"id\": \"r2\", \"url\": \"https://example.com/a.bin\" }"
#guard (calls sFetch.2) == [(⟨.resource, 0⟩, .fetch "https://example.com/a.bin")]
#guard sendsAre 7 (Runtime.step testHost testCfg sFetch.1
    (.reply ⟨.resource, 0⟩ (.fetched ⟨[.v4 93 184 216 34], some [0, 1, 2, 255], false, "text/html"⟩))).2
  ["{ \"type\": \"resource.bytes.result\", \"id\": \"r2\", \"blob\": \"AAEC/w==\", \"mime\": \"application/octet-stream\" }"]
-- a redirect through the metadata address is blocked
#guard sendsAre 7 (Runtime.step testHost testCfg sFetch.1
    (.reply ⟨.resource, 0⟩ (.fetched ⟨[.v4 93 184 216 34, .v4 169 254 169 254], some [0], false, ""⟩))).2
  ["{ \"type\": \"resource.bytes.error\", \"id\": \"r2\", \"error\": \"blocked-by-policy\" }"]
-- cancelled: the late reply is dropped
#guard (sentTo 7 (runAll testHost testCfg sFetch.1
    [.message 7 (Json.parse! "{ \"type\": \"resource.cancel\", \"id\": \"r2\" }"),
     .reply ⟨.resource, 0⟩ (.fetched ⟨[.v4 93 184 216 34], some [0], false, ""⟩)]).2).isEmpty

/-! ### NAP-UPLOAD -/

#guard sendsAre 7 (post s1 7 "{ \"type\": \"upload.info\", \"id\": \"i1\" }").2
  ["{ \"type\": \"upload.info.result\", \"id\": \"i1\", \"info\": { \"rails\": [ { \"rail\": \"nip96\", \"enabled\": true, \"returns\": [\"https\"] }, { \"rail\": \"blossom\", \"enabled\": true, \"returns\": [\"https\", \"blossom\"] } ], \"maxBytes\": 104857600, \"mimeTypes\": [\"image/png\", \"image/jpeg\", \"application/pdf\"] } }"]

def firstTag (os : List Runtime.Output) : CallTag :=
  ((calls os).head?.map (·.1)).getD ⟨.upload, 999⟩

-- First upload: consent prompt, then the shell signs NIP-98 auth, then the server stores.
def sUp0 := post sU 7 "{ \"type\": \"upload.upload\", \"id\": \"u1\", \"request\": { \"rail\": \"nip96\", \"data\": [137, 80, 78, 71], \"mimeType\": \"image/png\", \"filename\": \"photo.png\" } }"
#guard match calls sUp0.2 with | [(_, .prompt .upload "upload" _)] => true | _ => false
def sUp1 := Runtime.step testHost testCfg sUp0.1 (.reply (firstTag sUp0.2) (.decision true none))
#guard match calls sUp1.2 with | [(_, .sign u)] => u.kind == 27235 | _ => false
def sUp2 := match calls sUp1.2 with
  | [(t, .sign u)] => Runtime.step testHost testCfg sUp1.1 (.reply t (.signed (some (signAs u))))
  | _ => (sUp1.1, [])
#guard match calls sUp2.2 with | [(_, .nap .upload "put" _)] => true | _ => false
def shaUp : String := fakeHash [137, 80, 78, 71]
def sUp3 := match calls sUp2.2 with
  | [(t, _)] => Runtime.step testHost testCfg sUp2.1 (.reply t (.json (Json.parse!
      ("{\"ok\":true,\"url\":\"https://files.example.com/abc123.png\",\"sha256\":\"" ++ shaUp ++ "\",\"size\":4,\"mimeType\":\"image/png\"}"))))
  | _ => (sUp2.1, [])
#guard match sentTo 7 sUp3.2 with
  | [m] => (m.get? "result" |>.bind (·.getStr? "status")) == some "complete" &&
           (m.get? "result" |>.bind (·.getStr? "url")) == some "https://files.example.com/abc123.png" &&
           m.getStr? "id" == some "u1"
  | _ => false
-- refused consent: nothing leaves the shell
#guard (calls (Runtime.step testHost testCfg sUp0.1 (.reply (firstTag sUp0.2) (.decision false none))).2).isEmpty

/-! ### NAP-LINK -/

#guard sendsAre 7 (post s1 7 "{ \"type\": \"link.open\", \"id\": \"l2\", \"url\": \"file:///etc/passwd\" }").2
  ["{ \"type\": \"link.open.result\", \"id\": \"l2\", \"status\": \"denied\", \"error\": \"unsupported-scheme\" }"]
def sLink := post s1 7 "{ \"type\": \"link.open\", \"id\": \"l1\", \"url\": \"https://example.com/post/123\", \"options\": { \"label\": \"Read the post\" } }"
#guard (calls sLink.2).length == 1
def sLinkOk := Runtime.step testHost testCfg sLink.1 (.reply ⟨.link, 0⟩ (.decision true none))
#guard sendsAre 7 sLinkOk.2 ["{ \"type\": \"link.open.result\", \"id\": \"l1\", \"status\": \"opened\" }"]
#guard sLinkOk.2.contains (.effect (.nap .link "open" (Json.parse! "{\"url\":\"https://example.com/post/123\"}")))
#guard sendsAre 7 (Runtime.step testHost testCfg sLink.1 (.reply ⟨.link, 0⟩ (.decision false none))).2
  ["{ \"type\": \"link.open.result\", \"id\": \"l1\", \"status\": \"denied\", \"error\": \"user-denied\" }"]

/-! ### NAP-VALUE -/

def valueReq : String := "{ \"rail\": \"zap\", \"amountMsat\": 21000, \"comment\": \"great note\", \"target\": { \"type\": \"zap\", \"eventId\": \"abc...\", \"pubkey\": \"def...\", \"relays\": [\"wss://relay.example.com\"] } }"
def sQ := post sU 7 ("{ \"type\": \"value.quote\", \"id\": \"q1\", \"request\": " ++ valueReq ++ " }")
#guard match calls sQ.2 with | [(⟨.value, 0⟩, .nap .value "quote" _)] => true | _ => false
#guard sendsAre 7 (Runtime.step testHost testCfg sQ.1 (.reply ⟨.value, 0⟩ (.json (Json.parse! "{\"feesMsat\":10,\"expiresAt\":1234567999}")))).2
  ["{ \"type\": \"value.quote.result\", \"id\": \"q1\", \"quote\": { \"ok\": true, \"rail\": \"zap\", \"amountMsat\": 21000, \"feesMsat\": 10, \"expiresAt\": 1234567999 } }"]
-- send without an allowance asks the user first; refusal moves no money
def sSend := post sU 7 ("{ \"type\": \"value.send\", \"id\": \"s2\", \"request\": " ++ valueReq ++ " }")
#guard match calls sSend.2 with | [(_, .prompt .value "send" _)] => true | _ => false
#guard (calls (Runtime.step testHost testCfg sSend.1 (.reply (firstTag sSend.2) (.decision false none))).2).all
  fun (_, c) => match c with | .nap .value "pay" _ => false | _ => true

/-! ### NAP-CVM -/

def sD := post sU 7 "{ \"type\": \"cvm.discover\", \"id\": \"d1\", \"query\": { \"search\": \"relay\", \"limit\": 5 } }"
#guard sendsAre 7 (Runtime.step testHost testCfg sD.1 (.reply ⟨.cvm, 1⟩ (.json (Json.parse! "{\"servers\":[{\"pubkey\":\"65a334\",\"name\":\"Relay tools\"}]}")))).2
  ["{ \"type\": \"cvm.discover.result\", \"id\": \"d1\", \"servers\": [{ \"pubkey\": \"65a334\", \"name\": \"Relay tools\" }] }"]
-- registry is not implemented by default: exactly one result, unsupported
#guard sendsAre 7 (post sU 7 "{ \"type\": \"cvm.registry.list\", \"id\": \"l1\" }").2
  ["{ \"type\": \"cvm.registry.list.result\", \"id\": \"l1\", \"error\": \"unsupported method\" }"]

/-! ### NAP-POW -/

def sMine := post sU 7 "{ \"type\": \"pow.mine\", \"id\": \"m1\", \"jobId\": \"job-1\", \"template\": { \"kind\": 1, \"content\": \"gm\", \"tags\": [] }, \"target\": 21, \"options\": { \"workers\": 4, \"priority\": 0 } }"
#guard sendsAre 7 sMine.2 ["{ \"type\": \"pow.mine.result\", \"id\": \"m1\", \"jobId\": \"job-1\", \"accepted\": true, \"state\": \"mining\" }"]
def sMined := Runtime.step testHost testCfg sMine.1 (.reply ⟨.pow, 1⟩ (.json (Json.parse! "{\"nonce\":\"1099148\",\"hashes\":4980000,\"elapsedMs\":12100}")))
#guard (sentTo 7 sMined.2).getLast?.map (Json.same · (Json.parse! ("{ \"type\": \"pow.done\", \"jobId\": \"job-1\", \"result\": { \"jobId\": \"job-1\", \"ok\": true, \"event\": { \"id\": \"" ++ hexOf 0x2db750 ++ "\", \"pubkey\": \"def...\", \"created_at\": 0, \"kind\": 1, \"tags\": [[\"nonce\", \"1099148\", \"21\"]], \"content\": \"gm\" }, \"pow\": 234, \"nonce\": \"1099148\", \"hashes\": 4980000, \"elapsedMs\": 12100 } }"))) == some true
#guard sendsAre 7 (post sMine.1 7 "{ \"type\": \"pow.mine\", \"id\": \"m2\", \"jobId\": \"job-1\", \"template\": { \"kind\": 1, \"content\": \"gm\" }, \"target\": 21 }").2
  ["{ \"type\": \"pow.mine.result\", \"id\": \"m2\", \"jobId\": \"job-1\", \"accepted\": false, \"state\": \"error\", \"error\": \"duplicate jobId\" }"]

end Napplet.Test
