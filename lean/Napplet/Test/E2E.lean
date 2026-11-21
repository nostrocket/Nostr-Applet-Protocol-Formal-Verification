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

end Napplet.Test
