/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Binding
import Napplet.Nip19
import Napplet.Run.Intent
import Napplet.Run.Inc

/-!
# Napplet side: convention URI methods (web projection §Convention URI binding)

`intent.invoke(uri, options?)`, `intent.open(uri, options?)` and `inc.emit(topic, payload?)`
as the binding turns them into wire requests, before anything is posted:

* `NapIntent.bindUri` splits off the fragment and query, checks the
  `napplet:<archetype>/<intent>` identity, percent-decodes unique `name=value` pairs as
  text (`+` literal) and rejects malformed encoding, repeated names, a query with an
  explicit payload, and a fragment anywhere but `intent.invoke`;
* `intent.invoke` decodes a bare `naddr` fragment (`Nip19.handlerHint?`) into
  `request.handlerHint`; the raw fragment never reaches the wire; a fragment plus
  `options.handlerHint` is rejected;
* `intent.open` additionally requires the intent segment to be `open`;
* `inc.emit` transposes a convention URI's query into `payload` and sends the stable
  topic; a topic that is not a `napplet:` convention URI is sent unchanged (topics
  are opaque).

The result is a builder taking the fresh request id (`Binding.request`).
-/

namespace Napplet.BindingUri

open NapIntent

/-- `IntentInvokeOptions`. -/
structure InvokeOptions where
  payload : Option Json := none
  handler : Option String := none
  handlerHint : Option Run.Intent.Hint := none
  behavior : Option Run.Intent.Behavior := none

inductive UriError where
  | bind (e : BindError)
  | invalidFragment
  | fragmentWithHint
  | notOpen
  deriving Repr

def paramsJson (ps : List (String × String)) : Json := .obj (ps.map fun (k, v) => (k, .str v))

/-- Split the bound identity `napplet:<archetype>/<intent>`. -/
def segments (ident : List Char) : String × String :=
  let rest := ident.drop 8
  let (a, b) := splitFirst '/' rest
  (String.ofList a, String.ofList (b.getD []))

/-- `intent.invoke(uri, options)` as a request builder. -/
def invoke (uri : String) (o : InvokeOptions) : Except UriError (String → Json) := do
  let b ← (bindUri uri .intentInvoke o.payload.isSome).mapError .bind
  let hint ← match b.handlerHint with
    | none => pure o.handlerHint
    | some frag =>
      if o.handlerHint.isSome then throw .fragmentWithHint
      else match Nip19.handlerHint? (String.ofList frag) with
        | some (addr, relays) => pure (some { address := addr, relays := if relays.isEmpty then none else some relays })
        | none => throw .invalidFragment
  let (arch, act) := segments b.identity
  let payload := if b.payload.isEmpty then o.payload else some (paramsJson b.payload)
  let req : Run.Intent.Request :=
    { archetype := arch, action := act, convention := String.ofList b.identity, payload,
      handler := o.handler, hint, behavior := o.behavior }
  pure fun id => Run.Intent.encodeReq (.invoke id req)

/-- `intent.open(uri, options)`: sugar over `invoke` whose intent must be `open`. -/
def «open» (uri : String) (o : InvokeOptions) : Except UriError (String → Json) := do
  let b ← (bindUri uri .intentInvoke o.payload.isSome).mapError .bind
  if (segments b.identity).2 ≠ "open" then throw .notOpen
  invoke uri o

/-- `inc.emit(topic, payload?)`: the wire message (fire-and-forget, no id). -/
def emit (topic : String) (payload : Option Json) : Except UriError Json :=
  if topic.startsWith "napplet:" then do
    let b ← (bindUri topic .other payload.isSome).mapError .bind
    let pl := if b.payload.isEmpty then payload else some (paramsJson b.payload)
    pure (Run.Inc.encodeReq (.emit (String.ofList b.identity) pl))
  else pure (Run.Inc.encodeReq (.emit topic payload))

/-! ### Vectors (upstream examples) -/

#guard match invoke "napplet:profile/open?pubkey=abc123..." {} with
  | .ok f => Json.same (f "i1") (Json.parse! "{ \"type\": \"intent.invoke\", \"id\": \"i1\", \"request\": { \"archetype\": \"profile\", \"action\": \"open\", \"convention\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } } }")
  | .error _ => false
#guard match emit "napplet:profile/open?pubkey=abc123..." none with
  | .ok j => Json.same j (Json.parse! "{ \"type\": \"inc.emit\", \"topic\": \"napplet:profile/open\", \"payload\": { \"pubkey\": \"abc123...\" } }")
  | .error _ => false
#guard (emit "napplet:profile/open?a=1" (some .null)) matches .error _
#guard (emit "napplet:profile/open#naddr1x" none) matches .error _
#guard (invoke "napplet:profile/open#notanaddr" {}) matches .error .invalidFragment
#guard (invoke ("napplet:profile/open#" ++ Nip19.encodeNaddr Nip19.sample Nip19.author)
  { handlerHint := some { address := "x" } }) matches .error .fragmentWithHint
#guard match invoke ("napplet:profile/open#" ++ Nip19.encodeNaddr Nip19.sample Nip19.author) {} with
  | .ok f => ((f "i9").get? "request" |>.bind (·.get? "handlerHint") |>.bind (·.getStr? "address")) ==
      some ("35129:" ++ Nip19.sample.pubkey ++ ":my-napplet")
  | .error _ => false
#guard («open» "napplet:feed/edit" {}) matches .error .notOpen
#guard match emit "shell:state-get" none with
  | .ok j => Json.same j (Json.parse! "{ \"type\": \"inc.emit\", \"topic\": \"shell:state-get\" }")
  | .error _ => false

end Napplet.BindingUri
