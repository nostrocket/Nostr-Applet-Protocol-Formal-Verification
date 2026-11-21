import Napplet.Basic

/-!
# Wire format (NIP-5D §Wire Format)

Every message is a JSON object whose `type` is `domain.action`. Payloads are
left abstract here; each NAP module types its own payloads.
-/

namespace Napplet

/-- An envelope as it crosses the port. -/
structure Envelope where
  type : String
  id : Option String := none
  deriving DecidableEq, Repr

/-- Domain prefix of a `type`, if it names a known domain and has an action. -/
def Envelope.domain? (e : Envelope) : Option Domain :=
  match e.type.splitOn "." with
  | d :: _ :: _ => Domain.ofName? d
  | _ => none

-- `String.splitOn` is not kernel-reducible, so these are checked by evaluation.
#guard ({ type := "relay.publish", id := some "a1" } : Envelope).domain? == some .relay
#guard ({ type := "relay.publish.result" } : Envelope).domain? == some .relay
#guard ({ type := "relay" } : Envelope).domain? == none
#guard ({ type := "NAP-RELAY.publish" } : Envelope).domain? == none

/-- Result type for a request type (`relay.publish` ↦ `relay.publish.result`). -/
def resultType (t : String) : String := t ++ ".result"

end Napplet
