# NAP-RELAY conformance

Upstream: `napplet/naps` PR #2, `naps/NAP-RELAY.md` at `9f30b3505335a52c574ff570576687d6467021ff`.
Lean: `Napplet/Run/Relay.lean` (component), `Napplet/Nap/Relay.lean` (pure model),
`Napplet/Host.lean` §RELAY (host contract), `Napplet/Binding.lean` (napplet shim).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | "Requests include correlation IDs; the shell responds with matching IDs" | API prose | OK | `Run/Relay.lean:169-181` (`pubOk`, `pubFail`, `queryOk`, `queryFail` carry `id`), `:158-164` (`eventMsg`, `eoseMsg`, `closedMsg` carry `subId`) |
| 2 | publishEncrypted: "encrypts ... (NIP-44 by default, NIP-04 as fallback)" | API prose | OK | `Run/Relay.lean:313-314` (`e.getD .nip44`); `Host.lean:166-168` (host MUST NOT fall back on its own) |
| 3 | "`relay.query.result` MAY include an `error` field instead of `events` if the query fails" | MAY | OK | `Run/Relay.lean:180` `queryFail`; used `:316`, `:370-372` |
| 4 | Sidecar: "Shells MAY attach sidecar metadata to any `RelayEventResult`" | MAY | OK | `Run/Relay.lean:154` `resultJson` (relay hints only) |
| 5 | Sidecar "is not part of the Nostr event and MUST NOT be written back into the event" | MUST | OK | `Run/Relay.lean:154` (`sidecar` is a sibling of `event`); theorem `resultJson_no_resources` (`:664`) |
| 6 | "it MAY include them in `sidecar.resources`" | MAY | OPTIONAL | Never performed: README "RELAY" (l.143-145) |
| 7 | "it SHOULD include those relay URLs in `sidecar.relayHints`" | SHOULD | OK | `Run/Relay.lean:276` `hintsOf`; `Cfg.relayHints := true` (`:95`) |
| 8 | Relay hints "MUST NOT bypass shell relay policy, ACL checks, scoped relay validation, or relay selection" | MUST | OK | Hints are output only: no request field carries hints (`decode` `:204`); scoped relays pass `Cfg.scopedAllowed` (`:293`), ACL `Cfg.canRead` (`:292`) |
| 9 | "Conformant shells MUST NOT enable sidecar pre-resolution by default" | MUST | OK | Never enabled: theorem `resultJson_no_resources` (`:664`); pure model `Nap/Relay.lean:262` `sidecar_default_off` |
| 10 | `ResourceSidecarEntry`: "relay ... MUST NOT redefine it" | MUST | OK | No such type is defined in the relay component; `resultJson` carries `relayHints` only |
| 11 | "the shell SHOULD include every relay URL where it observed the event after deduplication" | SHOULD | DECISION | Query: hints merged per id (`merge` `:280`, `finishDecrypt` `:335`). Subscriptions forward each pool event with the relay it came from (`:355`): README "RELAY" (l.143, "relay hints carry the relay an event was observed on") |
| 12 | "it MAY omit `relayHints` or return a policy-derived subset" | MAY | OK | `Cfg.relayHints` (`:95`) |
| 13 | "Napplets MUST treat these as hints, not proof of canonical storage" | MUST | NAPPLET | Constrains napplet code |
| 14 | Shims "MUST hydrate their `resource.bytes` single-flight cache ... BEFORE delivering the event" | MUST | NAPPLET | `Binding.lean:209` (`hydrate` runs before the push is handed to the handler) |
| 15 | "the shim MUST treat the existing cache entry as authoritative and discard the duplicate" | MUST | NAPPLET | `Binding.lean:189` `hydrate` (existing URL wins) |
| 16 | "Conformant shells MUST default sidecar pre-resolution to OFF" | MUST | OK | As row 9 |
| 17 | "Opt-in ... SHOULD be configurable by the user" | SHOULD | OPTIONAL | No pre-resolution exists to configure: README "RELAY" (l.144-145) |
| 18 | Opt-in shells "SHOULD only pre-fetch URLs that match a per-event-kind allowlist" | SHOULD | OPTIONAL | As row 17 |
| 19 | "Shells SHOULD also provide users with control over" kinds, hosts, napplets | SHOULD | OPTIONAL | As row 17 |
| 20 | "Opt-out at any granularity MUST be honored ... MUST receive event results with no `sidecar.resources` ... the fetch MUST NOT have happened" | MUST | OK | No sidecar fetch ever happens (component uses no `Call.fetch`); `resultJson_no_resources` (`:664`); `Nap/Relay.lean:268` `sidecar_opt_out` |
| 21 | Sidecar `mime` "MUST be shell-classified by byte-sniffing"; "MUST NOT populate sidecar `mime` from ... `Content-Type`"; SVG "MUST be rasterized"; "every safety property of `resource.bytes` MUST hold" | MUST | OK | Vacuous: no sidecar resources are produced (row 20) |
| 22 | "The shell MUST forward subscriptions to its relay pool and deliver matching events as `relay.event`" | MUST | OK | `stepReq` `:291-297` (`Call.subscribe`), `stepReply` `:353-356`; `Nap/Relay.lean:238` `delivery_only_matching_subscribers` |
| 23 | "The shell MUST send `relay.eose` when stored events for a subscription are exhausted" | MUST | OK | `stepReply` `:357-359`; held EOSE released after pending decryptions `finishDecrypt` `:330-331` |
| 24 | "The shell MUST honor `relay.close` by tearing down the subscription and ceasing event delivery" | MUST | OK | `stepReq` `:298-300`, `stopSub` `:269`; theorems `close_stops` (`:700`), `close_only_own` (`:693`) |
| 25 | "MUST sign event templates from `relay.publish`, forward the signed event ..., and respond with `relay.publish.result` containing the signed event" | MUST | OK | `stepReq` `:301-306`, `stepReply` `:382-387`, `pubOk` `:169`; theorems `handle_sign` (`:530`), `handle_no_publish` (`:521`), `onReply_publish_signed` (`:510`) |
| 26 | "MUST encrypt content and sign event templates from `relay.publishEncrypted`, forward ..., and respond" | MUST | OK | `stepReq` `:307-314`, `stepReply` `:377-381`; theorems `handle_encrypt` (`:542`), `onReply_sign_encrypted` (`:565`) |
| 27 | "The shell MUST decrypt incoming encrypted events (NIP-04/NIP-44) before delivering them" | MUST | OK | `stepReply` `:353-356`, `:362-365`, `finishDecrypt` `:322`; theorem `onReply_delivers_plaintext` (`:652`); kept `id`/`sig`: README decision 8 |
| 28 | "The shell MUST respond to `relay.query` by collecting event results until EOSE and returning them" | MUST | OK | `stepReq` `:315-317`, `stepReply` `:362-372`, `queryOk` `:176` |
| 29 | "The shell MUST respond to every request with a result or lifecycle message carrying the same `id` or `subId`" | MUST | OK | subscribe → `relay.event`/`eose`/`closed` (`:292-297`, `:353-361`); close → `relay.closed` (`:300`, README decision 9); publish/query → result. Requests without a usable `id`/`subId` are dropped: README decision 31 |
| 30 | "The shell MAY send `relay.closed` to indicate a subscription was terminated by the shell" | MAY | OK | `stepReply` `:360-361`; refusals `:292-294` |
| 31 | "The shell MAY enforce ACL checks on relay read and relay write" | MAY | OK | `Cfg.canRead`/`canWrite` (`:89-91`); theorem `handle_subscribe_read` (`:574`); `Nap/Relay.lean:187` `publish_requires_write` |
| 32 | "The shell MAY support scoped relay connections when the `relay` field is present" | MAY | OK | `stepReq` `:297` (`Call.subscribe fs (some [relay])`) |
| 33 | "The shell MAY manage a relay pool internally" | MAY | HOST | `Host.lean:184-189` (`Call.subscribe … none` is the shell's pool) |
| 34 | "The shell SHOULD include event relay hints in `RelayEventResult.sidecar.relayHints`" | SHOULD | OK | As row 7 |
| 35 | "MAY opportunistically pre-resolve ...; conformant shells MUST NOT enable it by default and SHOULD honor per-napplet / per-kind / per-host opt-out" | MAY/MUST/SHOULD | OK | As rows 6, 9, 20 |
| 36 | Security: "The shell MAY inspect event content before signing and publishing" | MAY | OK | `Host.looksCiphertext` check `:303`, `:309` (README decision 11); `Nap/Relay.lean:172` `no_napplet_ciphertext_broadcast` |
| 37 | "The shell MAY filter or reject subscriptions and publishes based on ACL capabilities" | MAY | OK | As row 31 |
| 38 | "Scoped relay URLs SHOULD be validated by the shell to prevent SSRF-like abuse (e.g. ... internal network addresses via `wss://`)" | SHOULD | OK | Hook `Cfg.scopedAllowed` (`:93`, applied `:293`). Note: the default only requires `wss://`; `wss://10.0.0.1` is accepted (checked by `#eval`) |
| 39 | "Subscription filters SHOULD be validated to prevent resource exhaustion" | SHOULD | OPTIONAL | Not done (filters must only be JSON objects, `filtersOf?` `:185`). Not listed in README "Optional behaviours" |
| 40 | Sidecar pre-resolution "MUST NOT be enabled by default" (Security) | MUST | OK | As row 9 |

Notes

- Row 38: the default `scopedAllowed` does not block private addresses. Upstream says SHOULD, so this is not a
  mismatch. Reusing the OUTBOX fix (see `NAP-OUTBOX.md` row 30) would close it.
- Row 39 is an unquantified SHOULD that the README's list of "Optional behaviours" does not mention. Add
  "RELAY subscription filter limits" to that list.
