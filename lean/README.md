# Napplet protocol: Lean 4 model

A machine-checked, executable model of a napplet shell: the NIP-5D core, all
nineteen live NAPs, the JSON wire codec, the composed runtime that ties them
together, the host interface, and the napplet-side bootstrap and binding.
818 theorems and 511 evaluated vectors (92 of them end to end through the
composed runtime). Section numbers refer to [`../NAPPLETS-SPEC.md`](../NAPPLETS-SPEC.md),
but the model was built from the upstream texts at the commits listed below.

- Lean `v4.36.0`, no Mathlib, no dependencies.
- No `sorry`. Proofs use only Lean's standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`). No `native_decide`.
- Every definition is computable, so the model runs as a test oracle
  (`Napplet/Test/Harness.lean`).
- Coverage against upstream: every one of the 177 type strings in the 19 NAP wire
  tables is decoded or produced by its component; all 91 JSON request examples in the
  NAP specs decode (`Napplet/Test/UpstreamExamples.lean`); `Napplet/Test/E2E.lean`
  feeds upstream example JSON for every NAP through `Runtime.step`. All 118 JSON
  response examples in the NAP specs are reproduced verbatim by guards
  (`scripts/response_coverage.py`). The INC examples run under a shell policy that names
  endpoints and channels as upstream assumes (`Config.endpointName`,
  `Run.Inc.Cfg.channelName`; NAP-INC: "Identifier encoding is runtime policy"), and the
  CVM registry examples with the optional registry enabled.
3. **`hello` naming a port already bound to another frame.** This is not covered by
   the spec. The model drops it, which the invariant needs, because a port must
   belong to at most one window.
4. **Window ids are never reused.** This follows from "MUST NOT re-bind an identity to
   an existing iframe". The model makes `create` on any known window a no-op.
5. **Unknown names in `R`.** These are treated as missing required domains.
6. **INC `channel.open` to oneself.** This is not covered by the spec. The model
   rejects it as `"target not found"`.
7. **INTENT explicit handler that is not authorised.** The runtime asks the user
   (`Call.prompt .intent "authorize"`); a refusal or an incompatible handler gives
   `"invoke rejected"` (kehto's string), and it never falls back to a recommendation.
   (The pure `NapIntent.resolve` still returns no handler for an unauthorised
   explicit selection.)
8. **RELAY: decrypted delivery keeps the original `id` and `sig`.** The model
   delivers the event with `content` replaced by plaintext, as the spec says. The
   result is an event whose signature no longer verifies. This is the open
   review issue on napplet/naps#2. A `view` form would fix it.
9. **RELAY `relay.close` reply.** The spec defines none. The model replies with
   `relay.closed`. A refused `subscribe` also gets `relay.closed` with
   `"policy denied"`.
10. **RELAY: reusing a `subId`.** The new subscription replaces the caller's
    previous one with that `subId`. Subscriptions are namespaced per endpoint, so
    one napplet cannot close another's.
11. **RELAY ciphertext detection.** NIP-5D forbids signing ciphertext a napplet
    supplies, but gives no test for it. The model uses an opaque
    `looksCiphertext` predicate on the napplet-supplied content. For
    `publishEncrypted`, it checks the plaintext before the shell encrypts.
12. **RESOURCE address classes.** The spec lists RFC1918, loopback, link-local,
    ULA and 169.254.169.254. The model also blocks CGNAT (100.64/10),
    unspecified addresses (0/8 and `::`), broadcast, and IPv4-mapped IPv6.
13. **RESOURCE: duplicate in-flight request ids.** These are not covered by the
    spec. The model ignores the duplicate, so each accepted request gets exactly
    one terminal envelope.
14. **OUTBOX: unresolved `toInboxes` authors.** The model still publishes to every
    resolved relay. It lists unresolved authors in `missing` with
    `"relay list unavailable"`, and never substitutes fallback relays for them.
    The spec allows "include … or report failure" but does not say whether to
    publish at all.
15. **OUTBOX: own write set when NIP-65 is unavailable.** The model uses the
    fallback relays. The spec permits this for the user's own write set only.
16. **UPLOAD: MIME policy.** The model checks the shell's sniffed type, not the
    napplet-supplied `mimeType`. The spec does not say which the policy uses.
17. **UPLOAD: when consent is asked.** The model prompts on the first upload that
    passes every other check, and remembers approval per napplet. The spec says
    SHOULD and is otherwise silent.
18. **VALUE: allowance debit timing.** The model debits a covering allowance when
    it authorises the payment, before the backend replies, and does not refund a
    failed payment. This is conservative: budget is never double-spent. Whether
    failures should refund is unspecified.
19. **VALUE: allowance and consent.** A covering allowance replaces the prompt.
    Without one, the user is asked. A request no allowance covers is never
    partially charged against one.
20. **KEYS: modifier order.** The spec calls `Alt+Ctrl+Shift+Meta` "alphabetical",
    but it is not alphabetical (the open review issue). The model uses the stated
    order, and parses modifiers in any order to one canonical form. The key segment
    is compared exactly, so reserved Ctrl+W/T/L are listed in both cases.
21. **KEYS: conflicting `defaultKey`.** The spec says the shell MAY bind. The model
    leaves an action unbound if its hint is reserved or already bound, so no combo
    is ever bound twice.
22. **MEDIA: initial state.** After a successful create, the model starts a session
    `stopped`. The spec does not define the first state (open review issue).
23. **MEDIA: focus pause and user pause.** The model records that focus loss
    paused a session. A later user or napplet pause clears that, so focus regain
    never resumes it.
24. **NOTIFY: who may dismiss.** The spec says only to ignore unknown ids. The
    model also ignores ids owned by another napplet.
25. **LINK: `blocked-by-policy` vs `user-denied`.** A persisted deny rule gives
    `blocked-by-policy`. A declined prompt gives `user-denied`. The open review
    question is whether to pass the shell's own reason through instead.
26. **CONFIG: invalid defaults.** The model delivers a declared default only if it
    validates, consistent with "validate every value before delivery".
27. **CVM: payment price.** Price is an input. CEP-8 negotiation is not modelled,
    nor are the `-32042` interception mechanics.
28. **POW: timeout.** A search that returns a nonce failing the target is treated
    as a timeout. The shell never returns a result below target.

### Decisions added with the wire codec, composition and coverage

Shared:

29. **Repeated JSON members.** The last member with a name wins, as in browser
    `JSON.parse` (`Json.get?`).
30. **Event templates.** Upstream types templates as open maps. The shell reads
    NIP-01 fields only: `kind` is required, `content` defaults to `""`, `tags` to `[]`
    and `created_at` to the shell clock; other members are dropped before signing.
31. **Malformed requests.** A known type with a malformed payload and a string `id`
    gets its result envelope with the NAP's own error string where upstream defines
    one for invalid input, else `"invalid request"`. Without a usable `id`, or for
    fire-and-forget types, it is dropped. Unknown types are always silently ignored.
    This matches kehto's practice.
32. **Request ids on the napplet side.** The SDK uses `crypto.randomUUID()`; the model
    uses a counter. Only freshness among pending requests matters.
33. **Endpoint and catalog identifiers.** INC endpoint ids default to
    `endpoint-<window>` (window ids are never reused) and channel ids to `c-<n>`; a
    shell may name them instead (`Config.endpointName`, `Run.Inc.Cfg.channelName`),
    under the contract that names are injective and never take the default form.
    Catalog ids use kehto's `nip5d:<kind>:…` encoding.
34. **Async host work.** Network, signer, prompts, wallet, storage servers, mining and
    ContextVM are host calls with tagged replies; a reply whose tag the runtime no
    longer holds (teardown, cancel) has no effect. Prompts never block other inputs.

INC: subscriptions are a set per (endpoint, topic), so `inc.unsubscribe {topic}`
removes it; channel ids are `c-<n>`; an open to an unknown, non-live, self or
`inc`-unexposed target fails with `"target not found"`, ACL refusal with
`"target denied"` and a channel cap with `"channel limit reached"` (kehto); endpoint
destruction sends `"peer destroyed"` to the surviving peer only.

INTENT: unknown request members (including any `sender`) are ignored; a malformed
`request` gets `{ok:false, error:"invalid convention"}`; `"no handler"` when no
candidate serves the role, `"unsupported convention"` when candidates exist but
none matches; a hint address maps to the catalog id `nip5d:<address>`; one
compatible candidate is used directly, several prompt a chooser; a default applies
only if it supports the convention; accepted deliveries are retained FIFO until a
target with that catalog id is bound (`Effect launch`), or the host reports
`launchFailed`. Uninstalled-recommendation discovery (MAY) is not offered.

RELAY: `relay.close` and a refused `subscribe` reply `relay.closed` (decision 9,
also kehto); a refused query replies `{id, error:"policy denied"}`; scoped relay
URLs must be `wss://` (`"invalid relay destination"`, kehto); `relay.eose` and the
query result wait for in-flight decryptions of stored events; relay hints carry the
relay an event was observed on; sidecar byte pre-resolution is never performed (a
MAY; this satisfies default-off and every opt-out). Error strings not defined
upstream follow kehto (`"no signer configured"`, `"publish failed"`, `"relay query
closed"`).

OUTBOX: reads route to the authors' allowed NIP-65 write relays, else fallback
relays, plus allowed napplet hints, with `incomplete:true` when a list is missing;
`resolveRelays` reports `source` `nip65` or `fallback` and an empty `policy` plan on
error; an empty publish plan is `ok:false` with `"relay list unavailable"`;
`outbox.close` replies `outbox.closed`; `timeoutMs` is enforced by the host closing
the stream; the NIP-5D ciphertext check also applies to `outbox.publish`.

RESOURCE: wire blobs are strict canonical base64 (non-canonical rejected); `data:`
URLs are decoded in the model; duplicate in-flight ids are ignored (decision 13);
at most 10 URLs per endpoint are in flight, the rest queue; the per-minute rate
limit has no upstream error code and is not modelled; `resource.info.error` only
when the shell does not disclose schemes; `htree` identifiers must be `npub` or
64-hex (aliases rejected), and `nostr:` accepts only non-secret NIP-19 entities.

UPLOAD: the structured-clone `Blob` is modelled as its byte list (a JSON array of
bytes); a declined consent is a `cancelled` result per upstream's example; errors
before an upload exists are top-level (upstream's open issue); `"unknown upload"`
for an unknown status id (kehto); uploads up to 1 MiB answer `complete` directly,
larger ones `uploading` then push; success requires the server's hash to match the
bytes sent (`"server rejected"` otherwise).

LINK: a missing URL is `invalid-url`; `http`/`https` without a host is
`invalid-url`; with prompting off or too many outstanding prompts the answer is
`blocked-by-policy`; the scheme is re-checked when the prompt is answered; rules
are keyed by manifest key and a deny rule wins.

NOTIFY: only the wire names `notify.channel.register` and
`notify.permission.request` are decoded (upstream's API table also says
`registerChannel`/`requestPermission`); permission is required by default and
lasts for the endpoint's lifetime; ids are `shell-<n>`; more than three actions are
truncated (MAY limit); `notify.controls` is pushed once per endpoint; a malformed
`permission.request` gets `granted:false`.

DISPLAY: device access is denied unless policy permits; checks run `not-found`,
`unavailable`, `denied`, then the batch; a missing `displayId` is
`"invalid request"`.

KEYS: single-character keys are upper-cased before matching (`Ctrl+s` matches a
`Ctrl+S` binding; upstream's examples use both, kehto upper-cases); a trailing `++`
is the `+` key; re-registering an action id is `"duplicate action ID"` (kehto
replaces); an unparseable `defaultKey` is `"invalid action"`; a forwarded combo that
is bound also fires `keys.action` to the owner.

MEDIA: creation errors are decided synchronously; later backend failures retire the
session with reason `error`; a napplet's session id hint is honoured if fresh and not
`shell-` prefixed; ids are never reused in a runtime session; out-of-range numbers
are dropped; caller reasons on commands are replaced by `user`; a napplet-owned
session that cannot pause on focus loss is retired with `policy`; a failed create
result echoes the napplet's preferred `sessionId` when it gave one (upstream's
example; the field is required only on success).

CONFIG: a rejected schema gets the correlated `config.registerSchema.result` and the
`config.schemaError` push upstream requires ("pushes `config.schemaError` messages when
it rejects a `registerSchema` call"), with the same code and error;
unknown standard keywords are `invalid-schema`; `$schema` may be draft-07, 2019-09 or
2020-12; a lower version is `version-conflict`; defaults resolve persisted → own
default → ancestor default, invalid candidates skipped (decision 26); secrets
resolve only from a persisted value; orphaned properties are pruned when a schema is
accepted; schemas persist per scope; `openSettings` without a schema is ignored.

VALUE: errors before a transfer exists are top-level (upstream's wire table marks
`result` required); preimages are not disclosed by default (upstream says both
"keep out of the sandbox" and "when safe to disclose"); `"transfer not found"` for
an unknown status id (kehto); a zero amount is out of policy; a zap target needs a
pubkey or address.

CVM: each network operation has a host timer for its deadline; payment gates
return to the shell as an offer and are settled only after `decidePay`; payments
are off by default (`"payment required"`); the registry is off by default
(`"unsupported method"`, `registry.has` → `false`); only server notifications and
requests become `cvm.event`.

POW: FIFO scheduling (priority reported, not used); rejections carry
`state:"error"`; the host's nonce is re-checked in the shell and a miss is
`"timeout"` (decision 28); `pause`/`resume` without `jobId` act on the whole miner;
publish asks for consent by default; NIP-01 ids and leading-zero bits are computed in
the model.

## Not modelled yet

- The deferred CLASS and CONNECT tracks.
- Behaviour upstream leaves undefined (each with the upstream text that leaves it
  open, and what the model does instead, so an implementer needs nothing more):
  - NAP-MEDIA §Shell Behavior: `source` is required "unless the shell defines a
    separate out-of-band source binding", and no such binding is defined. The model
    defines none: a shell-owned create without `source` is `"missing source"`.
  - NAP-RELAY says to decrypt "incoming encrypted events (NIP-04/NIP-44)" and never
    mentions NIP-59 gift wraps (kind 1059 appears only in the privacy text), so how
    deep to unwrap is undefined. The host's `encryptedWith`/`decrypt` contract
    decides, per NIP-17/NIP-59.
  - NAP-RESOURCE §Sidecar Pre-Resolution: "Concrete carrier attachments are deferred
    to the importing spec changes." The model never sends sidecar resources.
  - NAP-UPLOAD lists the state `cancelled` but defines no cancel operation or wire
    message. The model has nothing to receive; `cancelled` arises only from a declined
    consent prompt.
  - Paged `relay.query` (`stream: true`) appears only in review discussion, not in the
    NAP-RELAY text. The model's `relay.query` returns one result.

Optional behaviours the model leaves out on purpose (all MAY or unquantified SHOULD):
INC `shell:*` topic interception and emit ACLs, INTENT discovery of uninstalled
recommendations, RESOURCE single-flight caching and per-minute rate limits, MEDIA
promoted (detached) playback, CONFIG's `config.settingsOpened` acknowledgement and
`$version` migration across artifact hashes.

## Licence

[Mozilla Public License 2.0](../LICENSE).
