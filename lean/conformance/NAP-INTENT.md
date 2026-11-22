# NAP-INTENT conformance

Upstream: `napplet/naps` `naps/NAP-INTENT.md` at `377bf939c6c906817084b43dd21d424de646dbc2`.
Lean: `Napplet/Run/Intent.lean` (component), `Napplet/Nap/Intent.lean` (resolution
precedence, convention URI binding), `Napplet/BindingUri.lean` and `Napplet/Binding.lean`
(napplet side), `Napplet/Basic.lean` (`Identity.catalogId`), `Napplet/Host.lean` §INTENT.

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | "The source names a role and intent, never a target instance unless the user has explicitly authorized one" | normative | OK | Row 47 |
| 2 | "The runtime-provided binding derives the normalized `archetype`, `action`, `convention`, and `payload` fields before sending" | binding | OK (napplet side) | `BindingUri.lean:60-74` `invoke` |
| 3 | `IntentBehavior` fields are hints; "Runtime lifecycle and workspace policy remain authoritative" | schema | OK | `Run/Intent.lean:181-184`; forwarded as hints in `launch`/`focus` effects (421-434) |
| 4 | `IntentHandlerHint.address` required, `relays` optional | schema | OK | `Run/Intent.lean:186-189,282-283` |
| 5 | Address: "The pubkey is exactly 64 lowercase hex digits; the non-empty `d` value is opaque and case-sensitive" | constraint | OK | `Run/Intent.lean:380-387` `addressOk`; `Nip19.lean:131-134` |
| 6 | "Clients MUST NOT normalize `d` or identify a handler by `d` alone" | MUST NOT | OK | `Run/Intent.lean:390-391` `hintId` keeps the whole coordinate; `Basic.lean:129` `catalogId` |
| 7 | "`IntentHandlerHint` accepts kind `35129` only" | constraint | OK (binding) / RESOLVED (was MISMATCH) (runtime, minor) | Binding: `Nip19.lean:133`. Runtime: a wire `handlerHint` whose `address` fails `addressOk` is silently ignored (`hintId` → `none`, `Run/Intent.lean:390-391,401`) instead of rejecting the request as invalid (row 39) |
| 8 | `IntentRequest.archetype`, `.action`, `.convention` required | schema | OK | `Run/Intent.lean:292-297` `requestOf?`; missing → `"invalid convention"` (344) |
| 9 | `IntentContract.convention`, `.params` required | schema | OK | `Run/Intent.lean:251-252` |
| 10 | `IntentCandidate.id`, `.actions`, `.conventions`, `.contracts` required; `title`, `isDefault` optional | schema | OK | `Run/Intent.lean:254-259` |
| 11 | `IntentAvailability` all fields required | schema | OK | `Run/Intent.lean:261-264`, `emptyAvail` (320) |
| 12 | `IntentResult`: `archetype`, `action`, `convention`, `handler` "Required when `ok` is true"; `error` "Required when `ok` is false" | schema | OK | `Run/Intent.lean:307-315` `okJson`, `invokeErr` |
| 13 | `IntentDelivery` `sender`, `archetype`, `action`, `convention` required | schema | OK | `Run/Intent.lean:299-303` |
| 14 | "No intent delivery identifier is exposed" | normative | OK | `deliveryJson` has no id (`Run/Intent.lean:299-305`) |
| 15 | "The binding MUST derive these request fields before sending `intent.invoke`" | MUST | OK (napplet side) | `BindingUri.lean:60-74` |
| 16 | "Query values MUST remain text; `+` is literal. The binding MUST reject malformed percent-encoding, duplicate decoded query names, invalid fragments, query plus `options.payload`, or fragment plus `options.handlerHint`" | MUST | OK (napplet side) | `Nap/Intent.lean:301-312` `bindUri` (theorem `bindUri_ok`, 314); `BindingUri.lean:62-68`; vectors `BindingUri.lean:98-102` |
| 17 | "A fragment MUST satisfy the `IntentHandlerHint` address constraints" | MUST | OK (napplet side) | `Nip19.lean:131-134` (kind 35129, non-empty `d`, valid bech32) |
| 18 | "Only NAP-INTENT invocation accepts fragments; other convention-URI operations MUST reject them" | MUST | OK (napplet side) | `Nap/Intent.lean:303`; theorem `bindUri_ok` (314, `op = .other → handlerHint = none`) |
| 19 | "A queryless URI MAY combine a fragment with `options.payload`" | MAY | OK | `Nap/Intent.lean:306` (only query + payload rejected) |
| 20 | "The runtime MUST reject a request unless `convention` is exactly the queryless, fragment-free `napplet:<archetype>/<action>` matching its `archetype` and `action`" | MUST | OK + RESOLVED (was MISMATCH) (doc, minor) | `Run/Intent.lean:367-368` `convOk`, 454. `convOk` also requires `validIdent` segment characters `[A-Za-z0-9._-]` (`Nap/Intent.lean:217-225`), so e.g. `napplet:emoji~list/open` is `"invalid convention"`; upstream sets no character set and the README does not record this choice |
| 21 | "`open(uri, options?)` ... The URI intent MUST be `open`" | MUST | OK (napplet side) | `BindingUri.lean:77-80` |
| 22 | `onDelivery`: "The runtime supplies `sender`; the source napplet cannot set or override it" | normative | OK | Row 41 |
| 23 | "The runtime-provided binding MUST retain an incoming delivery until an `onDelivery` handler is registered" | MUST | OK (napplet side) | `Binding.lean:54-56,211`; theorems `retained_buffered` (250), `register_delivers_buffer` (241) |
| 24 | "Catalogs MUST recognize its napplet manifest kinds `5129`, `15129`, and `35129`" | MUST | HOST | Catalog contract `Host.lean:355-361` |
| 25 | "For each valid `i` tag, the runtime MUST expose an `IntentContract` whose `convention` is the tag's second element and whose `params` are the remaining elements, in order" | MUST | OK + RESOLVED (was MISMATCH) (minor) | `Run/Intent.lean:164-174` `Entry.contracts`. When one manifest has two valid `i` tags with the same convention, only the first is kept ("first contract per convention", line 163, 173); upstream asks for one contract per valid `i` tag and dedups only `actions`/`conventions`; no README decision covers it |
| 26 | "The convention MUST be a stable, queryless, fragment-free identity. Its archetype segment MUST match a `z` value on the same manifest to be eligible" | MUST | OK | `Run/Intent.lean:156-170` (`parseConv` via `validIdent`, `r ∈ e.roles`, `a = r`) |
| 27 | "Tag order is irrelevant; a runtime MUST NOT associate `i` with the nearest preceding `z` tag" | MUST NOT | OK | `Entry` keeps `z` and `i` as separate lists (`Run/Intent.lean:131-137`) |
| 28 | Trailing `i` values "MUST NOT be interpreted as `kind:<number>` restrictions" | MUST NOT | OK | `params` are only reported (`Run/Intent.lean:142,170`) |
| 29 | "The runtime MUST NOT inspect payload content to infer an event kind or select a handler" | MUST NOT | OK | `invoke` never reads `r.payload` (`Run/Intent.lean:453-467`, `autoCtx` 397-405) |
| 30 | "Missing or unusable advertisements MUST NOT invalidate an otherwise valid napplet manifest" | MUST NOT | OK + HOST | Unusable `i` tags are skipped (`Run/Intent.lean:166-172`); `checkManifest` ignores `z`/`i` validity (`Manifest.lean:267-268`); host sends empty lists (`Host.lean:362-363`) |
| 31 | "Legacy combined `archetype` tags MUST NOT substitute for `z` and `i`" | MUST NOT | OK | Only `z`/`i` are read (`Run/Intent.lean:497-499`; `Host.lean:362-363`) |
| 32 | "Runtimes MUST build `available()` and `handlers()` from these manifest tags. For each role, candidates MUST have at least one eligible contract, and their `contracts` MUST contain only contracts for that role" | MUST | OK | `Run/Intent.lean:237-244` `candidates`, `roles` |
| 33 | "Runtimes MUST derive the candidate's `actions` and `conventions` from those contracts, removing duplicates" | MUST | OK | `Run/Intent.lean:176-179` |
| 34 | "Handler resolution MUST match the requested stable convention by exact equality; it MUST NOT prefix-match, wildcard-match, or normalize" | MUST | OK | `Run/Intent.lean:246-247` `compatible` (`==`) |
| 35 | "The runtime MUST apply the manifest capability requirements and its own policy before accepting delivery" | MUST | RESOLVED (was MISMATCH) | `invoke`/`accept` (`Run/Intent.lean:453-467,437-439`) accept any catalog entry with a matching contract. Catalog entries (`Entry`, 131-137; contract `Host.lean:355-365`) carry no `R` set or exposure, and the host contract does not restrict the catalog to napplets the shell policy would admit with `intent` exposed. A handler whose `R` set the shell cannot meet, or that policy would load without `intent`, still gets `ok: true`; the failure surfaces later as `launchFailed` and the delivery is dropped silently |
| 36 | "Declaring a role or intent MUST NOT widen the domains exposed to the napplet" | MUST NOT | OK | `Capability.lean:33,46` |
| 37 | Catalog identifiers: "callers MUST preserve them exactly and MUST NOT interpret them" | MUST | NAPPLET | — |
| 38 | "callers MUST NOT substitute a hint coordinate for an explicit `handler`" | MUST NOT | NAPPLET | Shell side: an explicit `handler` must be a catalog id of a compatible candidate (`Run/Intent.lean:460-462`) |
| 39 | "The runtime MUST reserve `default` and `choose` for handler selection" | MUST | OK | `Run/Intent.lean:370-375` `selection`; catalog ids are `nip5d:…` (`Basic.lean:129-133`) |
| 40 | "Identifiers MUST distinguish publishers and manifest kinds"; named by publisher+kind+`d`; root by publisher+kind; snapshots by event id; updates preserve id; distinct snapshots distinct; no bare `d` | MUST | OK | `Basic.lean:120-133` `Identity.key`, `catalogId`; `Component.lean:59` |
| 41 | "The runtime MUST also assign an identifier to the source ... It MUST derive `sender` from the source's verified manifest bound to its authenticated endpoint" | MUST | OK | `Ctx.catalogId` (`Component.lean:59`) used at `Run/Intent.lean:447,461-467`; theorem `handle_sends` (684, `d.sender = cx.catalogId`); `ctx_verified` (`Runtime.lean:1240`) |
| 42 | `intent.deliver` "has no request or delivery id"; binding buffers it | wire | OK | Rows 14, 23 |
| 43 | "Delivery uses the same `IntentDelivery` shape whether the target was already running or started" | wire | OK | `deliverJson` in both `place` (428) and `flush` (`Run/Intent.lean:534-536`) |
| 44 | "The runtime MUST reject an invocation before acceptance when the convention URI or normalized request is invalid, no compatible handler exists, policy denies the request, or the user cancels handler selection" | MUST | OK (except row 7) | `Run/Intent.lean:344,454-456,462,474-477`; `"invalid convention"`, `"no handler"`, `"unsupported convention"`, `"invoke rejected"`, `"user cancelled"` |
| 45 | "A post-acceptance failure is not reported as a second result to the source" | normative | OK | `launchFailed` drops the queue silently (`Run/Intent.lean:527-530`) |
| 46 | "The runtime MUST derive the source `sender` from the authenticated endpoint. It MUST ignore or reject caller-supplied sender data" | MUST | OK | `requestOf?` ignores unknown members (`Run/Intent.lean:292-297`); row 41 |
| 47 | "The runtime MUST validate normalized `archetype`, `action`, and `convention` consistency before handler resolution" | MUST | OK | `Run/Intent.lean:454` (first check) |
| 48 | "The runtime MUST keep a user-overridable default per archetype. A napplet cannot set or change it" | MUST | OK + HOST | `St.defaults` (`Run/Intent.lean:226`), set only by `HostEvent "default"` (521-526); theorem `handle_prefs_unchanged` (644); persistence `Host.lean:46-49,366-370` |
| 49 | "The runtime SHOULD offer a chooser when `handler` is `choose`, or when several candidates exist and no default is set" | SHOULD | OK | `Run/Intent.lean:463,467` (`autoCtx.fallback` is `none` unless exactly one compatible candidate, 403-405) |
| 50 | "The runtime MUST resolve an installed handler using manifest contracts and the user's default-handler preference" | MUST | OK | `Run/Intent.lean:397-405,465`; theorem `default_accepted` (749) |
| 51 | "The runtime MUST respond to `intent.invoke` with the same request `id`" | MUST | OK + DECISION | Every path sends `invokeErr id`/`okJson id` (`Run/Intent.lean:453-493`); prompt paths answer from `onReply`; no string `id` → dropped (decision 31); source torn down during a prompt → prompt cancelled (538-540) |
| 52 | "An `ok: true` result MUST mean the runtime accepted delivery responsibility" | MUST | OK (but see row 35) | `accept` always places or retains the delivery (`Run/Intent.lean:425-439`) |
| 53 | "Before closing the source because of an invocation, the runtime MUST send its `intent.invoke.result`" | MUST | OK | The runtime never closes a source; the result precedes the delivery (`Run/Intent.lean:437-439`) |
| 54 | "After acceptance, the runtime MUST retain the normalized delivery independently of the source until ... delivery succeeded or failed terminally" | MUST | OK | `St.queue` (`Run/Intent.lean:229,432`); theorems `drop_keeps_queue` (785), `flush_retains` (779) |
| 55 | "After acceptance, delivery MUST NOT depend on the source remaining alive" | MUST NOT | OK | Row 54 (`drop` never touches `queue`) |
| 56 | "The runtime MUST deliver `IntentDelivery` only after the target is ready" | MUST | OK | `target?` requires a live bound endpoint with `intent` exposed (`Run/Intent.lean:418-419`); theorems `target?_spec` (657), `place_sends` (666), `flush_sends` (769) |
| 57 | "The runtime MAY reuse an existing target, briefly overlap source and target, or close the source" | MAY | OK | `place` reuses a live target (`Run/Intent.lean:426-430`) |
| 58 | "`behavior` fields are hints" | normative | OK | Row 3 |
| 59 | "The runtime MUST source `available()` and `handlers()` from verified installed NIP-5D manifests, not only running instances" | MUST | OK + HOST | Catalog from `HostEvent "catalog"` (`Run/Intent.lean:515-520`); contract `Host.lean:355-365` |
| 60 | "The runtime MUST NOT let a caller address a handler instance unless the user explicitly authorized that handler" | MUST NOT | OK | `Run/Intent.lean:459-462` (`authorize` prompt), `replyCtx` (408-415); decision 7 |
| 61 | "The runtime MUST reject an unsupported convention before acceptance" | MUST | OK | `Run/Intent.lean:456` |
| 62 | "The runtime SHOULD emit `intent.changed` when catalog or default-handler state changes" | SHOULD | OK | `Run/Intent.lean:510-526` `pushChanged` (endpoints with `intent` exposed) |
| 63 | Precedence: "The shell MUST apply this precedence: 1. explicit/`choose` 2. default 3. recommendation 4. normal resolution" | MUST | OK | `Nap/Intent.lean:53-62` `resolve`; `Run/Intent.lean:458-467`; theorems `default_wins` (`Nap/Intent.lean:71`), `unusable_recommendation_falls_back` (76) |
| 64 | "Absent `handler` and `handler: \"default\"` both use steps 2–4" | normative | OK | `Run/Intent.lean:372-373` |
| 65 | "An explicit selection MUST NOT silently fall back to the recommendation" | MUST NOT | OK | `replyCtx` has no recommendation (`Run/Intent.lean:413`); theorems `explicit_no_fallback` (`Nap/Intent.lean:65`), `explicit_reply_target` (`Run/Intent.lean:728`) |
| 66 | "Support MUST come from its verified catalog metadata, not from the hint itself" | MUST | OK | `recommendationUsable` = membership in `compatible` (`Run/Intent.lean:402`) |
| 67 | "At step 3 the shell SHOULD consider a compatible installed recommendation" | SHOULD | OK | `Cfg.hints` default `true` (`Run/Intent.lean:126,401`) |
| 68 | "If it is not installed, the shell MAY resolve its signed event ... and offer installation" | MAY | OPTIONAL | Not offered; README "Optional behaviours" and INTENT paragraph |
| 69 | "The shell MUST verify the resolved event's signature and exact coordinate ... MUST apply its ordinary installation, artifact verification, and execution rules" | MUST | OK (vacuous) | No discovery is performed (row 68) |
| 70 | "The hint MUST NOT alter the user's default" | MUST NOT | OK | theorem `handle_prefs_unchanged` (`Run/Intent.lean:644`) |
| 71 | "An unavailable, unsupported, declined, or policy-denied recommendation MUST fall back to step 4" | MUST | OK | theorem `unusable_recommendation_falls_back` (`Nap/Intent.lean:76`); `autoCtx` (`Run/Intent.lean:397-405`) |
| 72 | "A shell MAY ignore the recommendation under its policy" | MAY | OK | `Cfg.hints := false` |
| 73 | "Relay hints are untrusted discovery inputs and MUST NOT bypass the shell's network policy" | MUST NOT | OK (vacuous) | Relay hints are never used (row 68) |
| 74 | "The runtime SHOULD rate-limit or require a user gesture according to policy" | SHOULD | OPTIONAL (not listed) | Not modelled; README does not list invocation rate limits |
| 75 | "The runtime MUST derive `sender`; a napplet cannot impersonate another source" | MUST | OK | Row 41 |
| 76 | "The target MUST validate `payload` against `convention`" | MUST | NAPPLET | — |
| 77 | "Only installed manifest contracts, user defaults, or explicit user choice may select a target" | normative | OK | `resolve` inputs (`Run/Intent.lean:397-415`); the recommendation is admitted only if it is an installed compatible candidate |
| 78 | "Default-handler state belongs to the user. A napplet MUST NOT change it" | MUST NOT | OK | Row 48 |
| 79 | "The runtime MAY redact candidate details according to policy" | MAY | OK | Not done (allowed) |
| 80 | "Delivery MUST NOT leak payload or sender metadata to any napplet other than the resolved target" | MUST NOT | OK | theorems `handle_sends` (`Run/Intent.lean:684`), `onReply_sends` (706), `place_sends` (666), `flush_sends` (769); `invoke_single_delivery` (`Nap/Intent.lean:139`) |
