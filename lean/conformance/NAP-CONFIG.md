# NAP-CONFIG conformance

Upstream: `napplet/naps` PR #14, branch `nub-config`, `naps/NAP-CONFIG.md` at
`bed9cb5b1e7c9b5babee8870aa18b12949af1d62`.

Lean: `Napplet/Run/Config.lean` (component), `Napplet/Nap/Config.lean` (pure model),
`Napplet/Host.lean` §CONFIG (lines 270-294). "README" means `lean/README.md` (decision 26
and the CONFIG paragraph).

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | Depends: "the runtime MAY persist configuration through storage internally" | MAY | OK | `St.schemas`/`St.values` are their own persistent state (Host.lean:293-294) |
| 2 | "callers MUST register a schema before requesting values" | MUST | NAPPLET | Shell answers `no-schema` otherwise (#36) |
| 3 | `subscribe`: "The shell MUST deliver an immediate initial `config.values` push on subscription" | MUST | RESOLVED (was MISMATCH) (uncovered conflict) | `handle .subscribe` :602 → `deliver` :568. With a schema whose root `required` property has no persisted value and no default, `snapshot` is `none` and the shell pushes `config.schemaError {code:"invalid-schema"}` instead of values. Checked: the root schema `required:["a"]` with `a` a string and no default gives schemaError. Upstream conflicts here with "Every `config.values` ... MUST contain only values that validate". The model's choice is reasonable but is not a README decision. See C1 |
| 4 | "The reference shim implementation SHOULD ref-count local subscribers" | SHOULD | NAPPLET | Not modelled in `Binding`/`BindingApi` |
| 5 | `onSchemaError`: "The shell pushes `config.schemaError` when it rejects a `registerSchema` call or cannot validate a registered schema" | (normative) | OK | `handle .registerSchema` :593-596 (correlated result plus push, same code and error); README CONFIG paragraph |
| 6 | `openSettings`: "the section MUST be declared via `x-napplet-section`" | MUST | NAPPLET + OK | Shell passes `section` on only if declared (`handle .openSettings` :612) |
| 7 | `schema` accessor returns the last accepted schema or `null` | (local) | NAPPLET | Not modelled (local read) |
| 8 | Identity Scope: "The runtime MUST derive scope from the authenticated endpoint's verified manifest and artifact" (publisher, kind, `d` / event id, plus `artifactHash`) | MUST | OK | `scopeOf` :557 = `NapStorage.scopeFor cx.storage .shared` (`Nap/Storage.lean:56`): `Identity.key` (`Basic.lean:120`: named = publisher + `d`, root = publisher, snapshot = event id; kind is the constructor) plus `artifactHash`; `Ctx.ofBinding` from the verified binding |
| 9 | "A bare `d` value MUST NOT identify a scope" | MUST | OK | `ManifestKey.named publisher d` (`Basic.lean:122`); vector :1058 (same `d`, different publisher, isolated) |
| 10 | "A napplet MUST NOT supply or override manifest or artifact identity fields in a request" | MUST | OK / NAPPLET | `decode` :124 reads no identity field; scope comes only from `cx` |
| 11 | "Different publishers, manifest keys, and artifact hashes MUST remain isolated" | MUST | OK | theorem `handle_isolated` :886; `push` :584 only to endpoints with `scopeOf c = sc` (`push_spec` :792) |
| 12 | `config.registerSchema` positive ACK: "every call receives a `config.registerSchema.result`" | (normative) | OK | `handle .registerSchema` :589 (both branches); malformed with `id` :132; without a string `id` dropped (README decision 31) |
| 13 | "`config.subscribe` MUST produce an immediate initial `config.values` push before any value-change pushes" | MUST | OK / RESOLVED (was MISMATCH) | Ordering is OK: the push is sent in the subscribe step, before any later `edited`. Missing values: see #3 / C1 |
| 14 | `config.unsubscribe`: "iframe unmount also implicitly unsubscribes" | (normative) | OK | `drop` :640; theorem `drop_clears` :915 |
| 15 | "Shells and napplets MUST agree on a bounded subset" | MUST | OK | `allowedKeys` :330, `keyError` :341, `decodeNode` :421 |
| 16 | "Every conformant shell MUST accept and render schemas that use only the types, keywords, and constraints enumerated below" | MUST | RESOLVED (was MISMATCH) (partial) | `decodeNode` :421 / `leafOf` :397 reject some schemas built only from Core keywords: `enum` on `array` (`"enum does not apply to type array"`), `minimum`/`maximum` on non-numeric and `minLength`/`maxLength` on non-string types (`absent` checks :399-402), and a schema-valued `additionalProperties` (:445-447). All checked. See C3. Rendering: HOST (Host.lean:274-284) |
| 17 | "Napplets MUST NOT rely on any feature outside this subset" | MUST | NAPPLET | — |
| 18 | "The schema root MUST be `{ "type": "object", "properties": { ... } }`" | MUST | OK | `rootCheck` :504 (`invalid-schema`, "schema root must be of type `object`"). A missing `properties` is accepted as an empty object |
| 19 | Arrays homogeneous only; tuple `items` not in Core | (normative) | OK | `decodeNode` :465 (`invalid-schema`); vector :1086 |
| 20 | Nested object, "Recommended maximum depth is 4" | (normative) | OK | `Schema.depth` :199 counts the root as 1; vectors :1089-1090 |
| 21 | `enumDescriptions`: "shells SHOULD render each description alongside its enum value" | SHOULD | HOST | `annotationsOk` :389 checks the parallel shape; raw schema to host (`openSettings` effect) |
| 22 | "Shells MUST treat `additionalProperties` as `false` at the top-level schema object when the napplet does not specify it" | MUST | OK | Undeclared members are never delivered at any level (`Schema.valid` :254, `Props.resolve_declared` :700, `snapshot_declared` :761) and pruned on store (`pruneRoot` :587) |
| 23 | Default resolution: "the shell MUST resolve its value in the following order" (persisted-if-valid, own `default`, ancestor `default`, undefined) | MUST | OK | `Schema.resolve` :280 (`firstOk` over persisted ++ own ++ ancestors); theorems `default_resolution` :735, `own_default_first` :742, `Schema.resolve_valid` :657. Invalid candidates skipped: README decision 26 |
| 24 | Potentialities: "Shells MAY act on them; shells MAY ignore them" | MAY | OK / HOST | Passed in the raw schema to the host |
| 25 | "Shells that do not recognize an extension MUST treat it as opaque metadata and MUST NOT reject the schema on that basis" | MUST | OK | `keyError` :345 admits every `x-napplet-*` key; vector :1092 (`x-napplet-future: {}`) |
| 26 | `x-napplet-secret` MAY mask / suppress logs / no default / keychain | MAY | HOST | Host.lean:282-284, :294 |
| 27 | `$version`: "Shells MAY use `$version` ...; MAY ignore it" | MAY | DECISION | Non-decreasing check (`register` :536-540, `version-conflict`); README CONFIG paragraph. Migration is in README "Optional behaviours" |
| 28 | "Napplets MUST NOT receive values that violate the currently-registered schema at `config.values` delivery time" | MUST | OK | `snapshot_valid` :757, `deliver_values` :778, `push_spec` :792, `handle_values_valid` :854; re-registration pushes the new snapshot (`handle` :600) |
| 29 | Exclusions: `pattern`, `$ref` (all forms), `definitions`/`$defs`, `oneOf`/`anyOf`/`allOf`/`not`, `if`/`then`/`else`, `patternProperties`, `propertyNames`, `dependencies`, `dependentSchemas`, `unevaluatedProperties`, tuple arrays | (normative) | OK | `keyError` :341, `excludedKeys` :337, `decodeNode` :465; vectors :1083-1086, :1040 |
| 30 | "Shells MAY support [combinators] as an Extended Subset, but napplets MUST NOT rely on them" | MAY / MUST | OK / NAPPLET | Not supported (rejected `invalid-schema`) |
| 31 | Expression-valued defaults: "Napplets needing runtime-generated defaults MUST handle the `undefined` case" | MUST | NAPPLET | Defaults are literal JSON |
| 32 | "Shells MUST reject any schema that declares both [`x-napplet-secret: true` and `default`] on the same property with `code: "secret-with-default"`" | MUST | RESOLVED (was MISMATCH) (partial) | String properties: OK (`decodeNode` :478-479, `checkTree` :488; vector :1087). Non-string properties: `decodeNode` :438, :461, :477 throw `invalid-schema` ("`x-napplet-secret` applies only to strings") first. Checked: `{type:"integer", x-napplet-secret:true, default:1}` gives `invalid-schema`. See C2 |
| 33 | Format: "shells MAY use `format` to pick an input widget but MUST NOT reject a value solely because it fails the `format`" | MAY / MUST | OK | `Leaf.ok` :237 ignores `format`; Host.lean:280 ("`format` only as a widget hint") |
| 34 | "Napplets requiring strict validation MUST use `enum`, `minLength`, ... NOT `format`" | MUST | NAPPLET | — |
| 35 | "Shells MUST reject schemas nesting `object` properties more than 4 levels deep ... `schema-too-deep`" | MUST | OK | `decodeNode` fuel :422, `checkTree` :487; `register_accepts_only_core` :824; vector :1089. Counting the root as level 1 is the model's reading (upstream does not say whether the root counts) |
| 36 | "Napplets MUST NOT assume arbitrary nesting is supported" | MUST | NAPPLET | — |
| 37 | MUST "Validate every value before delivery ... Invalid values MUST NOT be delivered" | MUST | OK | as #28; an invalid edit is ignored (`edited` :629-630) |
| 38 | MUST "Apply declared defaults" | MUST | OK | as #23 |
| 39 | MUST "Use the verified identity scope ... A napplet cannot read or write outside its own scope" | MUST | OK | as #8-#11 |
| 40 | MUST "Be the sole writer ... No napplet->shell wire message mutates persisted values" | MUST | OK | theorem `sole_writer` :900; values are written only by the host `edited` event (:618) and orphan pruning on registration; `config.set` is unknown (vector :1031) |
| 41 | MUST "Mask `x-napplet-secret: true` fields (Tier 0): mask input, do NOT include the default, and do NOT deliver the property ... if never explicitly set" | MUST | OK + HOST | Not delivered unless persisted: `Schema.resolve` :282 (`if sec then p.filter l.ok`), theorem `Props.secret_unset` :715, vector :1099 (an ancestor default never supplies it). Masking, no default shown: Host.lean:282-283 |
| 42 | "napplets MUST NOT set `default` on such fields" | MUST | NAPPLET + OK | Shell rejects (#32) |
| 43 | MUST "Reject schemas exceeding the depth limit" | MUST | OK | as #35 |
| 44 | MUST "Reject schemas with forbidden features ... with `ok: false` and an appropriate code" | MUST | OK | as #29 (`ref-not-allowed`, `pattern-not-allowed`, `invalid-schema`) |
| 45 | MUST "Reject `x-napplet-secret: true` coexisting with `default`" (`secret-with-default`) | MUST | RESOLVED (was MISMATCH) (partial) | as #32 (C2) |
| 46 | MUST "`config.subscribe` MUST NOT deliver its first `config.values` until the most recent `config.registerSchema` from the same source has been fully applied" | MUST | OK | Registration is applied in the step that handles it (`handle` :597-600); atomic steps (Host.lean:39-41) |
| 47 | "If subscribe arrives before any schema has been registered, shells MUST emit `config.schemaError` with `code: "no-schema"`" | MUST | OK | `deliver` :570; theorem `no_schema_error` :847 |
| 48 | MUST "Drop orphaned properties ... MUST NOT be delivered. For secret properties, orphaned values MUST be deleted immediately on schema change" | MUST | OK | `pruneRoot` on every accepted registration (`handle` :599) deletes all orphans, secret or not, at every level (`Schema.prune` :305); `snapshot_declared` :761 |
| 49 | SHOULD group by `x-napplet-section`, sort by `x-napplet-order`, surface `deprecationMessage`, render `markdownDescription` as markdown "Never render as HTML" | SHOULD | HOST | Host.lean:277-280 |
| 50 | SHOULD "Coalesce rapid value changes" (~100 ms) | SHOULD | HOST | Host.lean:286 |
| 51 | SHOULD "Drop non-secret orphans after a grace period" | SHOULD | OK | Dropped immediately on schema change (stricter, allowed) |
| 52 | SHOULD "Honor `config.openSettings` for focused napplets ... Rate-limit repeated requests" | SHOULD | HOST | Host.lean:281-282 |
| 53 | MAY Tier 2+ secret handling | MAY | HOST | Host.lean:294 |
| 54 | MAY richer `format` widgets; "MUST NOT fail validation on `format` alone" | MAY / MUST | OK / HOST | as #33 |
| 55 | MAY render nested objects beyond one level | MAY | HOST | raw schema to host |
| 56 | MAY back storage with NAP-STORAGE | MAY | OK | not used |
| 57 | MAY use `$version` for cross-hash migration | MAY | OPTIONAL | README "Optional behaviours" (`$version` migration across artifact hashes) |
| 58 | MAY retain a graveyard; "Graveyard values MUST NOT be delivered" | MAY / MUST | OK | No graveyard; orphans are deleted (#48) |
| 59 | MAY emit `config.settingsOpened`; "Napplets MUST NOT rely on this message" | MAY / MUST | OPTIONAL / NAPPLET | README "Optional behaviours" |
| 60 | Anti-features "MUST NOT appear in conformant implementations" (`config.set`, `$ref`, `pattern`, napplet-rendered settings, napplet validation code, `ui:widget`, migration code, cross-napplet sharing, streaming keystrokes, 2020-12 conditionals, keychain as MUST) | MUST NOT | OK | `config.set` unknown (vector :1031); `$ref`/`pattern`/conditionals/`$dynamicRef` rejected (`keyError`); `ui:widget` is outside the subset and rejected (`keyError` :346); settings UI is the host's (`openSettings` effect); no napplet code runs in the shell; isolation `handle_isolated`; commit-only writes (`edited`) |
| 61 | Security: "NAP-CONFIG requests MUST NOT carry caller-selected identity or scope fields" | MUST | OK / NAPPLET | as #10 |
| 62 | Cleartext secrets: "Implementers MUST be aware that ..." | MUST (informative) | HOST | Host.lean:283-284 |
| 63 | "Shells SHOULD suppress console logging of `config.values` deliveries containing secret fields" | SHOULD | HOST | Host.lean:283-284 ("SHOULD keep their values out of logs") |
| 64 | "Napplets SHOULD read secrets on demand" | SHOULD | NAPPLET | — |
| 65 | "Napplets SHOULD still declare `additionalProperties: false` explicitly" | SHOULD | NAPPLET | — |
| 66 | "Shells MUST reject any schema containing `$ref` at `config.registerSchema` time" | MUST | OK | `keyError` :342 at every node (`decodeNode` :427); vector :1083 |
| 67 | Error envelopes `{type, id, ok, code?, error?}`; codes drawn from the catalogue | (normative) | OK | `resultOk` :116, `resultErr` :119, `codeName` :78 (all eight codes; `unknown-section` never emitted) |
| 68 | Undeclared section: "shells SHOULD silently ignore ... Shells MUST NOT return a wire error for this case"; "case-sensitive ... opaque identifier" | SHOULD / MUST | OK | `handle .openSettings` :612 drops an undeclared `section` (`List.contains`, exact match), sends nothing to the napplet; vector :1063 |
| 69 | Subscribe/get before schema: `config.schemaError` `no-schema`; "No `config.values` is emitted until a valid schema has been registered" | (normative) | OK | `deliver` :570; `push` :578 needs a schema; the subscription is kept, so the first `config.values` follows the first accepted registration (`handle` :600) |
| 70 | Unsupported `$schema` draft → `unsupported-draft` | (normative) | OK / DECISION | `rootCheck` :509, `supportedDrafts` :349 (draft-07, 2019-09, 2020-12: README CONFIG paragraph); vector :1088 |

## MISMATCH items (all resolved; see README decisions 35–47 and Host.lean)

**C1. No initial `config.values` when required root properties cannot be resolved (#3, #13).**
Upstream: "The shell MUST deliver an immediate initial `config.values` push on subscription",
and also "Every `config.values` delivery MUST contain only values that validate against the
currently-registered schema". Take a schema whose root `required` names a property with no
default and no persisted value. Delivering is then impossible without breaking validation.
`deliver` (:568-574) sends `config.schemaError {code: "invalid-schema", error: "configuration
requires valid values before delivery"}` for both `config.subscribe` and `config.get`. For
`config.get` this answer is uncorrelated (no `id`), so the napplet's `get()` promise never
settles. Upstream contradicts itself here and no README decision covers it.
Minimal fix: document it. Add to the README CONFIG paragraph: "When a `required` property
has no valid persisted value or default, no snapshot validates. `config.get` and the initial
`config.subscribe` push are answered with `config.schemaError` (`invalid-schema`) instead of
`config.values`. The subscription is kept, and the first `config.values` follows the first
commit that satisfies `required`." Optionally, as a behaviour change, also reject at
`registerSchema` a root `required` property that has neither a `default` nor an ancestor
default (`invalid-schema`). But that rejects schemas made only of Core keywords (see C3), so
documentation is preferred.

**C2. `secret-with-default` is not the code for non-string secret properties (#32, #45).**
Upstream: "Shells MUST reject any schema that declares both on the same property with `code:
"secret-with-default"`." `decodeNode` (`Run/Config.lean`) checks "`x-napplet-secret` applies
only to strings" before the secret-with-default check: line 438 (object), 461 (array) and
477 (non-string primitive). So `{type: "integer", "x-napplet-secret": true, default: 1}` is
rejected with `invalid-schema`.
Fix: in `decodeNode`, right after `let dflt := ...` (:434), add
`if secret && dflt.isSome then throw (.secretWithDefault, "`x-napplet-secret` property declares a `default`")`,
before the `match j.getStr? "type"`. Drop the now-redundant check at :478-479, and add a
vector for the integer case.

**C3. Some schemas made only of Core-Subset keywords are rejected (#16).**
Upstream: "Every conformant shell MUST accept and render schemas that use only the types,
keywords, and constraints enumerated below." `enum` is listed without a type restriction,
but `decodeNode` :462-463 rejects it on `array`. `leafOf` :399-402 rejects
`minimum`/`maximum` on strings and booleans and `minLength`/`maxLength` on non-strings,
which upstream describes only as "apply to" those types (JSON Schema ignores them
elsewhere). `additionalProperties` must be a boolean (:445-447).
Minimal fix, either:
- **Behaviour.** Accept `enum` on arrays: add an `enum : Option (List Json)` to `.arr` and
  check it in `arrOk`. Accept constraints that do not apply to the type and ignore them:
  replace the `absent` checks in `leafOf` with ignoring them.
- **Documentation.** Add a README CONFIG decision: "A Core keyword used on a type it does
  not apply to (`enum` on arrays or objects, length constraints on non-strings, numeric
  bounds on non-numbers) and a schema-valued `additionalProperties` are `invalid-schema`."
