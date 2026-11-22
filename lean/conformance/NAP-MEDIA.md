# NAP-MEDIA conformance

Upstream: `napplet/naps` PR #10, branch `nub-media`, `naps/NAP-MEDIA.md` at
`7806f438530251fce5129f8e6239d6b642278759`.

Lean: `Napplet/Run/Media.lean` (component), `Napplet/Nap/Media.lean` (pure model),
`Napplet/Host.lean` §MEDIA (lines 445-505), `Napplet/Binding.lean` (napplet side).
"README" means `lean/README.md` (decisions 22-23, the MEDIA paragraph, "Not modelled yet").

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | Artwork: "Napplets and shells that need the artwork bytes MUST fetch them through NAP-RESOURCE" | MUST | HOST / NAPPLET | Host.lean:492-493 ("artwork is fetched only through that same policy"); the runtime never fetches artwork |
| 2 | "`artwork.hash` ... MAY be used by shells as a content-addressed cache key" | MAY | HOST | Metadata passed opaquely to the host (`openArgs` :517, `registerArgs` :521) |
| 3 | "If the optional `resource` domain is unavailable, napplets SHOULD omit remote artwork" | SHOULD | NAPPLET | — |
| 4 | `MediaState.status` required | REQUIRED | OK | `stateOf?` :257 |
| 5 | `MediaCommand.action` required | REQUIRED | OK | `commandOf?` :265 (an unknown action makes it malformed) |
| 6 | `MediaSessionEnded` `sessionId`, `reason` required | REQUIRED | OK | `endedJson` :435 |
| 7 | `MediaSessionResult` `sessionId`/`owner` "Required on successful creation"; `error` means "no session was created" | REQUIRED | OK | `createOk` :424; `createErr` :431 (echoing the hint is a README MEDIA decision); `NapMedia.create` (`Nap/Media.lean:75-76`) leaves state unchanged on error |
| 8 | `createSession`: "The napplet MUST set `owner` to `shell` or `napplet`" | MUST | NAPPLET + OK | Shell rejects otherwise (#26) |
| 9 | "For shell-owned sessions, `source` is required"; napplet-owned `source` "optional and advisory" | (normative) | OK | `NapMedia.create` `"missing source"` (`Nap/Media.lean:75`); napplet-owned never opens a source (`open_only_shell_owned` :1042) |
| 10 | "The napplet MAY provide a preferred `sessionId` ..." / "The shell MAY reject session creation" | MAY | OK | `canonical` :496; `precheck` :504 (`session limit exceeded`, `unsupported owner mode`, `unsupported source`, `source blocked`), `autoplay denied` |
| 11 | `destroySession`: removes the session and "sends `media.session.ended` with reason `destroyed`" | (normative) | OK | `onSession .destroy` :567 → `retireWith … .destroyed true` :555; theorem `destroy_once` :985 |
| 12 | `onEnded`: "The binding MUST retain the terminal record until the napplet endpoint is destroyed. A handler registered after retirement MUST receive it once." | MUST | RESOLVED (was MISMATCH) | `Binding.receive.pushIn` :206 buffers `media.session.ended` only when no handler exists, and `Binding.register` :213 clears it after the first delivery. A second handler registered after retirement gets nothing, and so does any handler registered after an earlier one already got it live. Checked: register `onEnded`, receive `ended`, then register again gives 0 messages. See M1 |
| 13 | "Retirement MUST stop further state, capability, control, and command callbacks for that session" | MUST | OK (shell) / RESOLVED (was MISMATCH) (binding) | Shell never sends them (#36). `Binding.receive` does not drop late `media.state`/`capabilities`/`command`/`controls` after `media.session.ended` for that `sessionId`. Checked: 1 message delivered. See M2 |
| 14 | "A napplet-owned player MUST stop its output and release session resources when it receives retirement" | MUST | NAPPLET | Not modelled (app code) |
| 15 | `context` "MUST NOT change session ownership" | MUST | OK | `context` is opaque JSON (`Create.context`) and is never read for ownership; theorems `handle_keeps` :748, `onEvent_keeps` :724, `NapMedia.ops_preserve_owner` |
| 16 | A napplet-owned `source` "does not ask the shell to fetch or play media" | (normative) | OK | `registerArgs` :521 has no `source`; Host.lean:496-498 |
| 17 | "The shell MUST return the canonical `sessionId` in `media.session.create.result`" | MUST | OK | `createOk` :424 with `w := canonical s c.hint` :540 |
| 18 | "All later messages MUST use the canonical `sessionId`" | MUST | NAPPLET + OK | Shell resolves by canonical id only (`lookup` :406) |
| 19 | "Messages that use the pre-canonical hint after creation SHOULD be treated as unknown-session messages" | SHOULD | OK | `lookup`/`owned` :406-415 (a rewritten hint names no session of this endpoint) |
| 20 | "Missing or unrecognized reasons MUST be treated as unspecified causes, while still processing the message's status, action, or terminal meaning" | MUST | OK / DECISION | `MState.reason`/`MCommand.reason` are free text (`stateOf?`, `commandOf?`); a host `retire` with an unknown reason still retires, reported as `policy` (`hostEvent` :641; Host.lean:536-537) |
| 21 | "Receivers MUST NOT infer natural completion or permission to resume from `stopped` or `paused` alone" | MUST | OK | Resume needs `pausedByFocus` (`focusGained`, `Nap/Media.lean:112`), set only by `focusLost`; `keepsFocusPause` :481 never sets it |
| 22 | "Playback owners SHOULD include the known reason on state transitions" | SHOULD | OK / HOST | Runtime focus reports carry reasons (`realizeFocus` :602); host state contract Host.lean:522-525 |
| 23 | "A natural completion that leaves the session usable MUST be reported as `status: "stopped"` with `reason: "ended"`" | MUST | HOST / NAPPLET | Host.lean:523 ("natural end as `stopped`/`ended`"); vector :1210 |
| 24 | "If the shell retires the session for that completion instead, it MUST send `media.session.ended` with reason `ended` as the sole notification of that completion" | MUST | RESOLVED (was MISMATCH) (contract gap) | `hostEvent "retire"` :641 sends exactly one `ended`. But Host.lean:535-537 does not forbid the host first sending a `state` event `stopped`/`ended` for the same completion, which the runtime would forward (`hostEvent "state"` :611). See M4 |
| 25 | "Consumers MUST NOT interpret other reasons as natural completion" | MUST | OK | The runtime gives no meaning to reasons besides `focus-lost` (`keepsFocusPause`) |
| 26 | "An empty capability list disables actions; it MUST NOT be used as a substitute for session retirement" | MUST | OK | `media.capabilities []` only updates `Info.actions` (`onSession` :572); retirement only through `retireWith` |
| 27 | "The shell MAY retire either owner mode under policy" | MAY | OK | `hostEvent "retire"` (`policy`), focus-loss retirement :633 |
| 28 | "MUST retire a session when it permanently reallocates its output ... or when its backend exits" (`preempted`, `user`/`ended`/`error`/`backend-exited`) | MUST | HOST | Host.lean:535-537 (`retire` event with those reasons); vector :1217 |
| 29 | "Before notifying retirement, the shell MUST remove the session from dispatch and stop or revoke its output authority" | MUST | OK + HOST | `retireWith` :555 emits `close` before `ended` when the runtime decides, and removes it from `core.live` in the same step; host-initiated `retire` is sent after the host stopped output (Host.lean:535) |
| 30 | "It MUST send exactly one `media.session.ended` for that session to its still-live napplet endpoint" | MUST | OK | theorems `NapMedia.retire_once`, `destroy_once` :985; teardown sends none (`drop` :657) |
| 31 | "Any already-enqueued state, capability, control, or command messages MUST precede the terminal notification" | MUST | OK | Atomic steps and in-order sends per port (Host.lean:39-41) |
| 32 | "The shell MUST NOT send further state, capabilities, controls, or commands for the retired session" | MUST | OK | `lookup` returns `none` for retired ids; theorems `onEvent_unknown_silent` :978, `handle_unknown_silent` :973, `NapMedia.retired_silent` |
| 33 | "The binding MUST discard late messages for it and retain the terminal record for `onEnded`" | MUST | RESOLVED (was MISMATCH) | as #12/#13 (M1, M2) |
| 34 | "A successful creation result MUST precede any terminal notification. Failed creation produces no retirement notification." | MUST | OK | `handleCreate` :536 sends `createOk` in the creating step; a failed create adds no session, so nothing can retire |
| 35 | "Retired identifiers MUST NOT be reused during the napplet endpoint's lifetime, even when a later creation requests the same preferred identifier" | MUST | OK | `used` is never pruned (`drop_used` :943); `canonical` :496 refuses used hints; theorems `handle_used` :906, `NapMedia.create_fresh`; vector :1168 |
| 36 | "Messages targeting retired sessions, including `play`, MUST be silently ignored ... MUST NOT reacquire output or preempt another session" | MUST | OK | `handle_unknown_silent` :973; vector :1221 |
| 37 | "The shell MUST continue enforcing consent, autoplay, and audio-focus policy on creation" | MUST | OK + HOST | `Cfg.autoplay` (`autoplay denied`, `handleCreate` :543); Host.lean:493-494 ("starts output only if `autoplay` is `true` and its autoplay and audio-focus policy allow it") |
| 38 | "Endpoint destruction requires cleanup but no notification to the dead endpoint" | (normative) | OK | `drop` :657 (only `close` effects); vector :1245 |
| 39 | "Shell-promoted persistent playback MUST first detach ...; its former session identifier MUST NOT become usable by a replacement endpoint" | MUST (conditional) | OPTIONAL / OK | No promotion (README "Optional behaviours": "MEDIA promoted (detached) playback"); ids are never reissued in the runtime session (#35) |
| 40 | Shell-owned focus loss: "MUST report a focus-induced pause as `media.state` with `status: "paused"` and `reason: "focus-lost"`" | MUST | OK | `NapMedia.focusLost` (`Nap/Media.lean:109`), `realizeFocus` :602 |
| 41 | Napplet-owned focus loss: "the shell MUST identify a focus-induced pause command with `reason: "focus-lost"`" | MUST | OK | `NapMedia.focusLost` (`Nap/Media.lean:110`); vector :1227 |
| 42 | "The napplet MUST pause and report its actual state" | MUST | NAPPLET | — |
| 43 | "A napplet-owned session MUST support `pause` if it produces pausable output; otherwise the shell MUST revoke output and retire the session under policy" | MUST | OK | `hostEvent "focusLost"` :633 retires with `policy` and `close` (Host.lean:514-515, output authority revoked) when `pause` is not declared; vector :1240 |
| 44 | "A napplet MUST NOT resume automatically merely because its window regains focus" | MUST | NAPPLET | — |
| 45 | Focus-gained `play`: "The shell MAY issue that command only when the session was playing before the focus-induced pause and no later user pause, stop, retirement, or playback failure superseded it" | MAY (restriction) | OK | `focusLost` acts only on `playing`; `pausedByFocus` cleared by `supersede` :489, `report` :485/`keepsFocusPause` :481 (any other status or reason, including `error`), retirement; theorems `NapMedia.resume_only_after_focus_pause`, `user_pause_blocks_resume`, `focusGained_only_after_focus_pause` :1010; README decision 23 |
| 46 | "The napplet MUST ignore that automatic-resume command if its own subsequent user action or playback failure superseded the focus pause" | MUST | NAPPLET | — |
| 47 | Shell-owned: "applies the same conditions and reports resumed playback with reason `focus-gained`" | (normative) | OK | `realizeFocus` :602 for `.state … .playing (some .focusGained)` |
| 48 | "A focus transition MUST NOT revive a retired session" | MUST | OK | `onEvent_unknown_silent` :978; `NapMedia.retired_silent` |
| 49 | "Shells MAY support a subset of source forms and reject unsupported forms during session creation" | MAY | OK | `Cfg.sourceForms`, `sourceSupported` :501 |
| 50 | Shell-owned `source` "is required unless the shell defines a separate out-of-band source binding" | (normative) | DECISION | README "Not modelled yet": no out-of-band binding; `"missing source"` |
| 51 | "The shell MUST fetch and validate source bytes through shell-controlled policy" | MUST | HOST | Host.lean:489-491 (`open`: NAP-RESOURCE policy) |
| 52 | Napplet-owned: "The shell MUST NOT treat a napplet-owned `source` as permission to fetch or play" | MUST | OK + HOST | theorem `open_only_shell_owned` :1042, `NapMedia.fetch_only_shell_owned`; Host.lean:498 |
| 53 | "A shell MAY ignore any context field it does not understand" | MAY | HOST | `context` passed opaquely |
| 54 | "`context.links[]` ... unknown relation names MUST be ignored" | MUST | RESOLVED (was MISMATCH) (contract gap) | The runtime forwards `context` unread to the host (`openArgs` :517, `registerArgs` :521). Host.lean §MEDIA says nothing about how the host treats `links`. See M3 |
| 55 | "Absence of `nostr.relays` MUST NOT make the link invalid" | MUST | OK (runtime) / RESOLVED (was MISMATCH) (contract gap) | The runtime never validates `context`. The host contract does not state it. See M3 |
| 56 | Metadata artwork "If both are provided, the shell MAY prefer either" | MAY | HOST | — |
| 57 | Error strings `session limit exceeded`, `invalid session ID`, `missing source`, `unsupported source`, `source blocked`, `autoplay denied` | — | OK | `precheck` :504, `handleCreate` :541, `decodeCreate` :288, `NapMedia.create` |
| 58 | "Messages referencing an unknown `sessionId` MUST be silently ignored by both napplet and shell" | MUST | OK (shell) / NAPPLET | `handle_unknown_silent`, `onEvent_unknown_silent`; foreign ids too (`owned` :412). Binding: pushes without a handler are dropped |
| 59 | "Commands that are not valid for the current owner mode ... SHOULD be silently ignored ... MUST NOT cause a session to switch owner" | SHOULD / MUST | OK | `onSession` :563 (owner-mode checks; napplet `media.state`/`capabilities` ignored for shell-owned and vice versa); `handle_keeps` :748 |
| 60 | "MUST accept `media.session.create` and respond with `media.session.create.result` carrying the same `id`" | MUST | OK | `handleCreate` :536 (every path sends exactly one result); `decodeCreate` :280 rejections carry `id`; without a string `id` dropped (README decision 31) |
| 61 | "MUST reject `media.session.create` messages without `owner`" | MUST | OK | `decodeCreate` :284-285 (`"invalid request"`); vector :1133 |
| 62 | "MUST reject `owner: "shell"` creation when `source` is missing or blocked by policy" | MUST | OK | `NapMedia.create` (`missing source`), `precheck` :512 (`source blocked`), vector :1160 |
| 63 | "MUST return the canonical `sessionId`" | MUST | OK | as #17 |
| 64 | "MUST track active sessions per napplet and apply Session retirement and preemption" | MUST | OK | `NapMedia.MediaState` (endpoint per session), `NapMedia.Inv` preserved (`handle_inv` :820, `onEvent_inv` :844, `drop_inv` :867) |
| 65 | "SHOULD display media controls ... based on the napplet's reported capabilities" | SHOULD | HOST | `capabilities` effect; Host.lean:503-504 |
| 66 | "SHOULD update its media control UI in response to `media.state`" | SHOULD | HOST | `state` effect; Host.lean:501-502 |
| 67 | "MAY send `media.command` to control napplet playback" | MAY | OK | `hostEvent "command"` :625 |
| 68 | "MAY send `media.controls`" | MAY | OK | after create (`realizeCreate` :527) and host `controls` event |
| 69 | "MAY enforce audio policy" / "SHOULD make audio focus decisions across all sessions, regardless of owner" | MAY / SHOULD | HOST + OK | Host decides (`focusLost`/`focusGained` events, Host.lean:533-534); the runtime applies them to either owner |
| 70 | "For shell-owned sessions, the shell MUST own fetching, playback lifecycle, state emission, and policy enforcement" | MUST | OK + HOST | napplet `media.state`/`capabilities` ignored for shell-owned (`onSession` :568-576); state comes only from host events; Host.lean:487-495 |
| 71 | "For napplet-owned sessions, the shell MUST NOT fetch/play `source` on the napplet's behalf" | MUST | OK | as #52 |
| 72 | "When the owning napplet/window closes, the shell MUST destroy napplet-owned sessions and SHOULD stop shell-owned sessions unless promoted" | MUST / SHOULD | OK | `drop` :657 retires and `close`s every session of the endpoint; Host.lean:512-518 |
| 73 | Promoted playback "MUST detach ... and MUST define how the user can stop or revoke" | MUST (conditional) | OPTIONAL | not modelled (README "Optional behaviours") |
| 74 | "MAY limit the number of concurrent sessions per napplet" | MAY | OK | `Cfg.maxSessions` |
| 75 | "MAY enforce ACL checks on `media`" | MAY | OK | domain exposure in `Runtime` |
| 76 | "MUST silently ignore messages from unknown session IDs" | MUST | OK | as #58 |
| 77 | "On endpoint removal, the shell MUST clean up all sessions still bound to it" | MUST | OK | `drop` :657; theorems `drop_clears` :774, `drop_inv` :867 |
| 78 | Napplet-owned: "The shell SHOULD only send commands listed in the napplet's current `media.capabilities`" | SHOULD | OK | `hostEvent "command"` :628 (`c.action ∈ i.actions`). The focus-gained `play` is sent whether or not `play` is declared (SHOULD, acceptable) |
| 79 | "unsupported pause MUST NOT leave revoked output playing" | MUST | OK | as #43 |
| 80 | "The napplet SHOULD ignore commands it does not currently support" | SHOULD | NAPPLET | — |
| 81 | "`seek` MUST include `value` as a position in seconds" | MUST | OK | `cmdOk` :467 on host commands and napplet commands |
| 82 | "`volume` MUST include `value` from `0.0` to `1.0`" | MUST | OK | `cmdOk` :470 (`unitInterval`) |
| 83 | Shell-owned: "The napplet MAY send `media.command` only for actions exposed through `media.controls` or `media.capabilities`" | MAY (restriction) | OK | `onSession .command` :578 (`c.action ∈ i.actions ∨ c.action ∈ i.controls`) |
| 84 | "The shell MUST enforce source policy, autoplay policy, audio focus, and output volume" | MUST | HOST | Host.lean:507-509 (backend applies its policy), :455-460 |
| 85 | "MAY ignore `seek` when live / `next` and `prev` unless a queue" | MAY | HOST | Host.lean:508-509 |
| 86 | "MUST NOT expose raw source bytes to the napplet as part of command handling" | MUST | OK + HOST | No runtime message carries bytes; Host.lean:491 ("it never gives the bytes to the napplet") |
| 87 | "Napplets SHOULD NOT include sensitive information in metadata" | SHOULD | NAPPLET | — |
| 88 | "Shells SHOULD validate Nostr references before using them for UI or routing and MUST ignore unknown context links" | SHOULD / MUST | RESOLVED (was MISMATCH) (contract gap) | as #54 (M3) |
| 89 | Artwork URLs: "SHOULD validate URLs and enforce a content security policy" | SHOULD | HOST | Host.lean:492-493 |
| 90 | "Shell-owned `source` URLs ... MUST apply the same resource safety policy" | MUST | HOST | Host.lean:489-491 |
| 91 | "The shell MAY enforce volume limits at the iframe level" | MAY | HOST | not stated; MAY |
| 92 | "The shell MUST NOT let a caller-supplied reason bypass ownership, capability, autoplay, or audio-focus checks" | MUST | OK | `cleanCmd … (some "user")` :476/:579 replaces napplet reasons; checks in `onSession`/`handleCreate` never read a reason; a napplet `paused/focus-lost` report cannot set `pausedByFocus` (`report` :486: `x.pausedByFocus && …`) |
| 93 | "The napplet ... SHOULD validate the `action` against its declared capabilities" | SHOULD | NAPPLET | — |
| 94 | Initial state after create | — | DECISION | README decision 22 (`stopped`) |

## MISMATCH items (all resolved; see README decisions 35–47 and Host.lean)

**M1. `onEnded` terminal record is not retained for every late handler (#12, #33).**
Upstream: "The binding MUST retain the terminal record until the napplet endpoint is
destroyed. A handler registered after retirement MUST receive it once."
`Binding.receive.pushIn` (`Binding.lean:206`) puts `media.session.ended` in `buffer` only
when no handler is registered, and `Binding.register` (:213) removes it on first delivery.
So a handler registered after one that already got the record (live, or from the buffer)
receives nothing.
Fix (`Napplet/Binding.lean`): add `terminal : List (Key × Json)` to `St`. In `pushIn`,
always record `media.session.ended` in `terminal`, whether or not a handler exists. In
`register`, for a key whose type is `media.session.ended`, also deliver the matching
`terminal` entry and do not remove it. Add a theorem: after `ended` is received, every later
`register k` delivers it exactly once.

**M2. The binding does not discard late messages for a retired session (#13, #33).**
Upstream: "Retirement MUST stop further state, capability, control, and command callbacks
for that session." and "The binding MUST discard late messages for it."
`Binding.receive` routes `media.state` / `media.capabilities` / `media.command` /
`media.controls` to their handler regardless of an earlier `media.session.ended` with the
same `sessionId`. The shell never sends such messages (#32), so the composed system is
unaffected, but the binding as specified is not.
Fix (`Napplet/Binding.lean` `receive.pushIn`): if `t` is one of those four types and
`terminal` (from M1) holds `media.session.ended` for the same route, return `(s, [])`. Add a
theorem saying so.

**M3. The host contract does not say how `context` links are handled (#54, #55, #88).**
Upstream: "unknown relation names MUST be ignored", "Absence of `nostr.relays` MUST NOT make
the link invalid", "Shells SHOULD validate Nostr references ... and MUST ignore unknown
context links". The runtime forwards `context` unread to the host in `open`/`register`, so
these duties fall on the host, but Host.lean §MEDIA (and the Host operations docstring in
`Run/Media.lean` :56-67) does not state them.
Fix: add to the `open` and `register` bullets in both places: "`context` is UI and
association metadata only. It never grants fetch authority or changes ownership. The host
MUST ignore `links[]` entries whose `rel` it does not understand, MUST NOT treat a missing
`nostr.relays` as invalid (it resolves the reference through its normal routing), and
SHOULD validate Nostr references before using them for UI or routing."

**M4. "Sole notification" of a retiring completion is not in the host contract (#24).**
Upstream: "If the shell retires the session for that completion instead, it MUST send
`media.session.ended` with reason `ended` as the sole notification of that completion."
The runtime sends one `ended` for a host `retire {reason: "ended"}`. But the host's `state`
event contract (Host.lean:522-525, "natural end as `stopped`/`ended`") does not forbid
sending a `state stopped/ended` for the same completion first. The runtime would forward it,
and the napplet would get two completion notices.
Fix: Host.lean §MEDIA `retire` bullet (and `Run/Media.lean` :104-106): "When the host
retires a session because its source completed, it sends `retire` with reason `ended` and
MUST NOT send a `state` event with reason `ended` for that completion."
