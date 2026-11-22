# NAP-NOTIFY conformance

Upstream: `napplet/naps` PR #11, branch `nub-notify`, `naps/NAP-NOTIFY.md` at
`67877ef6c31ec8acee3125c1d8b4c781010e37dc`.

Lean: `Napplet/Run/Notify.lean` (component), `Napplet/Nap/Notify.lean` (pure model),
`Napplet/Host.lean` §NOTIFY (lines 507-534). "README" means `lean/README.md`. Its NOTIFY
paragraph is in "Decisions added with the wire codec"; decision 24 is in the numbered list.

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | `title` required in `NotificationPayload` | REQUIRED | OK | `Run/Notify.lean:177` `payloadOf?`; a missing title gets `"invalid request"` (`decode` :209, README decision 31) |
| 2 | `NotificationResult.notificationId` required | REQUIRED | DECISION | Upstream contradicts itself: the wire table has `notificationId?` and Error Handling says it is absent on error. `sendResult` :253 omits it only on error (`Nap/Notify.lean:72-78`) |
| 3 | `NotificationAction` `id`, `label` required | REQUIRED | OK | `actionOf?` :165 |
| 4 | `NotificationChannel` `channelId`, `label` required | REQUIRED | OK | `channelOf?` :182; a malformed one is dropped |
| 5 | `PermissionResult.granted` required | REQUIRED | OK | `permissionResult` :206 always sets `granted` |
| 6 | "The shell MAY reject the notification (permission denied, rate limited)" | MAY | OK | `NapNotify.send` (`Nap/Notify.lean:70`); `Cfg.requirePermission`, `limited` :283; theorem `send_requires_permission` |
| 7 | `registerChannel`: "The shell MAY ignore channels it does not support" | MAY | HOST | Host.lean:555-557 ("the host MAY ignore channels"); `core` :320 forwards |
| 8 | `requestPermission`: "MAY prompt the user or apply policy silently" | MAY | OK | `core` `.requestPermission` :326 (answers at once when permitted, else `Call.prompt`) |
| 9 | Wire names `notify.channel.register` / `notify.permission.request` (API table says `registerChannel` / `requestPermission`) | — | DECISION | README NOTIFY paragraph; `decode` :209; vector :778 |
| 10 | `notify.dismiss`, `notify.badge`, `notify.channel.register` fire-and-forget | — | OK | `decode` :218-229 (no reply; malformed dropped) |
| 11 | `notify.permission.request`: "The shell MAY prompt the user asynchronously" | MAY | OK | `Call.prompt` :330, answered in `onReply` :339 |
| 12 | Actions: "The shell MAY limit the number of actions displayed" | MAY | OK | `take 3` in `NapNotify.send` (`Nap/Notify.lean:76`); `render_actions_capped`; README NOTIFY paragraph |
| 13 | "When `error` is present, `notificationId` is absent and the notification was not created" | (normative) | OK | `Nap/Notify.lean:72-73`; theorems `send_error_creates_nothing` (`Nap/Notify.lean:125`), `send_refused_creates_nothing` :635 |
| 14 | `granted: false` on denial "is not an error" | (normative) | OK | `onReply` :343 (any non-allow reply gives `granted:false`); malformed `channel` also gets `granted:false` :236 |
| 15 | "Messages referencing an unknown `notificationId` MUST be silently ignored by both napplet and shell" | MUST | OK (shell) / NAPPLET | Shell: `core .dismiss` :309-311, `onEvent` :353-374 (unknown ids give `(s, [])`), theorem `NapNotify.dismiss_foreign_ignored`. Napplet: `Binding.receive` only routes pushes to handlers; no NOTIFY-specific state |
| 16 | "MUST accept `notify.send` and respond with `notify.send.result` carrying the same `id`" | MUST | OK | `core .send` :302; theorems `NapNotify.send_same_id`, `send_replies_to_requester` :613; malformed with `id` gets an error result :217; without a string `id` dropped (README decision 31) |
| 17 | "MUST accept `notify.permission.request` and respond with `notify.permission.result` carrying the same `id`" | MUST | OK | `core .requestPermission` :326, `onReply` :339; malformed `channel` :236. Teardown cancels the prompt (`drop` :385), so no reply goes to a dead endpoint |
| 18 | "MUST track active notifications per napplet and remove them when the napplet iframe is removed" | MUST | OK | `NotifyState.shown` with `owner`; `drop` :376 → `NapNotify.cleanup`; theorems `cleanup_removes_all`, `drop_cleanup` :716, `drop_clears` :502; called from `Runtime.lean:281` |
| 19 | "SHOULD display notifications using its own UI" | SHOULD | HOST | `Effect.nap .notify "show"`; Host.lean:546-551 |
| 20 | "SHOULD respect the `priority` field" | SHOULD | HOST | Host.lean:550 ("SHOULD honour `priority`"); `showArgs` :259 passes it (absent → `normal`, :303) |
| 21 | "MAY send `notify.action`, `notify.clicked`, `notify.dismissed`" | MAY | OK | `onEvent` :353; theorem `event_to_owner` :681; `action` only if the id is one of that notification's actions :362 |
| 22 | "MAY send `notify.controls`" | MAY | OK | `pushControls` :297 (once per endpoint, before the first result); README NOTIFY paragraph |
| 23 | "MAY enforce notification rate limits per napplet" | MAY | OK | `Cfg.rateWindow/rateMax/urgentMax` :101-105, `limited` :283 |
| 24 | "MAY enforce ACL checks on `notify` capabilities" | MAY | OK | permission gate `permitted` :277 (default `requirePermission := true`); domain exposure in Runtime |
| 25 | "MAY support notification channels and per-channel policies" | MAY | HOST | Host.lean:555-557, 516 ("its per-channel user settings") |
| 26 | "MAY delegate to the browser's Notification API" | MAY | HOST | Host.lean:548 ("toast, system notification, notification centre") |
| 27 | "MUST silently ignore messages referencing unknown notification IDs" | MUST | OK | as #15 |
| 28 | "MUST clean up all notifications for a napplet when the napplet's iframe is removed" | MUST | OK | as #18; `drop` also clears the badge :386 and cancels prompts :385 |
| 29 | "SHOULD sanitize notification `title` and `body`" | SHOULD | OK + HOST | `Cfg.sanitize` applied in `NapNotify.send` (theorem `render_sanitized`); default is `id`, but Host.lean:548-549 requires plain-text rendering ("MUST render ... as plain text, never markup") |
| 30 | "`icon` ... SHOULD validate URLs and enforce a content security policy" | SHOULD | HOST | Host.lean:551 ("fetches `icon` only under its own resource policy") |
| 31 | "SHOULD clearly attribute notifications to the originating napplet" | SHOULD | OK + HOST | `showArgs` :259 carries `port` and `napplet` (catalog id); theorem `render_attributed`, `show_safe` :589; Host.lean:549 ("MUST visibly attribute it to the napplet") |
| 32 | "SHOULD rate-limit urgent notifications" | SHOULD | OK | `urgentMax := 3` per `rateWindow`, `limited` :284 |
| 33 | "MAY require explicit user consent for urgent notifications" | MAY | OPTIONAL | Not modelled; urgent uses the ordinary permission. Not in README's optional list (README gap only) |
| 34 | "MUST NOT block other napplet messages while a permission prompt is pending" | MUST | OK + HOST | Prompt is an async `Call` with a tagged reply (`core` :329-332, `onReply`); README decision 34; Host.lean:182-183 and :526 ("The prompt MUST NOT block other inputs") |
| 35 | "The shell MAY cap or ignore badge counts" | MAY | OK | `min c s.cfg.badgeMax` :316 |
| 36 | Who may dismiss (upstream only says ignore unknown ids) | — | DECISION | README decision 24; `NapNotify.dismiss` (`Nap/Notify.lean:81`), theorems `dismiss_only_own` (Nap :138, Run :656), vector :796 |

No MISMATCH items.
