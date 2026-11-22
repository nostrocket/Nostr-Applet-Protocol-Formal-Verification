# NAP-DISPLAY conformance

Upstream: `napplet/naps` PR #97, branch `nap-display`, `naps/NAP-DISPLAY.md` at
`2c2e1b5ca3849dbab8c3a721704e30646a641079`.

Lean: `Napplet/Run/Display.lean` (component), `Napplet/Nap/Display.lean` (pure model),
`Napplet/Host.lean` §DISPLAY (lines 318-339). "README" means `lean/README.md` (DISPLAY
paragraph in "Decisions added with the wire codec").

| # | Upstream statement (short quote) | Level | Status | Lean |
|---|---|---|---|---|
| 1 | `DisplayDevice` `id`, `width`, `height`, `type` required; width/height positive | REQUIRED | OK | `deviceJson` :98 always emits all four; `deviceOf?` :102 drops zero geometry or an unknown `type` from host reports; Host.lean:321 ("with positive geometry") |
| 2 | "MUST return the same `id` for the same display across list calls, ordering changes, and runtime restarts" | MUST | HOST | Host.lean:322-323; the runtime never invents or rewrites ids (`St.devices` comes only from `Cfg.devices` and the host `devices` event, `onEvent` :203) |
| 3 | "MUST NOT reuse an `id` for a different display" | MUST | HOST | Host.lean:323 |
| 4 | `Pixel` `x`, `y`, `bytes` required; "exactly three sRGB bytes" | REQUIRED | OK | `pixelOf?` :116 (malformed gives `invalid-pixel`, `decode` :161); `pixelOk` checks `bytes.length == 3` (`Nap/Display.lean:49`) |
| 5 | "Each byte MUST fall within `0..255`" | MUST | OK | `pixelOk` (`Nap/Display.lean:50`), checked by `batchOk` :52 before anything is applied; theorem `push_applies` (`∀ p ∈ ps, pixelOk d p`) |
| 6 | "Each coordinate MUST satisfy `0 <= x < width` and `0 <= y < height`" | MUST | OK | `pixelOk`; negative numbers fail `Json.asNat?` and give `invalid-pixel` (vector :344) |
| 7 | "A batch MUST contain each coordinate at most once" | MUST | OK | `batchOk` Nodup check (`Nap/Display.lean:56`); vector :338 |
| 8 | `list()` "returns the displays that the shell permits"; "MAY reflect connection or policy changes" | MAY | OK | `NapDisplay.list` (`Nap/Display.lean:60`), theorem `list_permitted` (Nap :63, Run :238); host `devices` event replaces the list (`onEvent` :203) |
| 9 | `push`: "submits one non-empty pixel batch"; success = whole batch accepted | (normative) | OK | `batchOk` rejects empty (`invalid-pixel`); theorem `push_applies` :266 |
| 10 | "The runtime validates a whole batch before applying any pixel from it" | (normative) | OK | `NapDisplay.push` (`Nap/Display.lean:71`); theorems `push_atomic` (Nap :81, Run :254) |
| 11 | "The runtime never exposes device byte order, scan order, or driver commands" | (normative) | OK + HOST | `pushArgs` :175 carries only logical `{x, y, bytes}`; Host.lean:338-339 ("It never receives driver commands from a napplet") |
| 12 | Result `error` values `not-found`, `unavailable`, `denied`, `invalid-pixel`, `too-large` (MAY include) | MAY | OK | `NapDisplay.push`/`batchOk`, `handle` :188 (`unavailable`); order not-found, unavailable, denied, batch is a README decision |
| 13 | "A failed `display.list` returns an empty `displays` list" | (normative) | OK | `display.list` never fails; with no permitted display the list is `[]` (vector :347) |
| 14 | "A failed `display.push` applies no pixels" | (normative) | OK | theorem `push_atomic` :254 (no `push` effect means state unchanged) |
| 15 | Missing `displayId` | — | DECISION | README DISPLAY paragraph (`"invalid request"`); `decode` :157 |
| 16 | "MUST discover devices and determine their `id`, `width`, `height`, `type`. A napplet cannot supply or alter descriptors" | MUST | HOST + OK | Discovery: Host.lean:320-322 (`Cfg.devices`), :328-332 (`devices` event). `handle` :185 only ever changes `fb`, never `devices`/`offline` (by inspection: both branches return `s` or `{ s with fb := fb' }`) |
| 17 | "MUST map logical RGB pixels to the selected device" | MUST | HOST | Host.lean:336-338 |
| 18 | "SHOULD preserve position, relative luminance, and color" | SHOULD | HOST | Host.lean:336 ("maps logical sRGB to the device"). The luminance/colour fidelity SHOULD is not restated in the contract (wording gap only) |
| 19 | "MAY rotate coordinates, reorder scan lines, quantize, dither, adjust brightness, or coalesce refreshes" | MAY | HOST | Host.lean:336-337 |
| 20 | "MUST process accepted batches in arrival order for each display" | MUST | OK + HOST | One `push` effect per accepted request, emitted in the same step (`handle` :195); Host.lean:337-338 ("MUST apply batches for the same display in the order the effects are emitted"); global atomic-step contract Host.lean:39-41 |
| 21 | "The shell MUST mediate which displays each napplet can list and write" | MUST | OK | `Cfg.permitted : Identity → String → Bool` (default deny) :70; `list_permitted` :238; `push_applies` requires `s.cfg.permitted cx.identity did` |
| 22 | "MUST respond to every request with the matching result and `id`" | MUST | OK | theorems `list_permitted` :238, `push_one_result` :244; decode rejections with a string `id` answer with that `id` (:157, :161); without a string `id` nothing is sent (README decision 31) |
| 23 | "MAY reject, rate-limit, or cap batches" | MAY | OK | `Cfg.maxBatch` (`too-large`); no rate limit |
| 24 | "SHOULD require explicit per-napplet permission" | SHOULD | OK | `Cfg.permitted` default `fun _ _ => false` :70 |
| 25 | "SHOULD use opaque identifiers instead of hardware serial numbers" | SHOULD | HOST | Host.lean:323-324 ("it SHOULD be opaque (not a hardware serial)") |
| 26 | "SHOULD bound batch size and update rate" | SHOULD | OK (size) / OPTIONAL (rate) | `maxBatch := 4096`. Update rate is not bounded and is not in README's optional list (README gap only) |

Note (no change needed): a push to a display the napplet may not write returns `denied`, or
`unavailable` if that display is offline, rather than `not-found`. So a napplet can learn that
an id exists. Upstream defines `denied` for exactly this case, and writing is still mediated,
so no MUST is broken.

No MISMATCH items.
