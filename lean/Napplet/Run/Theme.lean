/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Component
import Napplet.Nap.Theme

/-!
# NAP-THEME runtime component

Upstream: `napplet/naps` `master`, `naps/NAP-THEME.md` at `377bf939`.

Wire: `theme.get {id}` → `theme.get.result {id, theme}` or `{id, error}`;
push `theme.changed {theme}` (no `id`) to every endpoint with `theme` exposed.

`Theme` JSON: `{colors: {background, text, primary}, fonts?: {body?, title?},
background?: {url, mode, mime}, title?}`; a font is `{name, url}`. The host reports
the active theme as JSON (`HostEvent.themeChanged`); a host theme without all three
colours is not a valid `Theme` and is ignored (the type makes "all three colours in
every payload" hold).
-/

namespace Napplet.Run.Theme

open NapTheme

structure St where
  current : Option Theme

def St.init : St := ⟨none⟩

inductive Req where
  | get (id : String)
  deriving DecidableEq, Repr

/-! ### Theme JSON -/

def fontJson (f : ThemeFont) : Json := .obj [("name", .str f.name), ("url", .str f.url)]

def fontOf? (j : Json) : Option ThemeFont := do
  some ⟨← j.getStr? "name", ← j.getStr? "url"⟩

def optField {α : Type} (j : Json) (k : String) (f : Json → Option α) : Option (Option α) :=
  match j.get? k with
  | none => some none
  | some v => (f v).map some

def themeJson (t : Theme) : Json :=
  let fonts : Option Json :=
    if t.body.isNone && t.titleFont.isNone then none
    else some (Json.mkObj [("body", t.body.map fontJson), ("title", t.titleFont.map fontJson)])
  Json.mkObj
    [("colors", some (.obj [("background", .str t.colors.background), ("text", .str t.colors.text),
                            ("primary", .str t.colors.primary)])),
     ("fonts", fonts),
     ("background", t.background.map fun b =>
        .obj [("url", .str b.url), ("mode", .str b.mode), ("mime", .str b.mime)]),
     ("title", t.title.map .str)]

def themeOf? (j : Json) : Option Theme := do
  let c ← j.get? "colors"
  let colors : ThemeColors := ⟨← c.getStr? "background", ← c.getStr? "text", ← c.getStr? "primary"⟩
  let fonts ← optField j "fonts" some
  let body ← match fonts with
    | none => some none
    | some fs => optField fs "body" fontOf?
  let titleFont ← match fonts with
    | none => some none
    | some fs => optField fs "title" fontOf?
  let background ← optField j "background" fun b => do
    some ⟨← b.getStr? "url", ← b.getStr? "mode", ← b.getStr? "mime"⟩
  let title ← optField j "title" Json.asStr?
  some { colors, body, titleFont, background, title }

/-! ### Codec -/

def decode (j : Json) : Decoded Req :=
  if j.getStr? "type" = some "theme.get" then
    match reqId? j with
    | some id => .ok (.get id)
    | none => .reject []
  else .unknown

def encodeReq : Req → Json
  | .get id => Json.msg "theme.get" [("id", some (.str id))]

def encodeOut : ThemeOut → PortId × Json
  | .getResult to id (some t) _ => (to, Json.msg "theme.get.result" [("id", some (.str id)), ("theme", some (themeJson t))])
  | .getResult to id none e => (to, Json.msg "theme.get.result" [("id", some (.str id)), ("error", (e.getD "no active theme") |> Json.str |> some)])
  | .changed to t => (to, Json.msg "theme.changed" [("theme", some (themeJson t))])

def sendOut (o : ThemeOut) : Eff := .send (encodeOut o).1 (encodeOut o).2

/-! ### Component -/

def handle (_h : Host) (_w : World) (cx : Ctx) (s : St) : Req → St × List Eff
  | .get id => (s, [sendOut (get cx.port id s.current)])

def onEvent (_h : Host) (w : World) (s : St) : HostEvent → St × List Eff
  | .themeChanged (some j) =>
    match themeOf? j with
    | some t => (⟨some t⟩, (broadcast (w.live.map fun c => (c.port, c.exposed)) t).map sendOut)
    | none => (s, [])
  | .themeChanged none => (⟨none⟩, [])
  | _ => (s, [])

def drop (s : St) (_p : PortId) : St × List Eff := (s, [])

def mentions (_s : St) (_p : PortId) : Bool := false

/-! ### Properties -/

theorem decode_encodeReq (r : Req) : decode (encodeReq r) = .ok r := by
  cases r; simp [decode, encodeReq, Json.msg, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, reqId?]

theorem themeOf?_themeJson (t : Theme) : themeOf? (themeJson t) = some t := by
  obtain ⟨⟨bg, tx, pr⟩, body, tf, back, title⟩ := t
  cases body <;> cases tf <;> cases back <;> cases title <;>
    simp [themeOf?, themeJson, Json.mkObj, Json.getStr?, Json.get?, Json.lookup, optField,
      fontOf?, fontJson, Json.asStr?]

/-- `theme.changed` reaches only endpoints that have `theme` exposed. -/
theorem changed_only_exposed (h : Host) (w : World) (s : St) (j : Json) (p : PortId) (m : Json)
    (hm : Eff.send p m ∈ (onEvent h w s (.themeChanged (some j))).2) :
    ∃ c ∈ w.live, c.port = p ∧ Domain.theme ∈ c.exposed := by
  simp only [onEvent] at hm
  split at hm
  · rename_i t _
    simp only [List.mem_map] at hm
    obtain ⟨o, ho, he⟩ := hm
    cases o with
    | getResult => simp [broadcast] at ho
    | changed to t' =>
      obtain ⟨ds, hmem, hd⟩ := broadcast_only_exposed ho
      simp only [sendOut, encodeOut, Eff.send.injEq] at he
      simp only [List.mem_map] at hmem
      obtain ⟨c, hc, hce⟩ := hmem
      simp at hce
      exact ⟨c, hc, by rw [hce.1, he.1], hce.2 ▸ hd⟩
  · simp at hm

/-- Every theme payload sent carries all three colours (they are fields of `Theme`). -/
theorem payload_has_colors (t : Theme) :
    ((themeJson t).get? "colors").bind (·.getStr? "background") = some t.colors.background ∧
    ((themeJson t).get? "colors").bind (·.getStr? "text") = some t.colors.text ∧
    ((themeJson t).get? "colors").bind (·.getStr? "primary") = some t.colors.primary := by
  obtain ⟨⟨bg, tx, pr⟩, body, tf, back, title⟩ := t
  cases body <;> cases tf <;> cases back <;> cases title <;>
    simp [themeJson, Json.mkObj, Json.get?, Json.lookup, Json.getStr?]

theorem drop_clears (s : St) (p : PortId) : mentions (drop s p).1 p = false := rfl

/-! ### Vectors -/

#guard decode (Json.parse! "{ \"type\": \"theme.get\", \"id\": \"t1\" }") matches .ok (.get "t1")
#guard (themeOf? (Json.parse! "{\"colors\": { \"background\": \"#1a1a2e\", \"text\": \"#e0e0e0\", \"primary\": \"#6c3ce0\" }, \"fonts\": { \"body\": { \"name\": \"Inter\", \"url\": \"https://example.com/inter.woff2\" }, \"title\": { \"name\": \"Playfair Display\", \"url\": \"https://example.com/playfair.woff2\" } }, \"background\": { \"url\": \"https://example.com/bg.jpg\", \"mode\": \"cover\", \"mime\": \"image/jpeg\" }, \"title\": \"MK Dark Theme\"}")).isSome
#guard (themeOf? (Json.parse! "{\"colors\": { \"background\": \"#1a1a2e\", \"text\": \"#e0e0e0\" }}")).isNone

end Napplet.Run.Theme
