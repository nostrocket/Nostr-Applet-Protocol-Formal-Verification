/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.BindingApi
import Napplet.Srcdoc

/-!
# The bootstrap script

`bootstrapJs exposed` is the JavaScript the host injects (`Srcdoc.buildSrcdoc`) before any
napplet script. It implements `Binding.lean`:

* **One hello.** It creates a `MessageChannel`, keeps `port1` in its closure and calls
  `window.parent.postMessage({type: "napplet.hello"}, "*", [port2])` once (`Binding.boot`).
* **Domain surface.** `window.napplet` is a frozen object holding exactly the `exposed`
  domains, each with the methods of `BindingApi.methods` for that domain. Request
  methods take the envelope members as one object (the NAP tables' parameters, by wire
  name) and return a promise for the result envelope; fire-and-forget methods post;
  `on…` methods register a push handler under the push type and, when given, a routing
  value (`Binding.routeField`); `shell.ready` resolves with the sticky `shell.init`.
  Methods the tables mark local or as sugar are not wire methods and are not installed.
* **Correlation.** Each request gets a fresh id; a message settles the pending request
  with its `id` only if its type is one `Binding.resultTypes` accepts, once
  (`Binding.settle`); `Binding.noResult` types settle nothing.
* **Buffering.** Pushes for `Binding.retainedTypes` wait for a handler; `stickyTypes`
  are replayed to every later handler; late media pushes for an ended session are
  dropped (`Binding.receive`, `Binding.register`).

The data tables in the script (`API`, `RESULTS`, `NO_RESULT`, `RETAINED`, `STICKY`,
`RETIRED_LATE`, `ROUTE`) are renderings of the Lean definitions they name, spliced between
literal code (`rawJs`). Results:
* `rawJs_api`: the script's method table is the rendering of `BindingApi.methods`;
* `bootstrap_safe`: for every exposure, the script contains no `<`, so it is safe inside
  `<script>` (`Srcdoc.safeText`), and `srcdoc_order` holds for the shipped `srcdoc`;
* vectors parse the tables back out of the text, check them against `Binding.lean`, check
  that the script posts exactly one hello, and that `noLt` leaves the script unchanged.
-/

namespace Napplet.Bootstrap

open BindingApi

def wireJson : Wire → Json
  | .local => .arr [.str "local"]
  | .req t inst => .arr [.str "req", .str t, .bool inst]
  | .fire t => .arr [.str "fire", .str t]
  | .push t => .arr [.str "push", .str t]
  | .ready s r => .arr [.str "ready", .str s, .str r]

/-- `{domain: [[op, wire...], ...]}` in table order. -/
def apiJson : Json :=
  let doms := (methods.map (·.domain)).foldl (fun acc d => if acc.contains d then acc else acc ++ [d]) []
  .obj (doms.map fun d =>
    (d, .arr ((methods.filter (·.domain == d)).map fun m => .arr [.str m.op, wireJson m.wire])))

def reqTypes : List String :=
  methods.filterMap fun m => match m.wire with | .req t _ => some t | _ => none

/-- Result types that differ from `<type>.result`. -/
def resultsJson : Json :=
  .obj (reqTypes.filterMap fun t =>
    if Binding.resultTypes t == [resultType t] then none
    else some (t, Json.strs (Binding.resultTypes t)))

def pushTypes : List String :=
  methods.filterMap fun m => match m.wire with
    | .push t => some t | .ready _ r => some r | _ => none

def routeJson : Json :=
  .obj ((pushTypes ++ Binding.retiredLateTypes ++ ["inc.channel.event", "inc.channel.closed",
      "relay.event", "relay.eose", "relay.closed", "outbox.event", "outbox.closed",
      "pow.state", "pow.progress", "pow.done", "pow.error", "inc.event", "media.session.ended"]).foldl
    (fun acc t => match Binding.routeField t with
      | some f => if acc.any (·.1 == t) then acc else acc ++ [(t, .str f)]
      | none => acc) [])

/-! ### The script text

`rawJs` is the script: literal code (`tpl0` … `tpl8`, which contain no `<`) around the
JSON tables, each the rendering of the Lean definition it names. `rawJs_api` states that
the method table in the script is `BindingApi.methods`. -/

def tpl0 : String := "(function () {
  \"use strict\";
  var EXPOSED = "
def tpl1 : String := ";
  var API = "
def tpl2 : String := ";
  var RESULTS = "
def tpl3 : String := ";
  var NO_RESULT = "
def tpl4 : String := ";
  var RETAINED = "
def tpl5 : String := ";
  var STICKY = "
def tpl6 : String := ";
  var RETIRED_LATE = "
def tpl7 : String := ";
  var ROUTE = "
def tpl8 : String := ";
  var channel = new MessageChannel();
  var port = channel.port1;
  var next = 0;
  var pending = new Map();
  var handlers = [];
  var buffer = [];
  var sticky = [];
  function routeOf(m) {
    var f = ROUTE[m.type];
    return f && typeof m[f] === \"string\" ? m[f] : null;
  }
  function same(a, t, r) { return a.type === t && a.route === r; }
  function resultTypes(t) { return RESULTS[t] || [t + \".result\"]; }
  function retired(t, r) {
    return RETIRED_LATE.indexOf(t) >= 0 && r !== null &&
      sticky.some(function (s) { return same(s, \"media.session.ended\", r); });
  }
  function deliver(t, r, m) {
    handlers.forEach(function (h) { if (same(h, t, r)) { h.fn(m); } });
  }
  function pushIn(m) {
    var t = m.type, r = routeOf(m);
    if (retired(t, r)) { return; }
    var handled = handlers.some(function (h) { return same(h, t, r); });
    if (STICKY.indexOf(t) >= 0) { sticky.push({ type: t, route: r, msg: m }); }
    else if (!handled && RETAINED.indexOf(t) >= 0) { buffer.push({ type: t, route: r, msg: m }); return; }
    if (handled) { deliver(t, r, m); }
  }
  port.onmessage = function (e) {
    var m = e.data;
    if (!m || typeof m.type !== \"string\") { return; }
    if (typeof m.id === \"string\" && pending.has(m.id)) {
      var p = pending.get(m.id);
      if (p.accepts.indexOf(m.type) >= 0) { pending.delete(m.id); p.resolve(m); return; }
    }
    pushIn(m);
  };
  function request(t, params, extra) {
    var id = \"r\" + (next++);
    var m = Object.assign({}, params || {}, extra || {}, { type: t, id: id });
    if (NO_RESULT.indexOf(t) >= 0) { port.postMessage(m); return Promise.resolve(m); }
    return new Promise(function (resolve) {
      pending.set(id, { accepts: resultTypes(t), resolve: resolve });
      port.postMessage(m);
    });
  }
  function fire(t, params) { port.postMessage(Object.assign({}, params || {}, { type: t })); }
  function on(t, route, fn) {
    if (typeof route === \"function\") { fn = route; route = null; }
    var h = { type: t, route: route === undefined ? null : route, fn: fn };
    handlers.push(h);
    var mine = buffer.filter(function (b) { return same(b, h.type, h.route); });
    buffer = buffer.filter(function (b) { return !same(b, h.type, h.route); });
    mine.forEach(function (b) { fn(b.msg); });
    sticky.forEach(function (s) { if (same(s, h.type, h.route)) { fn(s.msg); } });
    return { close: function () { handlers = handlers.filter(function (x) { return x !== h; }); } };
  }
  function method(w) {
    switch (w[0]) {
      case \"req\": return function (params) { return request(w[1], params, w[2] ? { scope: \"instance\" } : null); };
      case \"fire\": return function (params) { fire(w[1], params); };
      case \"push\": return function (route, fn) { return on(w[1], route, fn); };
      case \"ready\": return function () {
        return new Promise(function (resolve) { on(w[2], null, resolve); fire(w[1]); });
      };
      default: return null;
    }
  }
  function install(obj, path, fn) {
    var parts = path.split(\".\");
    var last = parts.pop();
    parts.forEach(function (q) { if (!obj[q]) { obj[q] = {}; } obj = obj[q]; });
    obj[last] = fn;
  }
  var napplet = {};
  EXPOSED.forEach(function (d) {
    var o = {};
    (API[d] || []).forEach(function (row) {
      var fn = method(row[1]);
      if (fn && !/^[A-Z]/.test(row[0])) { install(o, row[0], fn); }
    });
    napplet[d] = Object.freeze(o);
  });
  Object.defineProperty(window, \"napplet\", { value: Object.freeze(napplet), writable: false, configurable: false });
  window.parent.postMessage({ type: \"napplet.hello\" }, \"*\", [channel.port2]);
})();
"

/-- The exposure list as JSON. -/
def exposedJson (exposed : List Domain) : String := (Json.strs (exposed.map Domain.name)).render

def rawJs (exposed : List Domain) : String :=
  tpl0 ++ exposedJson exposed ++ tpl1 ++ apiJson.render ++ tpl2 ++ resultsJson.render ++ tpl3 ++ (Json.strs Binding.noResult).render ++ tpl4 ++ (Json.strs Binding.retainedTypes).render ++ tpl5 ++ (Json.strs Binding.stickyTypes).render ++ tpl6 ++ (Json.strs Binding.retiredLateTypes).render ++ tpl7 ++ routeJson.render ++ tpl8

/-- **The script's method table is `BindingApi.methods`**: the text after `var API = ` is
the rendering of `apiJson`, which lists `BindingApi.methods` in table order. -/
theorem rawJs_api (exposed : List Domain) :
    tpl1 = ";\n  var API = " ∧
    rawJs exposed = (tpl0 ++ exposedJson exposed ++ tpl1) ++ apiJson.render ++
      (tpl2 ++ resultsJson.render ++ tpl3 ++ (Json.strs Binding.noResult).render ++ tpl4 ++
        (Json.strs Binding.retainedTypes).render ++ tpl5 ++ (Json.strs Binding.stickyTypes).render ++
        tpl6 ++ (Json.strs Binding.retiredLateTypes).render ++ tpl7 ++ routeJson.render ++ tpl8) := by
  refine ⟨rfl, ?_⟩
  simp only [rawJs, String.append_assoc]

/-- Replace every `<` by the JSON/JavaScript string escape `\u003c`. The code in `rawJs`
has no `<` (vector below), so this only touches `<` inside JSON strings, where the escape
means the same character. -/
def noLt (s : String) : String :=
  String.ofList (s.toList.flatMap fun c => if c = '<' then "\\u003c".toList else [c])

theorem noLt_spec (s : String) : '<' ∉ (noLt s).toList := by
  simp only [noLt, String.toList_ofList, List.mem_flatMap, not_exists, not_and]
  intro c _
  split
  · decide
  · rename_i h; simp only [List.mem_singleton]; exact fun e => h e.symm

/-- The bootstrap script for a napplet exposed to `exposed`. -/
def bootstrapJs (exposed : List Domain) : String := noLt (rawJs exposed)

/-- **The bootstrap is safe inside `<script>`, for every exposure.** -/
theorem bootstrap_safe (exposed : List Domain) : Srcdoc.scriptSafe (bootstrapJs exposed) = true :=
  Srcdoc.scriptSafe_of_no_lt (noLt_spec _)

/-! ### Checks -/

def allDomains : List Domain :=
  [.shell, .intent, .inc, .theme, .identity, .relay, .storage, .keys, .media, .notify,
   .resource, .config, .upload, .value, .outbox, .cvm, .link, .pow, .display]

/-- The JSON after `var <name> = ` up to the end of that line, parsed back from the text. -/
def tableIn (js name : String) : Option Json :=
  match (js.splitOn ("var " ++ name ++ " = ")) with
  | [_, rest] => Json.parse ((rest.splitOn ";\n").headD "")
  | _ => none

def count (js pat : String) : Nat := (js.splitOn pat).length - 1

def js : String := bootstrapJs allDomains

-- the method table in the script is BindingApi.methods
#guard tableIn js "API" == some apiJson
#guard match apiJson with
  | .obj kvs => kvs.flatMap (fun (d, v) => (v.asArr?.getD []).map fun r => (d, r)) ==
      methods.map fun m => (m.domain, .arr [.str m.op, wireJson m.wire])
  | _ => false
-- correlation and buffering tables are Binding.lean's
#guard tableIn js "NO_RESULT" == some (Json.strs Binding.noResult)
#guard tableIn js "RETAINED" == some (Json.strs Binding.retainedTypes)
#guard tableIn js "STICKY" == some (Json.strs Binding.stickyTypes)
#guard tableIn js "RETIRED_LATE" == some (Json.strs Binding.retiredLateTypes)
#guard reqTypes.all fun t =>
  match (tableIn js "RESULTS").bind (·.get? t) with
  | some v => v.asStrs? == some (Binding.resultTypes t)
  | none => Binding.resultTypes t == [resultType t]
#guard pushTypes.all fun t =>
  ((tableIn js "ROUTE").bind (·.getStr? t)) == Binding.routeField t
-- exactly the exposed domains
#guard tableIn (bootstrapJs [.storage, .theme]) "EXPOSED" == some (Json.strs ["storage", "theme"])
-- exactly one hello, and only through window.parent
#guard count js "postMessage({ type: \"napplet.hello\" }" == 1
#guard count js "window.parent.postMessage" == 1
#guard count js "napplet.hello" == 1
-- no placeholder left
#guard count js "@" == 0
-- safe inside <script>
#guard Srcdoc.scriptSafe js

end Napplet.Bootstrap

namespace Napplet.Bootstrap

/-- The `srcdoc` the host builds for verified bytes and an exposure set. -/
def srcdoc (bytes : Bytes) (exposed : List Domain) : Bytes :=
  Srcdoc.buildSrcdoc bytes Srcdoc.baselineCsp (bootstrapJs exposed)

/-- **The shipped `srcdoc`.** In parse order: element-free napplet tokens, a `<head>`
start tag, the baseline CSP `<meta>`, the bootstrap `<script>`, exactly the bootstrap
text, the injected `</script>`, then the napplet's remaining bytes. -/
theorem srcdoc_order (bytes : Bytes) (exposed : List Domain) :
    ∃ ts h p q, (∀ t ∈ ts, t.allowed = true) ∧ h.isHead = true ∧
      Srcdoc.stripBom (bytes.map UInt8.toNat) = p ++ q ∧
      srcdoc bytes exposed = (Srcdoc.buildCodes (bytes.map UInt8.toNat) Srcdoc.baselineCsp (bootstrapJs exposed)).map Nat.toUInt8 ∧
      Srcdoc.lexR (ts.length + 3) (Srcdoc.buildCodes (bytes.map UInt8.toNat) Srcdoc.baselineCsp (bootstrapJs exposed)) =
        (ts ++ [h, .startTag (Srcdoc.ascii "meta") (Srcdoc.cspMeta Srcdoc.baselineCsp),
                .startTag (Srcdoc.ascii "script") Srcdoc.scriptOpen],
         Srcdoc.codes (bootstrapJs exposed) ++ Srcdoc.scriptClose ++ q) ∧
      Srcdoc.scriptData (Srcdoc.codes (bootstrapJs exposed) ++ Srcdoc.scriptClose ++ q) =
        some (Srcdoc.codes (bootstrapJs exposed), Srcdoc.scriptClose ++ q) ∧
      Srcdoc.step (Srcdoc.scriptClose ++ q) = some (.endTag (Srcdoc.ascii "script"), Srcdoc.scriptClose, q) := by
  obtain ⟨ts, h, p, q, h1, h2, h3, h4, h5, h6⟩ :=
    Srcdoc.bootstrap_first (bytes.map UInt8.toNat) Srcdoc.baselineCsp (bootstrapJs exposed) (bootstrap_safe exposed)
  exact ⟨ts, h, p, q, h1, h2, h3, rfl, h4, h5, h6⟩

-- the real script is the one injected
-- `noLt` changes nothing: the script has no `<` at all
#guard (rawJs allDomains).toList.all (· ≠ '<')
#guard bootstrapJs allDomains == rawJs allDomains

-- end to end: the baseline CSP and the real bootstrap come first in head
#guard
  let doc := "<!doctype html><HTML><head><script>napplet()</script>".toUTF8.toList
  let out := Srcdoc.buildCodes (doc.map UInt8.toNat) Srcdoc.baselineCsp js
  match (Srcdoc.lexN 50 out).dropWhile Srcdoc.Tok.allowed with
  | h :: m :: sc :: _ => h.isHead && m == .startTag (Srcdoc.ascii "meta") (Srcdoc.cspMeta Srcdoc.baselineCsp) &&
      sc == .startTag (Srcdoc.ascii "script") Srcdoc.scriptOpen
  | _ => false

end Napplet.Bootstrap
