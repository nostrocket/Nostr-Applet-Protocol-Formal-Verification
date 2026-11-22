#!/usr/bin/env python3
"""Derive the machine-readable method table from the API tables in BindingApi.lean.

Prints the Lean list for `BindingApi.methods`. With --check, compares it with the
definition in BindingApi.lean and exits non-zero on any difference (run in CI).
"""
import re, sys

SRC = "Napplet/BindingApi.lean"
REQ_SINGLE = {"resource.info", "resource.bytes", "resource.bytesMany"}

def rows(text):
    dom = None
    for line in text.splitlines():
        m = re.match(r"### `window\.napplet\.(\w+)`", line)
        if m:
            dom = m.group(1)
            continue
        if line.startswith("| `") and dom:
            cols = [c.strip() for c in line.strip("|").split("|")]
            yield dom, cols[0].strip("`"), cols[-1]

def wire(op, w):
    ticks = re.findall(r"`([^`]*)`", w)
    if w.startswith("local") or "sugar over" in w or "wrapper over" in w:
        return ".local"
    if w.startswith("resolves after"):
        return '.ready "%s" "%s"' % (ticks[0], ticks[1])
    if w.startswith("fires after"):
        return '.push "%s"' % ticks[0]
    t = ticks[0]
    if "/" in w or " plus " in w:
        inst = 'scope: "instance"' in w
        return '.req "%s"%s' % (t, " true" if inst else " false")
    last = op.split(".")[-1]
    if last.startswith("on"):
        return '.push "%s"' % t
    if t in REQ_SINGLE:
        return '.req "%s" false' % t
    return '.fire "%s"' % t

def table(text):
    return ['  ⟨"%s", "%s", %s⟩' % (d, op, wire(op, w)) for d, op, w in rows(text)]

text = open(SRC).read()
lines = table(text)
if "--check" in sys.argv:
    m = re.search(r"def methods : List Method := \[\n(.*?)\n\]", text, re.S)
    have = [l.rstrip(",") for l in m.group(1).splitlines()] if m else []
    if have != lines:
        print("BindingApi.methods does not match the API tables", file=sys.stderr)
        for a, b in zip(have, lines):
            if a != b:
                print("  have: %s\n  want: %s" % (a, b), file=sys.stderr)
        sys.exit(1)
    print("BindingApi.methods matches the %d table rows" % len(lines))
else:
    print(",\n".join(lines))
