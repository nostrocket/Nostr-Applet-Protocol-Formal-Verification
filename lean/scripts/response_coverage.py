#!/usr/bin/env python3
"""For every upstream shell->napplet example (`<- {...}`), report whether a #guard in
the model compares output against that exact JSON (canonical form)."""
import json, re, sys, glob
up = sys.argv[1].rstrip('/') + '/'
names = {"SHELL":"Shell","INTENT":"Intent","INC":"Inc","THEME":"Theme","IDENTITY":"Identity",
 "RELAY":"Relay","STORAGE":"Storage","KEYS":"Keys","MEDIA":"Media","NOTIFY":"Notify",
 "RESOURCE":"Resource","CONFIG":"Config","UPLOAD":"Upload","VALUE":"Value","OUTBOX":"Outbox",
 "CVM":"Cvm","LINK":"Link","POW":"Pow","DISPLAY":"Display"}
def canon(o): return json.dumps(o, sort_keys=True)
# collect JSON literals appearing in Lean sources (Json.parse! "...")
lean = ""
for f in glob.glob("Napplet/**/*.lean", recursive=True): lean += open(f).read()
lits = set()
for m in re.finditer(r'"((?:[^"\\]|\\.)*)"', lean):
    raw = m.group(1)
    cands = [raw, raw.replace('\\"', '"').replace('\\\\', '\\')]
    try: cands.append(json.loads('"' + raw + '"'))
    except Exception: pass
    for t in cands:
        try:
            o = json.loads(t)
            if isinstance(o, dict): lits.add(canon(o))
        except Exception: pass
tot = hit = 0; miss = {}
for N, f in names.items():
    lines = open(up + f'NAP-{N}.md').read().split('\n'); i = 0
    while i < len(lines):
        m = re.match(r'\s*(?:opener |target )?<-\s*(\{.*)$', lines[i])
        if not m: i += 1; continue
        txt, j, obj = m.group(1), i, None
        while True:
            try: obj = json.loads(txt); break
            except Exception:
                j += 1
                if j >= len(lines) or j - i > 80 or re.match(r'\s*(<-|->|```)', lines[j]): break
                txt += '\n' + lines[j]
        if isinstance(obj, dict):
            tot += 1
            if canon(obj) in lits: hit += 1
            else: miss.setdefault(N, []).append(json.dumps(obj)[:110])
        i = j + 1
print(f"{hit}/{tot} upstream response examples reproduced verbatim by guards")
for k, v in miss.items():
    print(k, len(v));
    for x in v: print("   ", x)
