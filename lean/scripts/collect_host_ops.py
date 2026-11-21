#!/usr/bin/env python3
"""Print the '## Host operations' doc sections of every Napplet/Run/*.lean file."""
import glob, re, sys
out = []
for f in sorted(glob.glob("Napplet/Run/*.lean")):
    s = open(f).read()
    m = re.search(r"#+ Host operations[^\n]*\n(.*?)-/", s, re.S)
    if m:
        name = f.split("/")[-1][:-5]
        out.append(f"### {name.upper()} (`Napplet/Run/{name}.lean`)\n\n" + m.group(1).strip() + "\n")
print("\n".join(out))
