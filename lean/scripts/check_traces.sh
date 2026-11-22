#!/bin/sh
# Replay every trace through napplet-oracle and compare with the reference outputs byte
# for byte. Run from lean/ after `lake build`.
set -e
fail=0
for f in traces/*.in.ndjson; do
  n=${f%.in.ndjson}
  if ! .lake/build/bin/napplet-oracle < "$f" | cmp -s - "$n.out.ndjson"; then
    echo "trace mismatch: $n"
    fail=1
  fi
done
[ "$fail" = 0 ] && echo "all traces match"
exit $fail
