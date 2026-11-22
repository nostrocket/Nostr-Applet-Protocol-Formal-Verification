#!/usr/bin/env bash
# Fetch every upstream spec at the commit recorded in lean/README.md into DIR, then run
# the coverage checks against those exact texts.
#   scripts/verify_upstream.sh DIR
set -euo pipefail
dir=${1:?usage: verify_upstream.sh DIR}; mkdir -p "$dir"
raw() { gh api -H "Accept: application/vnd.github.raw" "repos/$1/contents/$2?ref=$3"; }
raw dskvr/nips 5D.md f60550c3409d6d81a875088ec83e660571e10504 > "$dir/5D.md"
# web projection with PR #148 (intent.launch binding)
raw napplet/naps projections/web.md 9e25e6768b0528e5848297ce0b338bb3c94302bf > "$dir/web.md"
while read -r w sha; do raw napplet/naps "naps/NAP-$w.md" "$sha" > "$dir/NAP-$w.md"; done <<'T'
SHELL b9b0b7e38d99d9e3ad0b79e3de61b349156ee41f
INC 377bf939c6c906817084b43dd21d424de646dbc2
THEME 377bf939c6c906817084b43dd21d424de646dbc2
IDENTITY c13e8891ca6375bd0063b6dbd995ba42088df75e
RELAY 9f30b3505335a52c574ff570576687d6467021ff
STORAGE 4f4cf0ca7ecbd24c284a5d63bcd85e3de6af37ca
KEYS 8869a4cf77b023f4b049f47c546910a0280dc1a6
MEDIA 7806f438530251fce5129f8e6239d6b642278759
NOTIFY 67877ef6c31ec8acee3125c1d8b4c781010e37dc
CONFIG bed9cb5b1e7c9b5babee8870aa18b12949af1d62
VALUE e468764d9f8a4f40107244cebed921bbebc0a0bf
CVM 28cf1bdb5c6412bfbfcecb79a5a5121e18376f2f
OUTBOX 8865f73d52a4864afee145f28d26520476273927
UPLOAD f5cc981e527e2cc1572793a7a6e5082e5271ac49
POW d85b4252f26fccd6c61bba18429ca9a6c0559210
LINK 100e5c939ae6b1ea82cc58587c6da45a1cf8a760
RESOURCE ae5b9c64ab8a4d8909f288829a01e99d6bd713bc
DISPLAY 2c2e1b5ca3849dbab8c3a721704e30646a641079
T
# NAP-INTENT: master with PR #148 (launch) and PR #128 (selected-instance delivery). Both
# branch from master's text; only their changelog lines overlap, which --union keeps.
raw napplet/naps naps/NAP-INTENT.md 377bf939c6c906817084b43dd21d424de646dbc2 > "$dir/INTENT-base.md"
raw napplet/naps naps/NAP-INTENT.md 9e25e6768b0528e5848297ce0b338bb3c94302bf > "$dir/NAP-INTENT.md"
raw napplet/naps naps/NAP-INTENT.md 74f9bf85ebb83b50b7b2ad8308a835d5f3113cd9 > "$dir/INTENT-128.md"
git merge-file --union "$dir/NAP-INTENT.md" "$dir/INTENT-base.md" "$dir/INTENT-128.md"
rm "$dir/INTENT-base.md" "$dir/INTENT-128.md"
python3 scripts/upstream_examples.py "$dir"
python3 scripts/response_coverage.py "$dir"
lake build Napplet.Test.UpstreamExamples Napplet.Test.E2E
