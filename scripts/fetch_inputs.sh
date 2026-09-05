#!/bin/sh
# Fetch the pinned inputs for the stage-1 audit reproduction into $1 (default: ./audit-data).
# Read-only GitHub API access through gh; nothing is executed from these repositories.
set -eu
D="${1:-audit-data}"; mkdir -p "$D/etp" "$D/pm"
ETP=88088faaccfaa05f268cf4d007ceb5286630ba24   # teorth/equational_theories, 2026-09-02
PM=89ed607086103535a5ef3b6174a1ff4da4023033    # carlok/parsimagma, 2026-09-02
gh api "repos/teorth/equational_theories/contents/data/equations.txt?ref=$ETP" --jq .content | base64 -d > "$D/etp/equations.txt"
for n in 930 937 938 939; do
  gh api "repos/teorth/equational_theories/contents/equational_theories/Generated/All4x4Tables/Refutation$n.lean?ref=$ETP" --jq .content | base64 -d > "$D/etp/Refutation$n.lean"
  python3 - "$D/etp/Refutation$n.lean" "$D/etp/table$n.json" <<'PY'
import re, sys
text = open(sys.argv[1]).read(); m = re.search(r"\[\[.*?\]\]", text, re.S)
rows = eval(m.group(0)); assert all(len(r) == len(rows) for r in rows)
open(sys.argv[2], "w").write(str(rows))
PY
done
gh api "repos/carlok/parsimagma/contents/data/etp/finite_uncovered.txt?ref=$PM" --jq .content | base64 -d > "$D/pm/finite_uncovered.txt"
echo "inputs in $D"; shasum -a 256 "$D"/etp/equations.txt "$D"/etp/table93*.json "$D"/pm/finite_uncovered.txt
