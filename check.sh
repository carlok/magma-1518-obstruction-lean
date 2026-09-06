#!/bin/sh
# Re-check every Lean file. Requires elan with leanprover/lean4:v4.33.0 (see lean-toolchain).
set -e
cd "$(dirname "$0")"
LEAN="$(lean +v4.33.0 --print-prefix)/bin/lean"
for f in lean/OneGenerated1518.lean lean/L2Cert.lean lean/H2Cert.lean lean/FamilyF5.lean lean/FamilyF13.lean lean/census/CensusBridge.lean; do
  echo "== $f"; "$LEAN" -M 8192 "$f" | grep -E "axioms|error"
done
for n in 2 3 4 5 6 7 8; do
  echo "== lean/census/Census1518_$n.lean"; "$LEAN" -M 24576 "lean/census/Census1518_$n.lean" | grep -E "axioms|error" | head -3
done
