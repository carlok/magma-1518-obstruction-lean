#!/bin/sh
# Regenerate the complete labelled model sets of the four hypothesis laws at sizes 2..4 with Mace4 2009-11A.
# clear(lnh) disables Mace4's isomorph pruning so the enumeration is complete; the adversary script audits
# sizes 2 and 3 against plain enumeration and reduces to isomorphism classes itself.
set -eu
D="${1:-audit-data}/m4"; mkdir -p "$D"; cd "$D"
mace4 -h < /dev/null 2>&1 | head -2 || true
for e in 879 1518 2054 2650; do
  for n in 2 3 4; do mace4 -n"$n" -m -1 < "e${e}_nolnh.in" > "e${e}_${n}_nolnh.out" 2>/dev/null; echo "E$e n=$n models=$(grep -c '^interpretation' "e${e}_${n}_nolnh.out")"; done
done
