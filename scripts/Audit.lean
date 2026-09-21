/-
Axiom audit of the headline results: the Palomar surface in `Solution.lean`
(Theorem A, Corollary A′, Theorem F for `F₅` and `F₁₃`) and the kernel-checked
certificates of the library in `lean/` (Theorems B and B′, Theorem F).

`scripts/check_axioms.py` runs this file and fails unless every theorem below
depends on `propext`, `Classical.choice` and `Quot.sound` only.

The `bv_decide` census under `lean/census/` is not audited here: it is
corroboration only, is not part of any library, and depends on native
evaluation by design (see the README, "Three trust levels").
-/
import Solution
import OneGenerated1518
import L2Cert
import H2Cert
import FamilyF5
import FamilyF13

#print axioms Magma1518.table
#print axioms Magma1518.cube
#print axioms Magma1518.words_in_T
#print axioms Magma1518.one_or_three
#print axioms Magma1518.familyF5_law1518
#print axioms Magma1518.familyF5_refutes
#print axioms Magma1518.familyF5_squaring_order
#print axioms Magma1518.familyF13_law1518
#print axioms Magma1518.familyF13_refutes
#print axioms Magma1518.familyF13_squaring_order
#print axioms OneGenerated1518.table
#print axioms OneGenerated1518.words_in_T
#print axioms OneGenerated1518.one_or_three
#print axioms L2.cert_47
#print axioms L2.cert_614
#print axioms L2.cert_817
#print axioms L2.cert_3862
#print axioms L2.cert_359
#print axioms H2.homotopy
#print axioms FamilyF5.law1518
#print axioms FamilyF5.not47
#print axioms FamilyF5.not614
#print axioms FamilyF5.not817
#print axioms FamilyF5.not3862
#print axioms FamilyF5.sq_cubed_not_id
#print axioms FamilyF5.sq_pow12_id
#print axioms FamilyF13.law1518
#print axioms FamilyF13.not47
#print axioms FamilyF13.not614
#print axioms FamilyF13.not817
#print axioms FamilyF13.not3862
#print axioms FamilyF13.sq_cubed_not_id
#print axioms FamilyF13.sq_pow12_id
