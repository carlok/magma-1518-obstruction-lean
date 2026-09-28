module

/-
Axiom audit of the headline results: the Palomar surface in `Solution.lean`
(Theorem A and Corollary A′) and the kernel-checked certificates of the library
in `lean/` (Theorems B and B′, and the F₅ and F₁₃ members of Theorem F, which
are audited there under their library names rather than through the Palomar
surface).

`scripts/check_axioms.py` runs this file and fails unless every theorem below
depends on `propext`, `Classical.choice` and `Quot.sound` only.

The `bv_decide` census under `lean/census/` is not audited here: it is
corroboration only, is not part of any library, and depends on native
evaluation by design (see the README, "Three trust levels").
-/
public import Solution
public import OneGenerated1518
public import L2Cert
public import H2Cert
public import FamilyF5
public import FamilyF13

@[expose] public section


#print axioms Magma1518.table
#print axioms Magma1518.cube
#print axioms Magma1518.words_in_T
#print axioms Magma1518.one_or_three
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
