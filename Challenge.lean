/-!
# One-generated (1518 + 3862)-magmas are trivial or the Z/3 shift; an explicit family of finite 1518-magmas violating 47, 614, 817, 3862

Laws are numbered as in the Equational Theories Project (ETP, `teorth/equational_theories`): a law is an identity between
two words in a binary operation `◇`, and a magma satisfies it when the identity holds for all values of the variables.
Write `S x = x ◇ x`.

**Theorem A.** In every magma satisfying laws 1518 (`x = (y ◇ y) ◇ (x ◇ (y ◇ x))`) and 3862 (`x ◇ x = (x ◇ (x ◇ x)) ◇ x`),
for every `x` and all `u, v` in `T = {x, S x, S (S x)}` one has `u ◇ v = S v`, and `S (S (S x)) = x`.  Hence every word
in `x` lies in `T`, and `T` has one element or three distinct elements on which `◇` is the cyclic shift `u ◇ v = S v`.
So every one-generated magma satisfying 1518 and 3862 is the trivial magma or the Z/3 shift `x ◇ y = y + 1`.  This is the
statement Terence Tao conjectured on the Lean Zulip (Equational stream, "Austin pairs", 2024-11-29, message 485148288)
for finite magmas satisfying 1518 and all four of 47, 614, 817, 3862; here one target suffices and no finiteness is used.
Declarations `table`, `cube`, `words_in_T`, `one_or_three`.

**Theorem F (two members).** Let `R` be a commutative ring with `1/2` and an element `i` with `i² = −1`, and `M ≠ 0` an
`R`-module.  On `Z/3 × M` put `(x,s) ◇ (y,t) = (y+1, a[x][y]·s + b[x][y]·t)` with
`a = [[-(1+i)/2, -1/2, (1-i)/2], [(1-i)/2, -(1+i)/2, 1+i], [1+i, (1-i)/2, 2i]]` and
`b = [[1, (1+i)/2, -(1+i)], [1/2, 1, -2i], [(1+i)/2, 1/2, -2(1+i)]]`.  Then 1518 holds and 47, 614, 817, 3862 all fail,
and the squaring map has order 12.  Only the members `M = F_5` (15 elements, `i = 2`) and `M = F_13` (39 elements,
`i = 5`) are formalized here, by kernel evaluation of the finite tables; the general statement is verified by exact
arithmetic in `Q(i)` outside Lean (`scripts/basedep_family.py`) and is not part of this Challenge.  The 15-element member
is isomorphic to one of the six 15-element countermodels found by Bruno Le Floch and Jose Brox (Lean Zulip, October 2025)
and already present in the ETP as `Refutation939`; the 39-element member is new.
Declarations `familyF5_*`, `familyF13_*`.

**Not in this Challenge.** The cohomological results of the repository (`H²_1518 = 0` over the shift, the obstruction
theorem for constant-coefficient extensions) are proved in prose with kernel-checked certificate identities and are not
stated here.  Novelty is unknown: the ETP sources, the Lean Zulip Equational stream, the SAIR Zulip, arXiv and the Palomar
registry were searched (September 2026) without finding these statements; Theorem A may be folklore.

The definitions below are the ordinary ones; the finite tables are given by their coefficient matrices, not by lookup
tables.  Proofs are in `Solution.lean`, which restates each declaration and proves it from `lean/OneGenerated1518.lean`
(a transcription of equational proofs found by Vampire 5.1.0) and by `decide`.
-/

namespace Magma1518

/-- ETP law 1518: `x = (y ◇ y) ◇ (x ◇ (y ◇ x))`. -/
def Law1518 {G : Type} (op : G → G → G) : Prop := ∀ x y, x = (op (op y y) (op x (op y x)))

/-- ETP law 3862: `x ◇ x = (x ◇ (x ◇ x)) ◇ x`. -/
def Law3862 {G : Type} (op : G → G → G) : Prop := ∀ x, (op x x) = (op (op x (op x x)) x)

/-- ETP law 47: `x = x ◇ (x ◇ (x ◇ x))`. -/
def Law47 {G : Type} (op : G → G → G) : Prop := ∀ x, x = (op x (op x (op x x)))

/-- ETP law 614: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`. -/
def Law614 {G : Type} (op : G → G → G) : Prop := ∀ x, x = (op x (op x (op (op x x) x)))

/-- ETP law 817: `x = x ◇ ((x ◇ x) ◇ (x ◇ x))`. -/
def Law817 {G : Type} (op : G → G → G) : Prop := ∀ x, x = (op x (op (op x x) (op x x)))

/-- `T x = {x, S x, S (S x)}` with `S y = y ◇ y`: `inT op x y` says that `y` is one of the three. -/
def inT {G : Type} (op : G → G → G) (x y : G) : Prop := y = x ∨ y = op x x ∨ y = op (op x x) (op x x)

/-- Words in one generator: the free magma on one generator `v`. -/
inductive W where
  | v : W
  | m : W → W → W

/-- Evaluation of a word at `x`. -/
def ev {G : Type} (op : G → G → G) (x : G) : W → G
  | .v => x
  | .m a b => op (ev op x a) (ev op x b)

/-- Coefficient matrix `a` of Theorem F reduced modulo 5 with `i = 2` (`i² = −1`): over `Q(i)`,
    `a = [[-(1+i)/2, -1/2, (1-i)/2], [(1-i)/2, -(1+i)/2, 1+i], [1+i, (1-i)/2, 2i]]`. -/
def a5 : Fin 3 → Fin 3 → Fin 5
  | 0, 0 => 1
  | 0, 1 => 2
  | 0, 2 => 2
  | 1, 0 => 2
  | 1, 1 => 1
  | 1, 2 => 3
  | 2, 0 => 3
  | 2, 1 => 2
  | 2, 2 => 4

/-- Coefficient matrix `b` of Theorem F reduced modulo 5 with `i = 2`: over `Q(i)`,
    `b = [[1, (1+i)/2, -(1+i)], [1/2, 1, -2i], [(1+i)/2, 1/2, -2(1+i)]]`. -/
def b5 : Fin 3 → Fin 3 → Fin 5
  | 0, 0 => 1
  | 0, 1 => 4
  | 0, 2 => 2
  | 1, 0 => 3
  | 1, 1 => 1
  | 1, 2 => 1
  | 2, 0 => 4
  | 2, 1 => 3
  | 2, 2 => 4

/-- The 15-element magma of Theorem F over `F_5`: on `Z/3 × F_5`, `(x,s) ◇ (y,t) = (y+1, a x y · s + b x y · t)`
    (arithmetic in `Fin 3` and `Fin p` is modular). -/
def op5 (u v : Fin 3 × Fin 5) : Fin 3 × Fin 5 := (v.1 + 1, a5 u.1 v.1 * u.2 + b5 u.1 v.1 * v.2)

/-- The squaring map `S x = x ◇ x` of `op5`. -/
def sq5 (u : Fin 3 × Fin 5) : Fin 3 × Fin 5 := op5 u u

/-- Coefficient matrix `a` of Theorem F reduced modulo 13 with `i = 5` (`i² = −1`): over `Q(i)`,
    `a = [[-(1+i)/2, -1/2, (1-i)/2], [(1-i)/2, -(1+i)/2, 1+i], [1+i, (1-i)/2, 2i]]`. -/
def a13 : Fin 3 → Fin 3 → Fin 13
  | 0, 0 => 10
  | 0, 1 => 6
  | 0, 2 => 11
  | 1, 0 => 11
  | 1, 1 => 10
  | 1, 2 => 6
  | 2, 0 => 6
  | 2, 1 => 11
  | 2, 2 => 10

/-- Coefficient matrix `b` of Theorem F reduced modulo 13 with `i = 5`: over `Q(i)`,
    `b = [[1, (1+i)/2, -(1+i)], [1/2, 1, -2i], [(1+i)/2, 1/2, -2(1+i)]]`. -/
def b13 : Fin 3 → Fin 3 → Fin 13
  | 0, 0 => 1
  | 0, 1 => 3
  | 0, 2 => 7
  | 1, 0 => 7
  | 1, 1 => 1
  | 1, 2 => 3
  | 2, 0 => 3
  | 2, 1 => 7
  | 2, 2 => 1

/-- The 39-element magma of Theorem F over `F_13`: on `Z/3 × F_13`, `(x,s) ◇ (y,t) = (y+1, a x y · s + b x y · t)`
    (arithmetic in `Fin 3` and `Fin p` is modular). -/
def op13 (u v : Fin 3 × Fin 13) : Fin 3 × Fin 13 := (v.1 + 1, a13 u.1 v.1 * u.2 + b13 u.1 v.1 * v.2)

/-- The squaring map `S x = x ◇ x` of `op13`. -/
def sq13 (u : Fin 3 × Fin 13) : Fin 3 × Fin 13 := op13 u u

/-- Theorem A (table). In a magma satisfying 1518 and 3862, for every `x` and all `u, v ∈ {x, S x, S (S x)}`, `u ◇ v = S v = v ◇ v`. -/
theorem table {G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x u v : G) (hu : inT op x u) (hv : inT op x v) :
    op u v = op v v := by
  sorry

/-- Theorem A, cyclicity: `S (S (S x)) = x`, i.e. `(S x ◇ S x) ◇ (S x ◇ S x) = x`. -/
theorem cube {G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x : G) :
    op (op (op x x) (op x x)) (op (op x x) (op x x)) = x := by
  sorry

/-- Corollary A′: every word in `x` evaluates into `{x, S x, S (S x)}`, so the submagma generated by `x` is that set. -/
theorem words_in_T {G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x : G) (w : W) :
    inT op x (ev op x w) := by
  sorry

/-- Corollary A′: either `S x = x = S (S x)` (one element) or `x, S x, S (S x)` are pairwise distinct (three elements). -/
theorem one_or_three {G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x : G) :
    (op x x = x ∧ op (op x x) (op x x) = x) ∨
    (op x x ≠ x ∧ op (op x x) (op x x) ≠ x ∧ op (op x x) (op x x) ≠ op x x) := by
  sorry

/-- Theorem F over `F_5`: the 15-element magma `op5` satisfies law 1518. -/
theorem familyF5_law1518 : Law1518 op5 := by
  sorry

/-- Theorem F over `F_5`: `op5` violates each of the laws 47, 614, 817 and 3862. -/
theorem familyF5_refutes : ¬ Law47 op5 ∧ ¬ Law614 op5 ∧ ¬ Law817 op5 ∧ ¬ Law3862 op5 := by
  sorry

/-- Theorem F over `F_5`: the squaring map of `op5` has order exactly 12 (`S^12 = id`, `S^3 ≠ id`). -/
theorem familyF5_squaring_order : (∀ u, sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 u))))))))))) = u) ∧ ¬ (∀ u, sq5 (sq5 (sq5 u)) = u) := by
  sorry

/-- Theorem F over `F_13`: the 39-element magma `op13` satisfies law 1518. -/
theorem familyF13_law1518 : Law1518 op13 := by
  sorry

/-- Theorem F over `F_13`: `op13` violates each of the laws 47, 614, 817 and 3862. -/
theorem familyF13_refutes : ¬ Law47 op13 ∧ ¬ Law614 op13 ∧ ¬ Law817 op13 ∧ ¬ Law3862 op13 := by
  sorry

/-- Theorem F over `F_13`: the squaring map of `op13` has order exactly 12 (`S^12 = id`, `S^3 ≠ id`). -/
theorem familyF13_squaring_order : (∀ u, sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 u))))))))))) = u) ∧ ¬ (∀ u, sq13 (sq13 (sq13 u)) = u) := by
  sorry

end Magma1518
