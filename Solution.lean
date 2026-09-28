module

public import OneGenerated1518

@[expose] public section

/-!
# Solution: proofs of the declarations of `Challenge.lean`

The definitions are repeated verbatim so that Comparator finds identical statements.  Theorem A is proved from
`lean/OneGenerated1518.lean` (core Lean, transcribed from Vampire's equational proofs); the finite members of Theorem F by
kernel `decide` on the coefficient-matrix definition of the tables.
-/

set_option maxRecDepth 100000

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

theorem table {G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x u v : G) (hu : inT op x u) (hv : inT op x v) :
    op u v = op v v := by
  exact OneGenerated1518.table op h1 h2 x u v hu hv

theorem cube {G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x : G) :
    op (op (op x x) (op x x)) (op (op x x) (op x x)) = x := by
  exact OneGenerated1518.B_B op h1 h2 x

theorem words_in_T {G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x : G) (w : W) :
    inT op x (ev op x w) := by
  induction w with
  | v => exact Or.inl rfl
  | m a b iha ihb => exact OneGenerated1518.closed op h1 h2 x _ _ iha ihb

theorem one_or_three {G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x : G) :
    (op x x = x ∧ op (op x x) (op x x) = x) ∨
    (op x x ≠ x ∧ op (op x x) (op x x) ≠ x ∧ op (op x x) (op x x) ≠ op x x) := by
  exact OneGenerated1518.one_or_three op h1 h2 x

end Magma1518
