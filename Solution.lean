import OneGenerated1518

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

theorem familyF5_law1518 : Law1518 op5 := by
  have h : ∀ x1 : Fin 3, ∀ x2 : Fin 5, ∀ y1 : Fin 3, ∀ y2 : Fin 5,
      (x1, x2) = op5 (op5 (y1, y2) (y1, y2)) (op5 (x1, x2) (op5 (y1, y2) (x1, x2))) := by decide
  intro ⟨x1, x2⟩ ⟨y1, y2⟩
  exact h x1 x2 y1 y2

theorem familyF5_refutes : ¬ Law47 op5 ∧ ¬ Law614 op5 ∧ ¬ Law817 op5 ∧ ¬ Law3862 op5 := by
  exact ⟨fun h => absurd (h (0, 1)) (by decide), fun h => absurd (h (0, 1)) (by decide), fun h => absurd (h (0, 1)) (by decide), fun h => absurd (h (0, 1)) (by decide)⟩

theorem familyF5_squaring_order : (∀ u, sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 u))))))))))) = u) ∧ ¬ (∀ u, sq5 (sq5 (sq5 u)) = u) := by
  refine ⟨?_, fun h => absurd (h (0, 1)) (by decide)⟩
  have h : ∀ x1 : Fin 3, ∀ x2 : Fin 5, sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (sq5 (x1, x2)))))))))))) = (x1, x2) := by decide
  intro ⟨x1, x2⟩
  exact h x1 x2

theorem familyF13_law1518 : Law1518 op13 := by
  have h : ∀ x1 : Fin 3, ∀ x2 : Fin 13, ∀ y1 : Fin 3, ∀ y2 : Fin 13,
      (x1, x2) = op13 (op13 (y1, y2) (y1, y2)) (op13 (x1, x2) (op13 (y1, y2) (x1, x2))) := by decide
  intro ⟨x1, x2⟩ ⟨y1, y2⟩
  exact h x1 x2 y1 y2

theorem familyF13_refutes : ¬ Law47 op13 ∧ ¬ Law614 op13 ∧ ¬ Law817 op13 ∧ ¬ Law3862 op13 := by
  exact ⟨fun h => absurd (h (0, 1)) (by decide), fun h => absurd (h (0, 1)) (by decide), fun h => absurd (h (0, 1)) (by decide), fun h => absurd (h (0, 1)) (by decide)⟩

theorem familyF13_squaring_order : (∀ u, sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 u))))))))))) = u) ∧ ¬ (∀ u, sq13 (sq13 (sq13 u)) = u) := by
  refine ⟨?_, fun h => absurd (h (0, 1)) (by decide)⟩
  have h : ∀ x1 : Fin 3, ∀ x2 : Fin 13, sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (sq13 (x1, x2)))))))))))) = (x1, x2) := by decide
  intro ⟨x1, x2⟩
  exact h x1 x2

end Magma1518
