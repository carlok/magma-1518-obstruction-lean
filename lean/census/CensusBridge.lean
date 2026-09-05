import Lean
set_option maxRecDepth 200000
set_option maxHeartbeats 0
/-!
Transparent formulation for small sizes, proved by kernel `decide` (no native evaluation, no bv_decide):
a magma on `Fin n` is a function `Fin n → Fin n → Fin n`; `law1518` is x = (y◇y)◇(x◇(y◇x)) for all x y;
`oneGenerated` says some g reaches every element within n-1 closure rounds. Tables are enumerated as `Fin (n^(n*n))`.
Bridges the bitvector encoding of Census1518_n.lean back to functions where the kernel can afford it.
-/
namespace CensusBridge

def law1518 {n : Nat} (op : Fin n → Fin n → Fin n) : Prop := ∀ x y, op (op y y) (op x (op y x)) = x

def step {n : Nat} (op : Fin n → Fin n → Fin n) (s : Fin n → Bool) : Fin n → Bool :=
  fun k => s k || (List.finRange n).any fun a => (List.finRange n).any fun b => s a && s b && decide (op a b = k)

def reach {n : Nat} (op : Fin n → Fin n → Fin n) (g : Fin n) : Nat → Fin n → Bool
  | 0 => fun k => decide (k = g)
  | m+1 => step op (reach op g m)

def oneGenerated {n : Nat} (op : Fin n → Fin n → Fin n) : Prop := ∃ g, ∀ k, reach op g (n-1) k = true

instance {n : Nat} (op : Fin n → Fin n → Fin n) : Decidable (law1518 op) := by unfold law1518; infer_instance
instance {n : Nat} (op : Fin n → Fin n → Fin n) : Decidable (oneGenerated op) := by unfold oneGenerated; infer_instance

/-- decode table number i (base n digits, cell (a,b) is digit a*n+b) -/
def table (n : Nat) (hn : 0 < n) (i : Nat) : Fin n → Fin n → Fin n :=
  fun a b => ⟨(i / n ^ (a.val * n + b.val)) % n, Nat.mod_lt _ hn⟩

theorem size2 : ∀ i : Fin (2 ^ 4), law1518 (table 2 (by decide) i.val) → ¬ oneGenerated (table 2 (by decide) i.val) := by
  decide

-- size 3 by kernel `decide` over 3^9 tables was stopped after 2h45m at 4 GB; the bv_decide theorem in Census1518_3.lean covers it.

end CensusBridge
#print axioms CensusBridge.size2
