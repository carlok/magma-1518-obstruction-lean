"""Generate the Palomar Challenge/Solution pair and comparator.json for this repository.
Challenge.lean: statements only (core Lean, no imports): Theorem A (table, S^3 = id, words, one-or-three) for arbitrary magmas
satisfying 1518 and 3862, and the F_5 and F_13 members of Theorem F defined by their coefficient matrices on Z/3 x F_p.
Solution.lean: the same definitions verbatim, proofs via lean/OneGenerated1518.lean and kernel `decide`.
Usage: python3 scripts/gen_palomar.py data   (reads data/etp/equations.txt and data/fifteen/family_Qi.json)"""
import sys, json, re, itertools
from fractions import Fraction as Fr
S = sys.argv[1]
eq = open(f"{S}/etp/equations.txt").read().splitlines()
fam = json.load(open(f"{S}/fifteen/family_Qi.json"))["F+"]
def parse(st):
    toks = re.findall(r"[a-z]|◇|\(|\)", st); pos = [0]
    def atom():
        t = toks[pos[0]]; pos[0] += 1
        if t == "(":
            e = expr(); pos[0] += 1; return e
        return t
    def expr():
        left = atom()
        while pos[0] < len(toks) and toks[pos[0]] == "◇": pos[0] += 1; left = (left, atom())
        return left
    return expr()
def lean(t, op="op"): return t if isinstance(t, str) else f"({op} {lean(t[0], op)} {lean(t[1], op)})"
def law_def(k):
    l, r = eq[k-1].split(" = "); vs = sorted(set(re.findall(r"[a-z]", eq[k-1])))
    body = f"∀ {' '.join(vs)}, {lean(parse(l))} = {lean(parse(r))}"
    return f"/-- ETP law {k}: `{eq[k-1]}`. -/\ndef Law{k} {{G : Type}} (op : G → G → G) : Prop := {body}"
def qi(s):
    s = s.replace(" ", "")
    if s.endswith("i"):
        core = s[:-1]; k = max(core.rfind("+", 1), core.rfind("-", 1))
        re_, im_ = (core[:k], core[k:]) if k > 0 else ("0", core)
        im_ = {"": "1", "+": "1", "-": "-1"}.get(im_, im_)
    else: re_, im_ = s, "0"
    return Fr(re_), Fr(im_)
QA = [[qi(v) for v in row] for row in fam["a"]]; QB = [[qi(v) for v in row] for row in fam["b"]]
def modp(c, p, ip): return (c[0].numerator*pow(c[0].denominator, -1, p) + c[1].numerator*pow(c[1].denominator, -1, p)*ip) % p
def ev(T, t, env): return env[t] if isinstance(t, str) else T[ev(T, t[0], env)][ev(T, t[1], env)]
def matrix_def(name, M, p, doc):
    cases = "\n".join(f"  | {x}, {y} => {M[x][y]}" for x in range(3) for y in range(3))
    return f"/-- {doc} -/\ndef {name} : Fin 3 → Fin 3 → Fin {p}\n{cases}"
shared = ["namespace Magma1518", "", law_def(1518), "", law_def(3862), "", law_def(47), "", law_def(614), "", law_def(817), "",
          "/-- `T x = {x, S x, S (S x)}` with `S y = y ◇ y`: `inT op x y` says that `y` is one of the three. -/",
          "def inT {G : Type} (op : G → G → G) (x y : G) : Prop := y = x ∨ y = op x x ∨ y = op (op x x) (op x x)", "",
          "/-- Words in one generator: the free magma on one generator `v`. -/",
          "inductive W where\n  | v : W\n  | m : W → W → W", "",
          "/-- Evaluation of a word at `x`. -/",
          "def ev {G : Type} (op : G → G → G) (x : G) : W → G\n  | .v => x\n  | .m a b => op (ev op x a) (ev op x b)", ""]
fin = {}
for p in (5, 13):
    ip = next(v for v in range(1, p) if v*v % p == p-1)
    A = [[modp(QA[x][y], p, ip) for y in range(3)] for x in range(3)]; B = [[modp(QB[x][y], p, ip) for y in range(3)] for x in range(3)]
    n = 3*p; T = [[0]*n for _ in range(n)]
    for x in range(3):
        for s in range(p):
            for y in range(3):
                for t in range(p): T[p*x+s][p*y+t] = p*((y+1) % 3) + (A[x][y]*s + B[x][y]*t) % p
    assert all(z == T[T[w][w]][T[z][T[w][z]]] for z in range(n) for w in range(n))
    wit = {}
    for k in (47, 614, 817, 3862):
        l, r = eq[k-1].split(" = "); L, R = parse(l), parse(r)
        z = next(z for z in range(n) if ev(T, L, {"x": z}) != ev(T, R, {"x": z})); wit[k] = (z // p, z % p)
    sq = [T[z][z] for z in range(n)]
    def it(f, z, k):
        for _ in range(k): z = f[z]
        return z
    assert all(it(sq, z, 12) == z for z in range(n)); z3 = next(z for z in range(n) if it(sq, z, 3) != z); wit["sq3"] = (z3 // p, z3 % p)
    fin[p] = (ip, A, B, wit)
    shared += [f"/-- Coefficient matrix `a` of Theorem F reduced modulo {p} with `i = {ip}` (`i² = −1`): over `Q(i)`,",
               "    `a = [[-(1+i)/2, -1/2, (1-i)/2], [(1-i)/2, -(1+i)/2, 1+i], [1+i, (1-i)/2, 2i]]`. -/",
               f"def a{p} : Fin 3 → Fin 3 → Fin {p}", "\n".join(f"  | {x}, {y} => {A[x][y]}" for x in range(3) for y in range(3)), "",
               f"/-- Coefficient matrix `b` of Theorem F reduced modulo {p} with `i = {ip}`: over `Q(i)`,",
               "    `b = [[1, (1+i)/2, -(1+i)], [1/2, 1, -2i], [(1+i)/2, 1/2, -2(1+i)]]`. -/",
               f"def b{p} : Fin 3 → Fin 3 → Fin {p}", "\n".join(f"  | {x}, {y} => {B[x][y]}" for x in range(3) for y in range(3)), "",
               f"/-- The {n}-element magma of Theorem F over `F_{p}`: on `Z/3 × F_{p}`, `(x,s) ◇ (y,t) = (y+1, a x y · s + b x y · t)`",
               "    (arithmetic in `Fin 3` and `Fin p` is modular). -/",
               f"def op{p} (u v : Fin 3 × Fin {p}) : Fin 3 × Fin {p} := (v.1 + 1, a{p} u.1 v.1 * u.2 + b{p} u.1 v.1 * v.2)", "",
               f"/-- The squaring map `S x = x ◇ x` of `op{p}`. -/", f"def sq{p} (u : Fin 3 × Fin {p}) : Fin 3 × Fin {p} := op{p} u u", ""]
def nest(f, k, arg): return arg if k == 0 else f"{f} ({nest(f, k-1, arg)})" if k > 1 else f"{f} {arg}"
stmts = [
 ("table", "Theorem A (table). In a magma satisfying 1518 and 3862, for every `x` and all `u, v ∈ {x, S x, S (S x)}`, `u ◇ v = S v = v ◇ v`.",
  "{G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x u v : G) (hu : inT op x u) (hv : inT op x v) :\n    op u v = op v v"),
 ("cube", "Theorem A, cyclicity: `S (S (S x)) = x`, i.e. `(S x ◇ S x) ◇ (S x ◇ S x) = x`.",
  "{G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x : G) :\n    op (op (op x x) (op x x)) (op (op x x) (op x x)) = x"),
 ("words_in_T", "Corollary A′: every word in `x` evaluates into `{x, S x, S (S x)}`, so the submagma generated by `x` is that set.",
  "{G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x : G) (w : W) :\n    inT op x (ev op x w)"),
 ("one_or_three", "Corollary A′: either `S x = x = S (S x)` (one element) or `x, S x, S (S x)` are pairwise distinct (three elements).",
  "{G : Type} (op : G → G → G) (h1 : Law1518 op) (h2 : Law3862 op) (x : G) :\n    (op x x = x ∧ op (op x x) (op x x) = x) ∨\n    (op x x ≠ x ∧ op (op x x) (op x x) ≠ x ∧ op (op x x) (op x x) ≠ op x x)"),
]
for p in (5, 13):
    stmts += [
     (f"familyF{p}_law1518", f"Theorem F over `F_{p}`: the {3*p}-element magma `op{p}` satisfies law 1518.", f": Law1518 op{p}"),
     (f"familyF{p}_refutes", f"Theorem F over `F_{p}`: `op{p}` violates each of the laws 47, 614, 817 and 3862.", f": ¬ Law47 op{p} ∧ ¬ Law614 op{p} ∧ ¬ Law817 op{p} ∧ ¬ Law3862 op{p}"),
     (f"familyF{p}_squaring_order", f"Theorem F over `F_{p}`: the squaring map of `op{p}` has order exactly 12 (`S^12 = id`, `S^3 ≠ id`).",
      f": (∀ u, {nest(f'sq{p}', 12, 'u')} = u) ∧ ¬ (∀ u, {nest(f'sq{p}', 3, 'u')} = u)"),
    ]
header_c = '''/-!
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
'''
header_s = '''import OneGenerated1518

/-!
# Solution: proofs of the declarations of `Challenge.lean`

The definitions are repeated verbatim so that Comparator finds identical statements.  Theorem A is proved from
`lean/OneGenerated1518.lean` (core Lean, transcribed from Vampire's equational proofs); the finite members of Theorem F by
kernel `decide` on the coefficient-matrix definition of the tables.
-/

set_option maxRecDepth 100000
'''
chal = [header_c] + shared
for name, doc, ty in stmts: chal += [f"/-- {doc} -/", f"theorem {name} {ty} := by\n  sorry", ""]
chal.append("end Magma1518")
sol = [header_s] + shared
proofs = {
 "table": "  exact OneGenerated1518.table op h1 h2 x u v hu hv",
 "cube": "  exact OneGenerated1518.B_B op h1 h2 x",
 "words_in_T": "  induction w with\n  | v => exact Or.inl rfl\n  | m a b iha ihb => exact OneGenerated1518.closed op h1 h2 x _ _ iha ihb",
 "one_or_three": "  exact OneGenerated1518.one_or_three op h1 h2 x",
}
for p in (5, 13):
    ip, A, B, wit = fin[p]
    l, r = eq[1517].split(" = ")
    proofs[f"familyF{p}_law1518"] = (f"  have h : ∀ x1 : Fin 3, ∀ x2 : Fin {p}, ∀ y1 : Fin 3, ∀ y2 : Fin {p},\n      (x1, x2) = op{p} (op{p} (y1, y2) (y1, y2)) (op{p} (x1, x2) (op{p} (y1, y2) (x1, x2))) := by decide\n"
                                     f"  intro ⟨x1, x2⟩ ⟨y1, y2⟩\n  exact h x1 x2 y1 y2")
    parts = [f"fun h => absurd (h ({wit[k][0]}, {wit[k][1]})) (by decide)" for k in (47, 614, 817, 3862)]
    proofs[f"familyF{p}_refutes"] = "  exact ⟨" + ", ".join(parts) + "⟩"
    proofs[f"familyF{p}_squaring_order"] = (f"  refine ⟨?_, fun h => absurd (h ({wit['sq3'][0]}, {wit['sq3'][1]})) (by decide)⟩\n"
                                            f"  have h : ∀ x1 : Fin 3, ∀ x2 : Fin {p}, {nest(f'sq{p}', 12, '(x1, x2)')} = (x1, x2) := by decide\n"
                                            f"  intro ⟨x1, x2⟩\n  exact h x1 x2")
for name, doc, ty in stmts: sol += [f"theorem {name} {ty} := by\n{proofs[name]}", ""]
sol.append("end Magma1518")
open("Challenge.lean", "w").write("\n".join(chal) + "\n"); open("Solution.lean", "w").write("\n".join(sol) + "\n")
json.dump({"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": [f"Magma1518.{n}" for n, _, _ in stmts],
           "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": True},
          open("comparator.json", "w"), indent=2)
print("wrote Challenge.lean (%d lines), Solution.lean (%d lines), comparator.json (%d theorems); witnesses %s" %
      (len("\n".join(chal).splitlines()), len("\n".join(sol).splitlines()), len(stmts), {p: fin[p][3] for p in fin}))
