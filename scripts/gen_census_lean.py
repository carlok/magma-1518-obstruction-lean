"""Generate Lean 4 files proving, per size n, that no one-generated 1518-magma of size n exists (n = 2, 4..7), and that the
one-generated 1518-magmas of size 3 are exactly the labelled copies of the Z/3 shift. Encoding for bv_decide:
  * table cells t_a_b : BitVec 3 with range hypotheses t_a_b < n;
  * the law x = (y◇y)◇(x◇(y◇x)) at every concrete pair (x,y): the inner lookups with concrete indices are cells, the two
    lookups with variable indices are muxes over rows (7-way) and over all cells (49-way);
  * a generator g : BitVec 3 (any element, no symmetry breaking) and Bool variables r_i_k meaning 'element k is reachable
    from g in i rounds', with r_0_k = (g == k) and r_{i+1}_k = r_i_k || OR_{a,b}(r_i_a && r_i_b && t_a_b == k);
  * hypothesis: all r_{n-1}_k are true (a one-generated magma of size n is generated in at most n-1 rounds);
  * conclusion False.
Usage: python3 gen_census_lean.py <outdir> <n> [timeout_seconds]"""
import sys, itertools
out, n = sys.argv[1], int(sys.argv[2]); timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 10
W = 3
def cell(a, b): return f"t_{a}_{b}"
def lit(v): return f"{v}#{W}"
def row(a, sel):
    """mux over row a selected by BitVec expression sel"""
    e = cell(a, n-1)
    for b in range(n-2, -1, -1): e = f"(bif {sel} == {lit(b)} then {cell(a,b)} else {e})"
    return e
def op(sel_a, sel_b):
    e = row(n-1, sel_b)
    for a in range(n-2, -1, -1): e = f"(bif {sel_a} == {lit(a)} then {row(a, sel_b)} else {e})"
    return e
binders = [f"({' '.join(cell(a,b) for a in range(n) for b in range(n))} g : BitVec {W})",
           f"({' '.join(f'r_{i}_{k}' for i in range(n) for k in range(n))} : Bool)"]
hyps = []
if n < 2**W:   # for n = 2^W every W-bit value is a valid element, and n#W would wrap to 0 and make the hypotheses false
    for a in range(n):
        for b in range(n): hyps.append(f"(range_{a}_{b} : {cell(a,b)} < {lit(n)})")
    hyps.append(f"(range_g : g < {lit(n)})")
for x in range(n):
    for y in range(n):
        w = row(x, cell(y, x))                 # x ◇ (y ◇ x), first index concrete
        z = op(cell(y, y), w)                  # (y ◇ y) ◇ (…), both indices variable
        hyps.append(f"(law_{x}_{y} : {z} = {lit(x)})")
for k in range(n): hyps.append(f"(reach_0_{k} : r_0_{k} = (g == {lit(k)}))")
for i in range(n-1):
    for k in range(n):
        leaves = [f"(r_{i}_{a} && r_{i}_{b} && ({cell(a,b)} == {lit(k)}))" for a in range(n) for b in range(n)]
        while len(leaves) > 1:   # balanced OR tree keeps the term shallow
            leaves = [f"({leaves[j]} || {leaves[j+1]})" if j+1 < len(leaves) else leaves[j] for j in range(0, len(leaves), 2)]
        hyps.append(f"(reach_{i+1}_{k} : r_{i+1}_{k} = (r_{i}_{k} || {leaves[0]}))")
if n == 3:
    # every one-generated 1518-magma of size 3 is one of the labelled copies of the shift: enumerate them here
    def holds(T):
        return all(T[T[y][y]][T[x][T[y][x]]] == x for x in range(3) for y in range(3))
    def onegen(T):
        for g in range(3):
            s = {g}
            for _ in range(3): s |= {T[a][b] for a in s for b in s}
            if len(s) == 3: return True
        return False
    tabs = [T for T in ([[d[3*i+j] for j in range(3)] for i in range(3)] for d in itertools.product(range(3), repeat=9)) if holds(T) and onegen(T)]
    concl = " ∨ ".join("(" + " ∧ ".join(f"{cell(a,b)} = {lit(T[a][b])}" for a in range(3) for b in range(3)) + ")" for T in tabs)
    hyps.append(f"(full : ({' && '.join(f'r_{n-1}_{k}' for k in range(n))}) = true)")
    stmt = f"theorem one_generated_3_is_the_shift {' '.join(binders)}\n    {chr(10).join('    ' + h for h in hyps)} :\n    {concl} := by\n  bv_decide (config := {{ timeout := {timeout} }})"
    name = "one_generated_3_is_the_shift"; extra = f"-- {len(tabs)} labelled one-generated 1518-magmas of size 3, all relabellings of x◇y = y+1: {tabs}\n"
else:
    hyps.append(f"(full : ({' && '.join(f'r_{n-1}_{k}' for k in range(n))}) = true)")
    stmt = f"theorem no_one_generated_{n} {' '.join(binders)}\n{chr(10).join('    ' + h for h in hyps)} :\n    False := by\n  bv_decide (config := {{ timeout := {timeout} }})"
    name = f"no_one_generated_{n}"; extra = ""
# ---- encoding controls, proved by kernel `decide` on literals: a genuine 1518 table satisfies every encoded law (and range)
# hypothesis, and at size 3 the shift with generator 0 satisfies the reachability chain with full = true.
import json
import os; ctrl = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "control_tables.json")))[str(n)]
def inst(text, T, g=None, r=None):
    for a in range(n):
        for b in range(n): text = text.replace(cell(a, b), lit(T[a][b]))
    if g is not None: text = text.replace("(g ==", f"({lit(g)} ==").replace(" g <", f" {lit(g)} <")
    if r is not None:
        for i in range(n):
            for k in range(n): text = text.replace(f"r_{i}_{k}", "true" if r[i][k] else "false")
    return text
law_props = [h[h.index(":")+2:-1] for h in hyps if h.startswith("(law_") or (h.startswith("(range_") and not h.startswith("(range_g"))]
chunks = [law_props[i:i+9] for i in range(0, len(law_props), 9)]   # per-chunk theorems keep instance synthesis small
controls = "".join(f"theorem law_control_{n}_{ci} : {' ∧ '.join(inst(pr, ctrl) for pr in chunk)} := by\n  decide\n" for ci, chunk in enumerate(chunks))
if n == 3:
    shift = [[1, 2, 0], [1, 2, 0], [1, 2, 0]]; g0 = 0
    r = [[False]*3 for _ in range(3)]; r[0][g0] = True
    for i in range(2):
        for k in range(3): r[i+1][k] = r[i][k] or any(r[i][a] and r[i][b] and shift[a][b] == k for a in range(3) for b in range(3))
    reach_props = [h[h.index(":")+2:-1] for h in hyps if h.startswith("(reach_") or h.startswith("(full")]
    controls += f"theorem reach_control_3 : {' ∧ '.join(inst(pr, shift, g0, r) for pr in reach_props)} := by\n  decide\n"
    controls += f"theorem law_control_3_shift : {' ∧ '.join(inst(pr, shift) for pr in law_props)} := by\n  decide\n"
src = f"""import Std.Tactic.BVDecide
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
Census of one-generated 1518-magmas, size {n}. Generated by scripts/gen_census_lean.py.
Cells t_a_b : BitVec 3 encode the table (range hypotheses t_a_b < {n}); law_x_y is
  x = (y ◇ y) ◇ (x ◇ (y ◇ x))  at the concrete pair (x, y), with the variable-index lookups written as muxes;
r_i_k : Bool means "k is reachable from the generator g in i rounds"; full says everything is reached in {n-1} rounds.
Trust: bv_decide bit-blasts, calls the bundled CaDiCaL, and checks the LRAT proof with Lean's verified checker run
natively; the check is recorded as an auxiliary axiom `…_native.bv_decide.ax_…` (the native_decide trust model).
-/
namespace Census1518
{extra}
{stmt}

{controls}
end Census1518
#print axioms Census1518.{name}
{chr(10).join(f"#print axioms Census1518.law_control_{n}_{ci}" for ci in range(len(chunks)))}
{"#print axioms Census1518.reach_control_3" if n == 3 else ""}
"""
open(f"{out}/Census1518_{n}.lean", "w").write(src)
print(f"wrote {out}/Census1518_{n}.lean: {len(hyps)} hypotheses, {len(src)} bytes")
