"""Is ETP Refutation939 (15 elements, refutes 1518 => 47, 614, 817, 3862) an extension of the Z/3 shift by Z/5 with
base-dependent affine coefficients  (x,s)◇(y,t) = (x◇y, alpha_{xy} s + beta_{xy} t + c_{xy}) ?  Search all labellings."""
import sys, itertools
S = sys.argv[1]
exec(open(__file__.replace("witness939_varying.py", "witness_structure.py")).read().split("# abelian groups of order m")[0])
T = table(939); N = 15; congs = congruences(T); assert len(congs) == 1
c = congs[0]; classes = {}
for i, rt in enumerate(c): classes.setdefault(rt, []).append(i)
blocks = list(classes.values()); cls = {e: bi for bi, b in enumerate(blocks) for e in b}
Q = [[cls[T[blocks[a][0]][blocks[b][0]]] for b in range(3)] for a in range(3)]
def canon(Tq):
    n = len(Tq); best = None
    for perm in itertools.permutations(range(n)):
        inv = {perm[i]: i for i in range(n)}
        U = tuple(tuple(perm[Tq[inv[i]][inv[j]]] for j in range(n)) for i in range(n))
        if best is None or U < best: best = U
    return best
print("Refutation939: unique nontrivial congruence, class sizes", sorted(len(b) for b in blocks), "; quotient", Q,
      "; isomorphic to the Z/3 shift:", canon(Q) == canon([[1, 2, 0], [1, 2, 0], [1, 2, 0]]))
p = 5
pairs_into = {z: [(x, y) for x in range(3) for y in range(3) if Q[x][y] == z] for z in range(3)}
def ok_label(z, L):
    for (x, y) in pairs_into[z]:
        Cx, Cy = blocks[x], blocks[y]
        if any(len({(L[T[s][t]] - L[T[s2][t]]) % p for t in Cy}) != 1 for s in Cx for s2 in Cx): return False
        if any(len({(L[T[s][t]] - L[T[s][t2]]) % p for s in Cx}) != 1 for t in Cy for t2 in Cy): return False
    return True
cands = {z: [dict(zip(blocks[z], perm)) for perm in itertools.permutations(range(p)) if ok_label(z, dict(zip(blocks[z], perm)))] for z in range(3)}
print("labellings of each class passing the additivity test:", [len(cands[z]) for z in range(3)])
found = []
for L0 in cands[0]:
    for L1 in cands[1]:
        for L2 in cands[2]:
            L = {**L0, **L1, **L2}; good = True; params = {}
            for x in range(3):
                for y in range(3):
                    Cx, Cy = blocks[x], blocks[y]; s0, t0 = Cx[0], Cy[0]
                    inv_x = {L[s]: s for s in Cx}; inv_y = {L[t]: t for t in Cy}; c0 = L[T[s0][t0]]
                    alpha = (L[T[inv_x[(L[s0]+1) % p]][t0]] - c0) % p; beta = (L[T[s0][inv_y[(L[t0]+1) % p]]] - c0) % p
                    cst = (c0 - alpha*L[s0] - beta*L[t0]) % p
                    if any(L[T[s][t]] != (alpha*L[s] + beta*L[t] + cst) % p for s in Cx for t in Cy): good = False; break
                    params[(x, y)] = (alpha, beta, cst)
                if not good: break
            if good: found.append(params)
print(f"labellings making it a base-dependent affine extension of the shift by Z/5: {len(found)} (= 20^3: unique up to affine relabelling of each fibre)")
params = found[0]
print("one choice, (alpha_xy, beta_xy, c_xy) for x = 0,1,2 (rows) and y = 0,1,2 (columns):")
for x in range(3): print("  ", [params[(x, y)] for y in range(3)])
print("distinct alpha:", sorted({v[0] for v in params.values()}), "distinct beta:", sorted({v[1] for v in params.values()}), "-> coefficients vary with the base pair")
