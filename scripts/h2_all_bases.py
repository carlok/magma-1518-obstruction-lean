"""Conjecture R (rigidity): does H^2_1518(G, M) vanish for EVERY finite 1518-magma G and every finite 1518-fibre M?
For each base G, over the finite-fibre ring R = Z[b]/(b^5+b^3-b^2-1): D = cocycle matrix (rows: assignments (x,y); cols: f(x,y)),
E = coboundary matrix. Test 1 (necessary): rank_Q(ker D) == rank_Q(im E). Test 2: for primes p with a root r of m, dim Z^2 == dim B^2
over F_p with beta = r, alpha = r^4 - r. Test 3 (sufficient, module-independent): a certificate E P + Q D = I over R via integer lattice
membership. Bases: all 1518-magmas up to isomorphism of the given sizes (Mace4 files), plus named tables. Standard library only."""
import sys, itertools, re, json, time
from fractions import Fraction
S = sys.argv[1]; sizes = [int(x) for x in sys.argv[2].split(",")]; do_cert = len(sys.argv) > 3 and sys.argv[3] == "cert"
exec(open(__file__.replace("h2_all_bases.py", "l2_symbolic.py")).read().split("# ---- the base and the extension")[0])   # ring R, law(), coef, linear_satisfies
exec(open(__file__.replace("h2_all_bases.py", "adversary_size5.py")).read().split("PAIRS = {")[0].replace("S = sys.argv[1]", "pass"))  # mace4_models, canonical, Fibre, Setting, nullspace, holds_table
def rows_R(base, n):
    nb = len(base); vs, L, Rr = law(n); out = []
    def word(t, env):
        if isinstance(t, str): return env[t], [ZERO]*(nb*nb)
        x, vs_ = word(t[0], env); y, vt = word(t[1], env)
        vec = [radd(rmul(A, p), rmul(B, q)) for p, q in zip(vs_, vt)]; vec[nb*x+y] = radd(vec[nb*x+y], ONE)
        return base[x][y], vec
    for vals in itertools.product(range(nb), repeat=len(vs)):
        env = dict(zip(vs, vals)); x, vl = word(L, env); y, vr = word(Rr, env)
        if x != y: return None
        out.append([rsub(p, q) for p, q in zip(vl, vr)])
    return out
def cob_R(base):
    nb = len(base); cols = []
    for k in range(nb):
        col = []
        for x in range(nb):
            for y in range(nb):
                v = ZERO[:]
                if base[x][y] == k: v = radd(v, ONE)
                if x == k: v = rsub(v, A)
                if y == k: v = rsub(v, B)
                col.append(v)
        cols.append(col)
    return cols   # nb columns, each in R^{nb^2}
def zmat_of_R_linear(rows_, nv):
    """Z-matrix (5*len(rows) x 5*nv) of the Z-linear map R^nv -> R^rows given by rows over R."""
    M = []
    for row in rows_:
        for i in range(5):
            # the map applied to unit vectors b^i e_j
            pass
    cols = []
    for j in range(nv):
        for i in range(5):
            f = [ZERO[:] for _ in range(nv)]; f[j] = rpow(B, i)
            img = []
            for row in rows_:
                acc = ZERO[:]
                for e, v in zip(row, f): acc = radd(acc, rmul(e, v))
                img.extend(acc)
            cols.append(img)
    return [[cols[c][r] for c in range(len(cols))] for r in range(len(cols[0]))]
def rank_Q(M):
    A_ = [[Fraction(x) for x in r] for r in M]; rk = 0
    if not A_: return 0
    for c in range(len(A_[0])):
        piv = next((i for i in range(rk, len(A_)) if A_[i][c] != 0), None)
        if piv is None: continue
        A_[rk], A_[piv] = A_[piv], A_[rk]; pv = A_[rk][c]; A_[rk] = [x/pv for x in A_[rk]]
        for i in range(len(A_)):
            if i != rk and A_[i][c] != 0:
                fct = A_[i][c]; A_[i] = [x - fct*y for x, y in zip(A_[i], A_[rk])]
        rk += 1
    return rk
def rank_p(M, p):
    A_ = [[x % p for x in r] for r in M]; rk = 0
    if not A_: return 0
    for c in range(len(A_[0])):
        piv = next((i for i in range(rk, len(A_)) if A_[i][c]), None)
        if piv is None: continue
        A_[rk], A_[piv] = A_[piv], A_[rk]; inv = pow(A_[rk][c], -1, p); A_[rk] = [x*inv % p for x in A_[rk]]
        for i in range(len(A_)):
            if i != rk and A_[i][c]:
                fct = A_[i][c]; A_[i] = [(x - fct*y) % p for x, y in zip(A_[i], A_[rk])]
        rk += 1
    return rk
ROOTS = [(p, r) for p in (2, 3, 5, 7, 13) for r in range(p) if (r**5 + r**3 - r**2 - 1) % p == 0]
def h2_report(base):
    nb = len(base); nv = nb*nb
    D = rows_R(base, 1518); assert D is not None
    E = cob_R(base)
    # Q-ranks: dim ker D = 5 nv - rank D ; dim im E = rank of E's Z-matrix
    MD = zmat_of_R_linear(D, nv); ME = zmat_of_R_linear([[E[k][i] for k in range(nb)] for i in range(nv)], nb)
    kerD = 5*nv - rank_Q(MD); imE = rank_Q(ME)
    per_p = []
    for p, r in ROOTS:
        f = Fibre(p, 1, [(r**4 - r) % p], [r]); st = Setting(base, f)
        Z = len(nullspace(st.rows(1518), nv, p))
        Ep = [[((1 if base[x][y] == k else 0) - (f.A[0] if x == k else 0) - (f.B[0] if y == k else 0)) % p for k in range(nb)] for x in range(nb) for y in range(nb)]
        Bd = rank_p([[Ep[i][k] for i in range(nv)] for k in range(nb)], p)
        per_p.append(Z - Bd)
    return kerD, imE, per_p
t0 = time.time()
named = {"Z/3 shift": [[1, 2, 0], [1, 2, 0], [1, 2, 0]]}
try:
    named["Refutation939 (15)"] = eval(re.search(r"\[\[.*?\]\]", open(f"{S}/etp/Refutation939.lean").read(), re.S).group(0))
except Exception as e: print("no 939:", e)
results = []
for name, T in named.items():
    kerD, imE, per_p = h2_report(T)
    results.append((name, len(T), kerD, imE, per_p))
    print(f"{name}: rank_Q ker D = {kerD}, rank_Q im E = {imE}, dim H^2 at (p,r) roots {ROOTS}: {per_p}   [{time.time()-t0:.0f}s]", flush=True)
for n in sizes:
    path = f"{S}/m4/e1518_{n}_nolnh.out" if n <= 4 else f"{S}/m4/e1518_{n}.out"
    classes = {}
    for T in mace4_models(path, n): classes.setdefault(canonical(T), T)
    bad = 0; tot = 0; nonzero = []
    for T in classes.values():
        tot += 1; kerD, imE, per_p = h2_report([list(r) for r in T])
        if kerD != imE or any(per_p):
            bad += 1; nonzero.append((T, kerD, imE, per_p))
    print(f"size {n}: {tot} classes; H^2 nonzero (Q-rank or some F_p): {bad}   [{time.time()-t0:.0f}s]", flush=True)
    for T, kerD, imE, per_p in nonzero[:8]: print("   ", T, "kerD", kerD, "imE", imE, "H2 at roots", per_p)
