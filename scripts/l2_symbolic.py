"""L2, symbolic: over the base G = Z/3 with x◇y = y+1, is every 1518-cocycle an E'-cocycle for E' in {47, 614, 817, 3862},
for every FINITE abelian fibre M with endomorphisms alpha, beta making alpha s + beta t a 1518-magma?

Reduction (proved in the audit): for finite M the 1518 identity forces beta (alpha + beta^2) = 1, so beta is invertible,
alpha = beta^-1 - beta^2, alpha and beta commute, and (beta^2 + 1)(beta^3 - 1) = 0. Hence M is a module over
    R = Z[b] / (b^5 + b^3 - b^2 - 1),   a = b^4 - b   (b^-1 = b^4 + b^2 - b),
a free Z-module of rank 5, and conversely every R-module is such a fibre. The E-cocycle condition is a matrix D_E over R
acting on M^9; ker D_1518 ⊆ ker D_E' for all R-modules M  <=>  the left R-span of the rows of D_E' lies in that of D_1518
(take M = R^9 / rowspan(D_1518) and its finite quotients). Over the commutative rank-5 ring this is a Z-lattice containment
in Z^45, decided exactly by integer row reduction. A certificate matrix C with D_E' = C · D_1518 over R is extracted and
re-verified by direct multiplication. Standard library only."""
import itertools, json, re, sys
S = sys.argv[1]
eq = open(f"{S}/etp/equations.txt").read().splitlines()
def parse(s):
    toks = re.findall(r"[a-z]|◇|\(|\)", s); pos = [0]
    def atom():
        t = toks[pos[0]]; pos[0] += 1
        if t == "(":
            e = expr(); pos[0] += 1; return e
        return t
    def expr():
        left = atom()
        while pos[0] < len(toks) and toks[pos[0]] == "◇":
            pos[0] += 1; left = (left, atom())
        return left
    return expr()
def law(n):
    l, r = eq[n-1].split(" = "); return sorted(set(re.findall(r"[a-z]", eq[n-1]))), parse(l), parse(r)

# ---- the ring R = Z[b]/(m), m = b^5 + b^3 - b^2 - 1 ; elements are int lists of length 5 (coefficients of 1, b, ..., b^4)
DEG = 5
def radd(u, v): return [x + y for x, y in zip(u, v)]
def rsub(u, v): return [x - y for x, y in zip(u, v)]
def rneg(u): return [-x for x in u]
def rmul(u, v):
    prod = [0]*(2*DEG - 1)
    for i, x in enumerate(u):
        if x:
            for j, y in enumerate(v): prod[i+j] += x*y
    for k in range(2*DEG - 2, DEG - 1, -1):   # b^5 = -b^3 + b^2 + 1  =>  b^k = b^(k-5) * (-b^3 + b^2 + 1)
        c = prod[k]
        if c: prod[k] = 0; prod[k-5] += c; prod[k-3] += c; prod[k-2] -= c
    return prod[:DEG]
ZERO, ONE = [0]*DEG, [1, 0, 0, 0, 0]
B = [0, 1, 0, 0, 0]
A = [0, -1, 0, 0, 1]                      # a = b^4 - b
BINV = [0, -1, 1, 0, 1]                    # b^-1 = b^4 + b^2 - b
assert rmul(B, BINV) == ONE and rsub(BINV, rmul(B, B)) == A, "ring constants"
def rpow(u, n):
    out = ONE
    for _ in range(n): out = rmul(out, u)
    return out

# ---- coefficient polynomials P_{w,i}(a,b) in R: does the linear magma over R satisfy a law?
def coef(t):
    if isinstance(t, str): return {t: ONE}
    L, Rr = coef(t[0]), coef(t[1]); out = {}
    for v, c in L.items(): out[v] = rmul(A, c)
    for v, c in Rr.items(): out[v] = radd(out.get(v, ZERO), rmul(B, c))
    return out
def linear_satisfies(n):
    vs, L, Rr = law(n); cl, cr = coef(L), coef(Rr)
    return all(cl.get(v, ZERO) == cr.get(v, ZERO) for v in vs)

# ---- the base and the extension's fibre component as an R-linear form in the 9 cocycle unknowns f(x,y), index 3x+y
BASES = {"Z/3 shift x◇y = y+1": [[1, 2, 0], [1, 2, 0], [1, 2, 0]], "one-element base": [[0]]}
BASE_NAME = sys.argv[2] if len(sys.argv) > 2 else "Z/3 shift x◇y = y+1"
base = BASES[BASE_NAME]; NB = len(base)
def word(t, env):
    if isinstance(t, str): return env[t], [ZERO]*(NB*NB)
    x, vs_ = word(t[0], env); y, vt = word(t[1], env)
    vec = [radd(rmul(A, p), rmul(B, q)) for p, q in zip(vs_, vt)]
    vec[NB*x + y] = radd(vec[NB*x + y], ONE)
    return base[x][y], vec
def rows(n):
    """Cocycle condition rows for law n over the base, as vectors in R^9; None if the base fails the law."""
    vs, L, Rr = law(n); out = []
    for vals in itertools.product(range(NB), repeat=len(vs)):
        env = dict(zip(vs, vals)); x, vl = word(L, env); y, vr = word(Rr, env)
        if x != y: return None
        out.append([rsub(p, q) for p, q in zip(vl, vr)])
    return out
def flatten(row): return [c for entry in row for c in entry]          # R^(NB^2) -> Z^(5 NB^2)
def zgens(rws):
    """Z-generators of the R-span of the rows: b^i * row, i = 0..4, with bookkeeping (row index, i)."""
    gens = []
    for ri, row in enumerate(rws):
        for i in range(DEG):
            bi = rpow(B, i); gens.append((flatten([rmul(bi, e) for e in row]), (ri, i)))
    return gens

# ---- integer row echelon with transformation tracking (each row carries its expression in the original generators)
def echelon(vectors):
    n = len(vectors); ncols = len(vectors[0])
    rows_ = [[list(v), [1 if j == k else 0 for j in range(n)]] for k, v in enumerate(vectors)]
    ech = []
    for col in range(ncols):
        active = [r for r in rows_ if r[0][col]]
        if not active: continue
        while len(active) > 1:
            active.sort(key=lambda r: abs(r[0][col]))
            piv = active[0]
            for r in active[1:]:
                q = r[0][col] // piv[0][col]
                r[0] = [x - q*y for x, y in zip(r[0], piv[0])]; r[1] = [x - q*y for x, y in zip(r[1], piv[1])]
            active = [r for r in active if r[0][col]]
        piv = active[0]
        if piv[0][col] < 0: piv[0] = [-x for x in piv[0]]; piv[1] = [-x for x in piv[1]]
        ech.append((col, piv)); rows_.remove(piv)
    return ech          # list of (pivot column, [vector, combination]); rows_ left over are zero rows
def member(ech, v):
    """Express v as an integer combination of the original generators, or return None."""
    v = list(v); combo = None
    for col, (vec, cmb) in ech:
        if v[col]:
            if v[col] % vec[col]: return None
            q = v[col] // vec[col]
            v = [x - q*y for x, y in zip(v, vec)]
            combo = [q*y for y in cmb] if combo is None else [x + q*y for x, y in zip(combo, cmb)]
    return None if any(v) else (combo or [0]*len(ech[0][1][1]))

HYP = 1518; TARGETS = [47, 614, 817, 3862]
CONTROLS_IMPLIED = [359, 3, 8]      # laws 1518 implies in general (359: (x◇x)◇x = x◇x; 3, 8 hold in finite 1518-magmas? checked below on R and base)
print(f"base: {BASE_NAME}")
print("ring check: linear magma over R satisfies 1518:", linear_satisfies(HYP))
for t in TARGETS: print(f"  linear magma over R satisfies E{t}: {linear_satisfies(t)}")
r_hyp = rows(HYP); assert r_hyp is not None, "base fails 1518"
gens = zgens(r_hyp); ech = echelon([g for g, _ in gens])
print(f"D_1518 over R: {len(r_hyp)} rows in R^{NB*NB}; Z-lattice of its R-span has rank {len(ech)} in Z^{5*NB*NB}")

certificate = {}
for t in TARGETS + CONTROLS_IMPLIED:
    if not linear_satisfies(t):
        print(f"E{t}: linear magma over R does not satisfy it: the direct product would refute; skipped"); continue
    r_t = rows(t)
    if r_t is None: print(f"E{t}: the base itself fails E{t}"); continue
    combos = []; ok = True
    for row in r_t:
        c = member(ech, flatten(row))
        if c is None: ok = False; break
        combos.append(c)
    if not ok:
        print(f"E{t}: NOT CONTAINED. Some E{t}-cocycle row is outside the R-span of the 1518 rows: a finite counterexample exists (see below)."); certificate[t] = None; continue
    # assemble C over R: C[i][j] = sum_k coeff * b^k over generators (j, k)
    C = []
    for c in combos:
        crow = [ZERO[:] for _ in r_hyp]
        for gidx, coeff in enumerate(c):
            if coeff:
                j, k = gens[gidx][1]; crow[j] = radd(crow[j], [coeff*x for x in rpow(B, k)])
        C.append(crow)
    # verify C * D_1518 == D_t in R^9
    for i, row in enumerate(r_t):
        acc = [ZERO[:] for _ in range(NB*NB)]
        for j, hrow in enumerate(r_hyp):
            if C[i][j] != ZERO:
                acc = [radd(p, rmul(C[i][j], q)) for p, q in zip(acc, hrow)]
        assert acc == row, f"certificate verification failed for E{t} row {i}"
    nz = sum(1 for crow in C for e in crow if e != ZERO)
    print(f"E{t}: CONTAINED. Certificate C ({len(C)} x {len(r_hyp)} over R, {nz} nonzero entries) verified: C * D_1518 = D_{t} in R^9." + ("   [control: 1518 implies it]" if t in CONTROLS_IMPLIED else ""))
    certificate[t] = C
json.dump({"ring": "Z[b]/(b^5 + b^3 - b^2 - 1), a = b^4 - b, elements as coefficient lists of 1,b,b^2,b^3,b^4",
           "base": BASE_NAME, "base_table": base, "cocycle_index": "f(x,y) at NB*x+y", "D_1518_rows": r_hyp,
           "targets": {str(t): {"D_rows": rows(t), "C": C} for t, C in certificate.items() if C is not None}},
          open(f"{S}/l2_certificate_{NB}.json", "w"))
print(f"certificate written to {S}/l2_certificate_{NB}.json")

# ---- numeric cross-check: specialise b to roots of m in F_p and compare with the numeric containment code
exec(open(__file__.replace("l2_symbolic.py", "adversary_size5.py")).read().split("PAIRS = {")[0].replace("S = sys.argv[1]", "pass"))
print("\nnumeric cross-check over F_p at every root r of b^5+b^3-b^2-1, fibre Z/p, beta = r, alpha = r^4 - r:")
for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
    for r in range(p):
        if (r**5 + r**3 - r**2 - 1) % p: continue
        f = Fibre(p, 1, [(r**4 - r) % p], [r]); assert fibre_satisfies(HYP, 1, p, f.A, f.B)
        st = Setting(base, f); rh = st.rows(HYP); NH = nullspace(rh, NB*NB, p)
        verdicts = []
        for t in TARGETS:
            rt = st.rows(t); both = nullspace(rh + rt, NB*NB, p); verdicts.append("blocked" if len(both) == len(NH) else "SEPARATES")
        print(f"  p={p:2} r={r:2}: dim Z2_1518 = {len(NH)}; {dict(zip(TARGETS, verdicts))}")
