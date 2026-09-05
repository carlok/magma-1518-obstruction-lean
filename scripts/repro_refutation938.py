"""Selective reproduction for the stage-1 audit. Standard library only. Nothing here touches algebra_lab."""
import itertools, random, re, sys
S = sys.argv[1]
eq = open(f"{S}/etp/equations.txt").read().splitlines()

def parse(s):
    toks = re.findall(r"[a-z]|◇|\(|\)", s)
    pos = [0]
    def atom():
        t = toks[pos[0]]; pos[0] += 1
        if t == "(":
            e = expr(); assert toks[pos[0]] == ")"; pos[0] += 1; return e
        return t
    def expr():
        left = atom()
        while pos[0] < len(toks) and toks[pos[0]] == "◇":
            pos[0] += 1; left = (left, atom())
        return left
    e = expr(); assert pos[0] == len(toks); return e

def law(n):
    l, r = eq[n-1].split(" = "); L, R = parse(l), parse(r)
    vs = sorted(set(re.findall(r"[a-z]", eq[n-1]))); return vs, L, R

def ev(t, env, T):
    return env[t] if isinstance(t, str) else T[ev(t[0], env, T)][ev(t[1], env, T)]

def holds(T, n):
    vs, L, R = law(n); N = len(T)
    for vals in itertools.product(range(N), repeat=len(vs)):
        env = dict(zip(vs, vals))
        if ev(L, env, T) != ev(R, env, T): return False, env
    return True, None

# 1. ETP Refutation938: Fin 65 table, claimed E1076 true, E2294 and E4435 false.
T = eval(open(f"{S}/etp/table938.json").read()); N = len(T)
assert N == 65 and all(len(r) == N and all(0 <= c < N for c in r) for r in T), "not a closed 65x65 table"
for n in (1076, 2294, 4435):
    ok, wit = holds(T, n); print(f"Refutation938: E{n} {'holds' if ok else 'fails at ' + str(wit)}")

# 2. Extension shape: find a labelling e -> (base, fibre) under which the table is (x*y, alpha s + beta t + c(x,y)).
def shape(T, nb, m, split):
    base = {}; fib = {}
    for e in range(N):
        for f in range(N):
            (x, s), (y, t), (z, u) = split(e), split(f), split(T[e][f])
            base.setdefault((x, y), z)
            if base[(x, y)] != z: return None
            fib.setdefault((x, y), []).append((s, t, u))
    for a in range(m):
        for b in range(m):
            cs = {}
            good = True
            for key, trip in fib.items():
                c = {(u - a*s - b*t) % m for s, t, u in trip}
                if len(c) != 1: good = False; break
                cs[key] = c.pop()
            if good: return base, a, b, cs
    return None
for name, split in (("e = 13*x + s", lambda e: divmod(e, 13)), ("e = x + 5*s", lambda e: (e % 5, e // 5))):
    r = shape(T, 5, 13, split)
    if r:
        base, a, b, cs = r
        print(f"labelling {name}: base table {[[base[(x,y)] for y in range(5)] for x in range(5)]}, alpha={a}, beta={b}")
        print("  base equals 4x+2y mod 5:", all(base[(x,y)] == (4*x+2*y) % 5 for x in range(5) for y in range(5)))
        cocycle_etp = cs
    else:
        print(f"labelling {name}: not an extension of this shape")

# 3. Cocycle space of E1076 for base 4x+2y on Z/5, fibre Z/13, alpha=5, beta=9. Linear algebra over F_13.
p, nb = 13, 5
base_op = lambda x, y: (4*x + 2*y) % nb
alpha, beta = 5, 9
def ext_table(c):
    T = [[0]*(nb*p) for _ in range(nb*p)]
    for x in range(nb):
        for s in range(p):
            for y in range(nb):
                for t in range(p):
                    T[x*p+s][y*p+t] = base_op(x, y)*p + (alpha*s + beta*t + c[(x, y)]) % p
    return T
def residual(c, n, fibre_coords):
    """Fibre component of LHS - RHS over all base assignments, at fixed fibre coordinates."""
    vs, L, R = law(n); T = ext_table(c); out = []
    for vals in itertools.product(range(nb), repeat=len(vs)):
        env = {v: x*p + fibre_coords[i] for i, (v, x) in enumerate(zip(vs, vals))}
        l, r = ev(L, env, T), ev(R, env, T)
        assert l // p == r // p, "base fails the law"
        out.append((l - r) % p)
    return out
keys = [(x, y) for x in range(nb) for y in range(nb)]
zero = {k: 0 for k in keys}
def system(n):
    r0 = residual(zero, n, [0]*7)
    cols = []
    for k in keys:
        c = dict(zero); c[k] = 1
        cols.append([(a - b) % p for a, b in zip(residual(c, n, [0]*7), r0)])
    rows = [[cols[j][i] for j in range(len(keys))] + [(-r0[i]) % p] for i in range(len(r0))]
    return rows
def rref(rows, nv):
    rows = [r[:] for r in rows]; piv = []; r = 0
    for c in range(nv):
        pr = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
        if pr is None: continue
        rows[r], rows[pr] = rows[pr], rows[r]
        inv = pow(rows[r][c], -1, p); rows[r] = [v*inv % p for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                f = rows[i][c]; rows[i] = [(a - f*b) % p for a, b in zip(rows[i], rows[r])]
        piv.append(c); r += 1
    inconsistent = any(all(v == 0 for v in row[:nv]) and row[nv] for row in rows)
    return rows[:r], piv, inconsistent
def solve_space(n):
    rows, piv, bad = rref(system(n), len(keys)); assert not bad
    free = [c for c in range(len(keys)) if c not in piv]
    def sol(fv):
        x = [0]*len(keys)
        for c, val in zip(free, fv): x[c] = val
        for i, c in enumerate(piv): x[c] = (rows[i][-1] - sum(rows[i][j]*x[j] for j in free)) % p
        return x
    part = sol([0]*len(free)); basis = [[(a-b) % p for a, b in zip(sol([1 if i == j else 0 for j in range(len(free))]), part)] for i in range(len(free))]
    return len(piv), part, basis
def flat(c, n):
    return all(residual(c, n, fc) == residual(c, n, [0]*7) for fc in ([3]*7, [1, 7, 2, 11, 0, 5, 9]))
rank, part, basis = solve_space(1076)
print(f"E1076 cocycle system: rank {rank}, solution dimension {len(basis)}, particular solution is {'zero' if not any(part) else 'nonzero'}")
print("residual flat in fibre coordinates for E1076:", flat(zero, 1076))
def in_space(c):
    v = [c[k] for k in keys]
    rows, piv, _ = rref(system(1076), len(keys))
    return all(sum(row[j]*v[j] for j in range(len(keys))) % p == row[-1] for row in rows)
print("ETP's cocycle lies in the E1076 solution space:", in_space(cocycle_etp))
# Exact rather than sampled: the E1076-cocycles that also satisfy the target form a subspace.
for target in (2294, 4435):
    rows, piv, bad = rref(system(1076) + system(target), len(keys))
    both = len(keys) - len(piv) if not bad else -1
    frac = 1 - p**(both - len(basis)) if both >= 0 else 1.0
    print(f"E1076 & E{target} cocycles: dimension {both}; fraction of E1076-cocycles refuting E{target}: {frac:.4f}")
    print(f"  target residual flat at zero cocycle: {flat(zero, target)}")
random.seed(1)
hits = 0
for _ in range(400):
    coeffs = [random.randrange(p) for _ in basis]
    c = {k: (part[i] + sum(cf*b[i] for cf, b in zip(coeffs, basis))) % p for i, k in enumerate(keys)}
    T2 = ext_table(c)
    assert holds(T2, 1076)[0]
    if not holds(T2, 2294)[0] or not holds(T2, 4435)[0]: hits += 1
assert any(any(b) for b in basis), "basis must be nonzero"
# Refutation937 (Fin 35): claimed base order 5, fibre Z/7, fibres affine.
T7 = eval(open(f"{S}/etp/table937.json").read()); N = len(T7)
for n in (1516, 1489):
    ok, wit = holds(T7, n); print(f"Refutation937: E{n} {'holds' if ok else 'fails at ' + str(wit)}")
r = shape(T7, 5, 7, lambda e: divmod(e, 7))
print("Refutation937 labelling e = 7*x + s:", "not an extension of this shape" if r is None else f"base {[[r[0][(x,y)] for y in range(5)] for x in range(5)]} alpha={r[1]} beta={r[2]}")
print(f"400 sampled E1076-cocycles: all satisfy E1076 on the full 65-element table; {hits} refute E2294 or E4435")
