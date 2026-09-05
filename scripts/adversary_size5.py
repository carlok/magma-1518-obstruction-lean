"""Q1 adversary, second round: bases of size <= 5, scalar fibres Z/p (p <= 13), rank-2 fibres over F_2, F_3, F_5,
rank-3 fibres over F_2. The cocycle condition is computed symbolically as a linear map on the cocycle, so no
extension table is built unless a separation must be verified. Standard library only; independent of algebra_lab.

Bases: sizes 2..4 from Mace4 with clear(lnh) (complete labelled sets, audited against brute force in adversary_size4.py);
size 5 from Mace4 with lnh on, accepted only after checking that lnh-on at size 4 yields every isomorphism class of the
complete size-4 set."""
import itertools, re, sys, time
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
LAW = {}
def law(n):
    if n not in LAW:
        l, r = eq[n-1].split(" = "); LAW[n] = (sorted(set(re.findall(r"[a-z]", eq[n-1]))), parse(l), parse(r))
    return LAW[n]
def ev(t, env, T): return env[t] if isinstance(t, str) else T[ev(t[0], env, T)][ev(t[1], env, T)]
def holds_table(T, n):
    vs, L, R = law(n)
    return all(ev(L, dict(zip(vs, v)), T) == ev(R, dict(zip(vs, v)), T) for v in itertools.product(range(len(T)), repeat=len(vs)))
def mace4_models(path, n):
    out = []
    for block in re.findall(r"function\(\*\(_,_\), \[(.*?)\]\)", open(path).read(), re.S):
        vals = list(map(int, re.findall(r"\d+", block))); assert len(vals) == n*n
        out.append([vals[i*n:(i+1)*n] for i in range(n)])
    return out
def canonical(T):
    n = len(T); best = None
    for perm in itertools.permutations(range(n)):
        inv = {perm[i]: i for i in range(n)}
        U = tuple(tuple(perm[T[inv[i]][inv[j]]] for j in range(n)) for i in range(n))
        if best is None or U < best: best = U
    return best

# --- matrices over F_p, row-major flat lists, k x k ---
def mmul(A, B, k, p): return [sum(A[i*k+l]*B[l*k+j] for l in range(k)) % p for i in range(k) for j in range(k)]
def madd(A, B, p): return [(a+b) % p for a, b in zip(A, B)]
def ident(k): return [1 if i == j else 0 for i in range(k) for j in range(k)]
def coef(t, k, p, A, B):
    """Blueprint P_{w,i}(a,b): coefficient matrix of each variable in the linear magma s◇t = As + Bt."""
    if isinstance(t, str): return {t: ident(k)}
    L, R = coef(t[0], k, p, A, B), coef(t[1], k, p, A, B); out = {}
    for v, M in L.items(): out[v] = mmul(A, M, k, p)
    for v, M in R.items(): out[v] = madd(out.get(v, [0]*(k*k)), mmul(B, M, k, p), p)
    return out
def fibre_satisfies(n, k, p, A, B):
    vs, L, R = law(n); cl, cr = coef(L, k, p, A, B), coef(R, k, p, A, B); z = [0]*(k*k)
    return all(cl.get(v, z) == cr.get(v, z) for v in vs)

class Fibre:
    def __init__(self, p, k, A, B): self.p, self.k, self.A, self.B = p, k, A, B; self.size = p**k
    def dec(self, e): return [(e // self.p**i) % self.p for i in range(self.k)]
    def enc(self, v): return sum((v[i] % self.p) * self.p**i for i in range(self.k))
    def mul(self, M, v): return [sum(M[i*self.k+j]*v[j] for j in range(self.k)) % self.p for i in range(self.k)]

class Setting:
    """Cocycle c has nv = nb*nb*k unknowns; the fibre component of any word at fibre coordinates zero is a k x nv matrix."""
    def __init__(self, base, f): self.base, self.f = base, f; self.nb = len(base); self.nv = self.nb*self.nb*f.k
    def word(self, t, env):
        f, k, nv = self.f, self.f.k, self.nv
        if isinstance(t, str): return env[t], [[0]*nv for _ in range(k)]
        x, Ms = self.word(t[0], env); y, Mt = self.word(t[1], env)
        M = [[0]*nv for _ in range(k)]
        for i in range(k):
            row = M[i]
            for l in range(k):
                a, b = f.A[i*k+l], f.B[i*k+l]
                if a:
                    for j, v in enumerate(Ms[l]):
                        if v: row[j] = (row[j] + a*v) % f.p
                if b:
                    for j, v in enumerate(Mt[l]):
                        if v: row[j] = (row[j] + b*v) % f.p
            row[(x*self.nb + y)*k + i] = (row[(x*self.nb + y)*k + i] + 1) % f.p
        return self.base[x][y], M
    def rows(self, n):
        """Homogeneous cocycle condition rows; None if the base fails the law."""
        vs, L, R = law(n); out = []
        for vals in itertools.product(range(self.nb), repeat=len(vs)):
            env = dict(zip(vs, vals)); x, ML = self.word(L, env); y, MR = self.word(R, env)
            if x != y: return None
            out.extend([(a-b) % self.f.p for a, b in zip(rl, rr)] for rl, rr in zip(ML, MR))
        return out
    def table(self, c):
        f, nb, k = self.f, self.nb, self.f.k; T = []
        for x in range(nb):
            for s in range(f.size):
                Av = f.mul(f.A, f.dec(s)); row = []
                for y in range(nb):
                    cxy = c[(x*nb+y)*k:(x*nb+y+1)*k]
                    for t in range(f.size):
                        Bw = f.mul(f.B, f.dec(t)); row.append(self.base[x][y]*f.size + f.enc([a+b+cc for a, b, cc in zip(Av, Bw, cxy)]))
                T.append(row)
        return T
def rref(rows, nv, p):
    rows = [r[:] for r in rows]; piv = []; r = 0
    for c in range(nv):
        pr = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
        if pr is None: continue
        rows[r], rows[pr] = rows[pr], rows[r]; inv = pow(rows[r][c], -1, p); rows[r] = [v*inv % p for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                fct = rows[i][c]; rows[i] = [(a - fct*b) % p for a, b in zip(rows[i], rows[r])]
        piv.append(c); r += 1
    return rows[:r], piv
def nullspace(rows, nv, p):
    R, piv = rref(rows, nv, p); free = [c for c in range(nv) if c not in piv]; basis = []
    for fcol in free:
        x = [0]*nv; x[fcol] = 1
        for i, c in enumerate(piv): x[c] = (-R[i][fcol]) % p
        basis.append(x)
    return basis

PAIRS = {879: [4065], 1518: [47, 614, 817, 3862], 2054: [255, 2644, 2847, 3456], 2650: [3253]}
CONTROLS = {1076: [2294, 4435], 1516: [1489], 2091: [2098], 2531: [1313, 4435]}
PRIMES = (2, 3, 5, 7, 11, 13)
FIBRE_SHAPES = [(p, 1) for p in PRIMES] + [(2, 2), (3, 2), (5, 2), (2, 3)]
t0 = time.time()

def linear(n, a, b): return [[(a*x + b*y) % n for y in range(n)] for x in range(n)]
bases = {}
print("bases per hypothesis, isomorphism classes by size:")
for h in PAIRS:
    classes = {}
    for n in (2, 3, 4):
        for T in mace4_models(f"{S}/m4/e{h}_{n}_nolnh.out", n):
            assert holds_table(T, h); classes.setdefault(canonical(T), n)
    lnh4 = {canonical(T) for T in mace4_models(f"{S}/m4/e{h}_4.out", 4)}
    assert lnh4 == {c for c, n in classes.items() if n == 4}, f"Mace4 lnh pruning lost a size-4 class for E{h}"
    for T in mace4_models(f"{S}/m4/e{h}_5.out", 5):
        assert holds_table(T, h); classes.setdefault(canonical(T), 5)
    bases[h] = [[list(r) for r in T] for T in classes]
    print(f"  E{h}: { {n: sum(1 for v in classes.values() if v == n) for n in (2, 3, 4, 5)} }  (lnh-on size-4 classes == complete size-4 classes: ok)")
for h in CONTROLS: bases[h] = [linear(n, a, b) for n in range(2, 6) for a in range(n) for b in range(n) if holds_table(linear(n, a, b), h)]

fib = {}
print("\nfibres per hypothesis (coefficient-polynomial test):")
for h in list(PAIRS) + list(CONTROLS):
    fs = []
    for p, k in FIBRE_SHAPES:
        mats = list(itertools.product(range(p), repeat=k*k))
        for A in mats:
            for B in mats:
                if fibre_satisfies(h, k, p, A, B): fs.append(Fibre(p, k, list(A), list(B)))
    fib[h] = fs
    shapes = {f"F_{p}^{k}": sum(1 for f in fs if (f.p, f.k) == (p, k)) for p, k in FIBRE_SHAPES}
    print(f"  E{h}: {len(fs)}  {shapes}")
# cross-check the symbolic fibre test against tables for the small shapes
for h in (879, 1518):
    for p, k in ((2, 1), (3, 1), (5, 1), (2, 2), (3, 2)):
        mats = list(itertools.product(range(p), repeat=k*k))
        for A in mats:
            for B in mats:
                f = Fibre(p, k, list(A), list(B))
                T = [[f.enc([a+b for a, b in zip(f.mul(f.A, f.dec(s)), f.mul(f.B, f.dec(t)))]) for t in range(f.size)] for s in range(f.size)]
                assert fibre_satisfies(h, k, p, A, B) == holds_table(T, h)
print("  symbolic fibre test agrees with table evaluation on all shapes up to F_3^2: ok")

print()
summary = []
for h, targets in list(PAIRS.items()) + list(CONTROLS.items()):
    th = time.time()
    stats = {t: {"settings": 0, "blocked": 0, "separates": 0, "maxdim": 0} for t in targets}; found = []
    for base in bases[h]:
        for f in fib[h]:
            st = Setting(base, f); rh = st.rows(h)
            if rh is None: continue
            NH = nullspace(rh, st.nv, f.p); dim = len(NH)
            for t in targets:
                rec = stats[t]; rec["settings"] += 1; rec["maxdim"] = max(rec["maxdim"], dim)
                if not fibre_satisfies(t, f.k, f.p, f.A, f.B):
                    found.append((t, base, f, [0]*st.nv)); rec["separates"] += 1; continue   # direct product already refutes
                rt = st.rows(t)
                if rt is None or len(nullspace(rh + rt, st.nv, f.p)) < dim:
                    probe = next(c for c in NH if rt is None or any(sum(r[j]*c[j] for j in range(st.nv)) % f.p for r in rt))
                    found.append((t, base, f, probe)); rec["separates"] += 1
                else: rec["blocked"] += 1
    for t, base, f, c in found:
        T = Setting(base, f).table(c); assert holds_table(T, h) and not holds_table(T, t), "separation failed full-table verification"
    for t, base, f, c in found[:4]:
        print(f"  VERIFIED SEPARATION E{h} -/-> E{t}: base {base}, fibre F_{f.p}^{f.k} A={f.A} B={f.B}, carrier {len(base)*f.size}")
    for t in targets: summary.append((h, t, stats[t], h in CONTROLS))
    print(f"  E{h}: {len(bases[h])} bases x {len(fib[h])} fibres in {time.time()-th:.1f}s")
print(f"\ntotal {time.time()-t0:.1f}s\n")
print("pair              settings  blocked  separates  max dim Z2_E")
for h, t, r, ctrl in summary:
    print(f"E{h:<5} -> E{t:<5} {r['settings']:8} {r['blocked']:8} {r['separates']:10}  {r['maxdim']:6}   {'CONTROL' if ctrl else ''}")
