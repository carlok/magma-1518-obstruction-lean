"""Independent re-derivation of the 1518 coefficient identities and of every cocycle row used in l2_symbolic.py,
with NONCOMMUTATIVE coefficients (words in a = alpha, b = beta), specialised to R only at the end. Compares with the
stored matrices in l2_certificate_3.json. Standard library only; shares no code with l2_symbolic.py."""
import re, itertools, json, sys
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
def padd(p, q):
    r = dict(p)
    for w, c in q.items(): r[w] = r.get(w, 0) + c
    return {w: c for w, c in r.items() if c}
def pscale(letter, p): return {letter + w: c for w, c in p.items()}
ONE = {"": 1}
def coeffs(t):
    if isinstance(t, str): return {t: ONE}
    L, R = coeffs(t[0]), coeffs(t[1]); out = {}
    for v, p in L.items(): out[v] = padd(out.get(v, {}), pscale("a", p))
    for v, p in R.items(): out[v] = padd(out.get(v, {}), pscale("b", p))
    return out
l, r = eq[1518-1].split(" = "); L, R = parse(l), parse(r); cl, cr = coeffs(L), coeffs(R)
print("1518 on a linear magma s◇t = a s + b t, identities P_L - P_R = 0 as noncommutative words:")
for v in "xy": print(f"  coefficient of {v}:", padd(cl.get(v, {}), {w: -c for w, c in cr.get(v, {}).items()}))
base = [[(y + 1) % 3 for y in range(3)] for x in range(3)]
def word(t, env):
    if isinstance(t, str): return env[t], {}
    x, F1 = word(t[0], env); y, F2 = word(t[1], env); F = {}
    for k, p in F1.items(): F[k] = padd(F.get(k, {}), pscale("a", p))
    for k, p in F2.items(): F[k] = padd(F.get(k, {}), pscale("b", p))
    F[(x, y)] = padd(F.get((x, y), {}), ONE)
    return base[x][y], F
def rows_nc(n):
    l, r = eq[n-1].split(" = "); L, R = parse(l), parse(r); vs = sorted(set(re.findall(r"[a-z]", eq[n-1]))); out = []
    for vals in itertools.product(range(3), repeat=len(vs)):
        env = dict(zip(vs, vals)); x, FL = word(L, env); y, FR = word(R, env); assert x == y
        row = {}
        for k, p in FL.items(): row[k] = padd(row.get(k, {}), p)
        for k, p in FR.items(): row[k] = padd(row.get(k, {}), {w: -c for w, c in p.items()})
        out.append({k: p for k, p in row.items() if p})
    return out
def polymul(u, w):
    out = [0]*(len(u) + len(w) - 1)
    for i, x in enumerate(u):
        for j, y in enumerate(w): out[i+j] += x*y
    return out
def reduce(u):
    u = u[:]
    for k in range(len(u) - 1, 4, -1):
        c = u[k]; u[k] = 0
        if c: u[k-5] += c; u[k-3] += c; u[k-2] -= c
    return (u + [0]*5)[:5]
def to_R(p):
    A = [0, -1, 0, 0, 1]; B = [0, 1, 0, 0, 0]; total = [0]*5
    for w, c in p.items():
        term = [1]
        for ch in w: term = polymul(term, A if ch == "a" else B)
        total = [x + c*y for x, y in zip(total, reduce(term))]
    return total
stored = json.load(open(f"{S}/l2_certificate_3.json"))
for n, key in ((1518, None), (47, "47"), (614, "614"), (817, "817"), (3862, "3862")):
    mat = [[to_R(row.get((x, y), {})) for x in range(3) for y in range(3)] for row in rows_nc(n)]
    ref = stored["D_1518_rows"] if key is None else stored["targets"][key]["D_rows"]
    print(f"E{n}: independently derived rows equal the stored rows: {mat == ref}")
print("1518 row at (x,y)=(0,1), noncommutative:", rows_nc(1518)[1])
