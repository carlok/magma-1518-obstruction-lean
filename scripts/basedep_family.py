"""Lift the orbit representatives of basedep_orbits.py to exact elements of Q(i), i^2 = -1, by CRT + rational reconstruction
across the primes 13, 17, 29, 37, 41, then verify the lifted tables EXACTLY in Q(i): the identities I1, I2 (equivalently, law
1518 on Z/3 x M for every module M over a ring containing i with 2, 3 invertible) and the coefficient defects of the four
target laws 47, 614, 817, 3862.  Orbits: T (a = 0), R_k (the I2-orbit u+v = k of a vanishes; k = 0, 1, 2), I+ / I- (D = 1,
b[x][2] = +-i), F+ / F- (D = +-i, the refuting ones).  Usage: basedep_family.py <data>"""
import sys, re, itertools, time, json
from fractions import Fraction as Fr
from math import isqrt
S = sys.argv[1]
src = open(__file__.replace("basedep_family.py", "basedep_smart.py")).read().split("t0 = time.time(); nb = 0")[0]
PRIMES = [13, 17, 29, 37, 41]
def reps_mod(p):
    sys.argv = [sys.argv[0], S, str(p)]; g = {}
    exec(src, g)
    betas, inv, table, holds = g["betas"], g["inv"], g["table"], g["holds"]
    i = next(v for v in range(1, p) if v*v % p == p-1)
    out = []
    for b in betas():
        if b[0][0] != 1 or b[1][1] != 1: continue
        a = [[None]*3 for _ in range(3)]
        for x in range(3): a[x][(x+1) % 3] = (inv[b[1][(x+2) % 3]] - b[x][(x+1) % 3]*b[0][x]) % p
        for x in range(3):
            x2 = (x+2) % 3; a[x2][x2] = (-a[x][(x+1) % 3]*b[x2][x2]*b[x][x2]) % p
        d = [(a[z][z] + b[z][z]) % p for z in range(3)]
        if any(v == 0 for v in d): continue
        for x in range(3):
            x2 = (x+2) % 3; a[x][x2] = (-b[x][x2]*b[x][(x+1) % 3]*a[x2][x] * inv[d[x2]]) % p
        if any((a[x][x]*d[(x+2) % 3] + b[x][x]*b[(x+1) % 3][(x+2) % 3]*a[(x+2) % 3][(x+1) % 3]) % p for x in range(3)): continue
        T = table(a, b, [[0]*3 for _ in range(3)]); assert holds(T, 1518)
        D = d[0]*d[1]*d[2] % p
        out.append((a, b, D, holds(T, 47)))
    assert len(out) == 8, len(out)
    lab = {}
    for a, b, D, f47 in out:
        zeros = [(u, v) for u in range(3) for v in range(3) if a[u][v] == 0]
        if len(zeros) == 9: lab["T"] = (a, b)
        elif len(zeros) == 3 and len({(u+v) % 3 for u, v in zeros}) == 1: lab[f"R{(zeros[0][0]+zeros[0][1]) % 3}"] = (a, b)
        elif D == 1: lab["I+" if b[0][2] == i else "I-"] = (a, b)
        else: lab["F+" if D == i else "F-"] = (a, b)
    assert sorted(lab) == ["F+", "F-", "I+", "I-", "R0", "R1", "R2", "T"], sorted(lab)
    return p, i, lab
def crt(residues, mods):
    M = 1; r = 0
    for res, m in zip(residues, mods):
        r = (r + M*(((res - r) * pow(M, -1, m)) % m)) % (M*m); M *= m
    return r, M
def ratrec(r, M):
    B = isqrt(M // 2); r0, r1 = M, r % M; s0, s1 = 0, 1
    while r1 > B:
        q = r0 // r1; r0, r1 = r1, r0 - q*r1; s0, s1 = s1, s0 - q*s1
    if s1 == 0 or abs(s1) > B: raise ValueError("no reconstruction")
    return Fr(r1, s1) if s1 > 0 else Fr(-r1, -s1)
class QI:
    def __init__(s, re=0, im=0): s.re = Fr(re); s.im = Fr(im)
    def __add__(s, o): o = o if isinstance(o, QI) else QI(o); return QI(s.re + o.re, s.im + o.im)
    __radd__ = __add__
    def __sub__(s, o): o = o if isinstance(o, QI) else QI(o); return QI(s.re - o.re, s.im - o.im)
    def __neg__(s): return QI(-s.re, -s.im)
    def __mul__(s, o): o = o if isinstance(o, QI) else QI(o); return QI(s.re*o.re - s.im*o.im, s.re*o.im + s.im*o.re)
    __rmul__ = __mul__
    def inv(s): n = s.re*s.re + s.im*s.im; return QI(s.re/n, -s.im/n)
    def __eq__(s, o): o = o if isinstance(o, QI) else QI(o); return s.re == o.re and s.im == o.im
    def __hash__(s): return hash((s.re, s.im))
    def iszero(s): return s.re == 0 and s.im == 0
    def norm(s): return s.re*s.re + s.im*s.im
    def __repr__(s):
        if s.im == 0: return str(s.re)
        if s.re == 0: return ("i" if s.im == 1 else "-i" if s.im == -1 else f"{s.im}i")
        return f"{s.re}{'+' if s.im > 0 else '-'}{abs(s.im) if abs(s.im) != 1 else ''}i"
    def modp(s, p, ip):
        return (int(s.re.numerator) * pow(int(s.re.denominator), -1, p) + int(s.im.numerator) * pow(int(s.im.denominator), -1, p) * ip) % p
data = [reps_mod(p) for p in PRIMES]
print("orbit labels found at every prime:", [sorted(lab) == ["F+", "F-", "I+", "I-", "R0", "R1", "R2", "T"] for _, _, lab in data])
def lift(name, partner):
    A = [[None]*3 for _ in range(3)]; B = [[None]*3 for _ in range(3)]
    for mat in (0, 1):
        for u in range(3):
            for v in range(3):
                us, vs = [], []
                for p, ip, lab in data:
                    e = lab[name][mat][u][v]; eb = lab[partner][mat][u][v]
                    us.append(((e + eb) * pow(2, -1, p)) % p); vs.append(((e - eb) * pow(2*ip, -1, p)) % p)
                ru, M = crt(us, PRIMES); rv, _ = crt(vs, PRIMES)
                (A if mat == 0 else B)[u][v] = QI(ratrec(ru, M), ratrec(rv, M))
    return A, B
FAM = {n: lift(n, {"T": "T", "R0": "R0", "R1": "R1", "R2": "R2", "I+": "I-", "I-": "I+", "F+": "F-", "F-": "F+"}[n]) for n in ["T", "R0", "R1", "R2", "I+", "I-", "F+", "F-"]}
# exact checks in Q(i)
eq = open(f"{S}/etp/equations.txt").read().splitlines()
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
LAWS = {n: (sorted(set(re.findall(r"[a-z]", eq[n-1]))), parse(eq[n-1].split(" = ")[0]), parse(eq[n-1].split(" = ")[1])) for n in (1518, 47, 614, 817, 3862)}
def law_defects(A, B, n):
    """evaluate law n on Z/3 x M symbolically (elements = (base point, linear form in the variables)); return the set of nonzero
    coefficient differences (the law holds on Z/3 x M iff each of them kills M)"""
    vs, L, R = LAWS[n]; k = len(vs); defects = set(); base_ok = True
    def ev(t, env):
        if isinstance(t, str): return env[t]
        (x, u), (y, w) = ev(t[0], env), ev(t[1], env)
        return ((y+1) % 3, [A[x][y]*ui + B[x][y]*wi for ui, wi in zip(u, w)])
    for xs in itertools.product(range(3), repeat=k):
        env = {v: (xs[j], [QI(1 if m == j else 0) for m in range(k)]) for j, v in enumerate(vs)}
        (xl, cl), (xr, cr) = ev(L, env), ev(R, env)
        if xl != xr: base_ok = False
        for ci, cj in zip(cl, cr):
            if not (ci - cj).iszero(): defects.add(ci - cj)
    return base_ok, defects
def show(M): return "  ".join("[" + ", ".join(repr(v) for v in row) + "]" for row in M)
summary = {}
for name, (A, B) in FAM.items():
    d = [A[z][z] + B[z][z] for z in range(3)]; D = d[0]*d[1]*d[2]
    ok1518, def1518 = law_defects(A, B, 1518)
    assert ok1518 and not def1518, (name, def1518)
    line = {n: law_defects(A, B, n) for n in (47, 614, 817, 3862)}
    print(f"\n{name}:  a = {show(A)}\n{' '*len(name)}   b = {show(B)}\n{' '*len(name)}   D = {D!r};  1518 holds exactly in Q(i);  target defects: " +
          "; ".join(f"{n}: {'none' if not dfs else ('base fails' if not okb else sorted(map(repr, dfs)))}" for n, (okb, dfs) in line.items()))
    for n, (okb, dfs) in line.items():
        for df in dfs:
            nm = df.norm(); q = nm
            for pr in (2, 3):
                while q.numerator % pr == 0: q = Fr(q.numerator // pr, q.denominator)
                while q.denominator % pr == 0: q = Fr(q.numerator, q.denominator // pr)
            assert q == 1, f"defect {df!r} of law {n} in {name} is not a unit of Z[i,1/6] (norm {nm})"
    # sanity: reduce mod 5 and mod 61 and re-check the table with the finite-field code
    for p in (5, 61):
        sys.argv = [sys.argv[0], S, str(p)]; g = {}; exec(src, g)
        ip = next(v for v in range(1, p) if v*v % p == p-1)
        a = [[A[u][v].modp(p, ip) for v in range(3)] for u in range(3)]; b = [[B[u][v].modp(p, ip) for v in range(3)] for u in range(3)]
        T = g["table"](a, b, [[0]*3 for _ in range(3)])
        assert g["holds"](T, 1518) and g["holds"](T, 47) == (not line[47][1]), (name, p)
    summary[name] = {"a": [[repr(v) for v in row] for row in A], "b": [[repr(v) for v in row] for row in B], "D": repr(D),
                     "refutes": [n for n, (okb, dfs) in line.items() if dfs]}
# rotation check: R1, R2 are the base rotations of R0 (relabel x -> x+1, then renormalise b00 = b11 = 1 by fibre rescaling)
def rotate(A, B):
    A2 = [[A[(u+1) % 3][(v+1) % 3] for v in range(3)] for u in range(3)]; B2 = [[B[(u+1) % 3][(v+1) % 3] for v in range(3)] for u in range(3)]
    lam = [QI(1), None, None]; lam[1] = lam[0]*B2[0][0].inv(); lam[2] = lam[1]*B2[1][1].inv()
    A3 = [[lam[(v+1) % 3]*A2[u][v]*lam[u].inv() for v in range(3)] for u in range(3)]
    B3 = [[lam[(v+1) % 3]*B2[u][v]*lam[v].inv() for v in range(3)] for u in range(3)]
    return A3, B3
def same(X, Y): return all(X[0][u][v] == Y[0][u][v] and X[1][u][v] == Y[1][u][v] for u in range(3) for v in range(3))
r1 = rotate(*FAM["R0"]); r2 = rotate(*r1); r3 = rotate(*r2)
print("\nrotations of R0 give:", [n for n in FAM if same(r1, FAM[n])], [n for n in FAM if same(r2, FAM[n])], "and back:", same(r3, FAM["R0"]))
for n in ("T", "I+", "I-", "F+", "F-"): print(f"rotation of {n} is", [m for m in FAM if same(rotate(*FAM[n]), FAM[m])])
json.dump(summary, open(f"{S}/fifteen/family_Qi.json", "w"), indent=1)
print("\nsummary written to fifteen/family_Qi.json")
