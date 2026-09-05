"""Theorem F beyond prime fields: build the F+ member of basedep_family.py over F_9 = F_3[i] (27 elements) and over Z/25 with
i = 7 (75 elements), and check 1518 and the four targets by brute force.  Usage: family_more_fibres.py <data>"""
import sys, json, itertools, re
from fractions import Fraction as Fr
S = sys.argv[1]
fam = json.load(open(f"{S}/fifteen/family_Qi.json"))["F+"]
def qi(s):
    s = s.replace(" ", "")
    if s.endswith("i"):
        core = s[:-1]; k = max(core.rfind("+", 1), core.rfind("-", 1))
        re_, im_ = (core[:k], core[k:]) if k > 0 else ("0", core)
        im_ = {"": "1", "+": "1", "-": "-1"}.get(im_, im_)
    else: re_, im_ = s, "0"
    return Fr(re_), Fr(im_)
A = [[qi(v) for v in row] for row in fam["a"]]; B = [[qi(v) for v in row] for row in fam["b"]]
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
def check(name, elems, add, mul, coef):
    """elems: list of fibre elements; add/mul: fibre ring ops; coef(q) maps a Q(i) constant into the ring"""
    idx = {e: k for k, e in enumerate(elems)}; m = len(elems); N = 3*m
    a = [[coef(A[x][y]) for y in range(3)] for x in range(3)]; b = [[coef(B[x][y]) for y in range(3)] for x in range(3)]
    T = [[0]*N for _ in range(N)]
    for x in range(3):
        for s in elems:
            for y in range(3):
                for t in elems: T[m*x+idx[s]][m*y+idx[t]] = m*((y+1) % 3) + idx[add(mul(a[x][y], s), mul(b[x][y], t))]
    def holds(n):
        vs, L, R = LAWS[n]
        def ev(t, env): return env[t] if isinstance(t, str) else T[ev(t[0], env)][ev(t[1], env)]
        return all(ev(L, dict(zip(vs, v))) == ev(R, dict(zip(vs, v))) for v in itertools.product(range(N), repeat=len(vs)))
    print(f"{name}: {N} elements; 1518 {'holds' if holds(1518) else 'FAILS'}; " + ", ".join(f"{n} {'holds' if holds(n) else 'fails'}" for n in (47, 614, 817, 3862)))
# F_9 = F_3[i]: elements (u, v) = u + v i
F9 = [(u, v) for u in range(3) for v in range(3)]
check("F_9", F9, lambda p, q: ((p[0]+q[0]) % 3, (p[1]+q[1]) % 3), lambda p, q: ((p[0]*q[0] - p[1]*q[1]) % 3, (p[0]*q[1] + p[1]*q[0]) % 3),
      lambda c: ((c[0].numerator*pow(c[0].denominator, -1, 3)) % 3, (c[1].numerator*pow(c[1].denominator, -1, 3)) % 3))
# Z/25 with i = 7
n = 25; i25 = 7; assert i25*i25 % n == n-1
check("Z/25 (i = 7)", list(range(n)), lambda p, q: (p+q) % n, lambda p, q: (p*q) % n,
      lambda c: (c[0].numerator*pow(c[0].denominator, -1, n) + c[1].numerator*pow(c[1].denominator, -1, n)*i25) % n)
