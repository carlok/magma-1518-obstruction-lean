"""Independent census with z3 (no Mace4): (1) does a one-generated 1518-magma of size n exist, n = 2..7?
Encoding: table T as an uninterpreted function on a finite enumeration sort; 1518 asserted at all n^2 assignments;
one-generated: reachability sets S_0 = {g}, S_{i+1} = S_i ∪ S_i◇S_i, with S_{n-1} = everything, g = element 0 (WLOG by symmetry).
(2) labelled model counts at n = 4, 5 by blocking-clause enumeration, to compare with Mace4's complete enumeration."""
import sys, time, re
from z3 import *
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
l, r = eq[1518-1].split(" = "); L1518, R1518 = parse(l), parse(r)
def build(n):
    El, els = EnumSort(f"E{n}_{build.calls}", [f"e{i}" for i in range(n)]); build.calls += 1
    f = Function("op", El, El, El)
    def ev(t, env): return env[t] if isinstance(t, str) else f(ev(t[0], env), ev(t[1], env))
    s = Solver()
    for x in els:
        for y in els: s.add(ev(L1518, {"x": x, "y": y}) == ev(R1518, {"x": x, "y": y}))
    return s, f, els
build.calls = 0
t0 = time.time()
print("one-generated 1518-magma of size n (generator = e0):")
for n in range(2, 8):
    s, f, els = build(n)
    reach = [[Bool(f"r_{i}_{k}") for k in range(n)] for i in range(n)]
    for k in range(n): s.add(reach[0][k] == (k == 0))
    for i in range(n-1):
        for k in range(n):
            prods = [And(reach[i][a], reach[i][b], f(els[a], els[b]) == els[k]) for a in range(n) for b in range(n)]
            s.add(reach[i+1][k] == Or(reach[i][k], Or(prods)))
    for k in range(n): s.add(reach[n-1][k])
    res = s.check()
    line = f"  n={n}: {res}"
    if res == sat:
        m = s.model(); T = [[els.index(m.eval(f(els[a], els[b]), model_completion=True)) for b in range(n)] for a in range(n)]
        line += f"  table {T}"
    print(line + f"   [{time.time()-t0:.0f}s]", flush=True)
print("\nlabelled model counts by blocking-clause enumeration:")
for n in (2, 3, 4, 5):
    s, f, els = build(n); count = 0
    while s.check() == sat:
        m = s.model(); count += 1
        s.add(Or([f(els[a], els[b]) != m.eval(f(els[a], els[b]), model_completion=True) for a in range(n) for b in range(n)]))
    print(f"  n={n}: {count} labelled 1518-magmas   [{time.time()-t0:.0f}s]", flush=True)
