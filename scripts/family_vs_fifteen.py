"""Are the F+ and F- members over F_5 (c = 0) the two shift-extension models among Le Floch's six 15-element countermodels?
Isomorphism test: an isomorphism commutes with squaring S, whose cycle type is (12, 3) for all eight tables, so it is fixed by
the image of one element of the 12-cycle (12 choices) and one of the 3-cycle (3 choices).  Usage: family_vs_fifteen.py <data>"""
import sys, json
from fractions import Fraction as Fr
S = sys.argv[1]; p = 5; ip = 2; N = 15
fam = json.load(open(f"{S}/fifteen/family_Qi.json"))
def val(s):
    """parse the repr used in family_Qi.json: '1/2-1/2i', '-i', '2', '1+i' ..."""
    s = s.replace(" ", "")
    if s.endswith("i"):
        core = s[:-1]
        k = max(core.rfind("+", 1), core.rfind("-", 1))
        re_, im_ = (core[:k], core[k:]) if k > 0 else ("0", core)
        im_ = {"": "1", "+": "1", "-": "-1"}.get(im_, im_)
    else: re_, im_ = s, "0"
    r, m = Fr(re_), Fr(im_)
    return (r.numerator*pow(r.denominator, -1, p) + m.numerator*pow(m.denominator, -1, p)*ip) % p
def table(name):
    a = [[val(v) for v in row] for row in fam[name]["a"]]; b = [[val(v) for v in row] for row in fam[name]["b"]]
    T = [[0]*N for _ in range(N)]
    for x in range(3):
        for s in range(p):
            for y in range(3):
                for t in range(p): T[p*x+s][p*y+t] = p*((y+1) % 3) + (a[x][y]*s + b[x][y]*t) % p
    return T
def holds1518(T): return all(x == T[T[y][y]][T[x][T[y][x]]] for x in range(N) for y in range(N))
def holds47(T): return all(x == T[x][T[x][T[x][x]]] for x in range(N))
def cycles(T):
    sq = [T[x][x] for x in range(N)]; seen = set(); cyc = []
    for z in range(N):
        if z in seen: continue
        w = z; c = []
        while w not in seen: seen.add(w); c.append(w); w = sq[w]
        cyc.append(c)
    return sorted(cyc, key=len, reverse=True)
def isomorphic(T1, T2):
    c1, c2 = cycles(T1), cycles(T2)
    if [len(c) for c in c1] != [len(c) for c in c2]: return False
    for r12 in range(12):
        for r3 in range(3):
            f = {}
            for cyc1, cyc2, r in ((c1[0], c2[0], r12), (c1[1], c2[1], r3)):
                for k, z in enumerate(cyc1): f[z] = cyc2[(k + r) % len(cyc2)]
            if all(f[T1[x][y]] == T2[f[x]][f[y]] for x in range(N) for y in range(N)): return True
    return False
models = [json.loads(l)["table"] if isinstance(json.loads(l), dict) else json.loads(l) for l in open(f"{S}/fifteen/1518-anti-47-models-size-15.jsonl")   # Le Floch's attachment, Zulip message 547744137; download it into data/fifteen/ if l.strip()]
for name in ("F+", "F-"):
    T = table(name); assert holds1518(T) and not holds47(T)
    print(name, "over F_5:", "squaring cycle lengths", [len(c) for c in cycles(T)], "isomorphic to Le Floch model(s)", [k+1 for k, M in enumerate(models) if isomorphic(T, M)])
print("F+ vs F- over F_5 isomorphic:", isomorphic(table("F+"), table("F-")))
