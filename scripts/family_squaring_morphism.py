"""For each of the eight exact tables in fifteen/family_Qi.json: is the squaring map S(x,s) = (x+1, d_x s) a magma endomorphism,
i.e. S(u v) = S(u) S(v)?  Coefficient conditions: d_{y+1} a_xy = a_{x+1,y+1} d_x and d_{y+1} b_xy = b_{x+1,y+1} d_y for all x, y
(exact arithmetic in Q(i)).  Also reports D and the ETP law number of 'squaring is a morphism' as used in Le Floch's Mace4 input.
Usage: family_squaring_morphism.py <data>"""
import sys, json
from fractions import Fraction as Fr
S = sys.argv[1]
fam = json.load(open(f"{S}/fifteen/family_Qi.json"))
def qi(s):
    s = s.replace(" ", "")
    if s.endswith("i"):
        core = s[:-1]; k = max(core.rfind("+", 1), core.rfind("-", 1))
        re_, im_ = (core[:k], core[k:]) if k > 0 else ("0", core)
        im_ = {"": "1", "+": "1", "-": "-1"}.get(im_, im_)
    else: re_, im_ = s, "0"
    return (Fr(re_), Fr(im_))
mul = lambda p, q: (p[0]*q[0] - p[1]*q[1], p[0]*q[1] + p[1]*q[0]); add = lambda p, q: (p[0]+q[0], p[1]+q[1])
m = lambda k: k % 3
for name, F in fam.items():
    A = [[qi(v) for v in row] for row in F["a"]]; B = [[qi(v) for v in row] for row in F["b"]]
    d = [add(A[z][z], B[z][z]) for z in range(3)]
    ok = all(mul(d[m(y+1)], A[x][y]) == mul(A[m(x+1)][m(y+1)], d[x]) and mul(d[m(y+1)], B[x][y]) == mul(B[m(x+1)][m(y+1)], d[y]) for x in range(3) for y in range(3))
    print(f"{name:3s} D = {F['D']:>3s}  S endomorphism: {ok}")
eq = open(f"{S}/etp/equations.txt").read().splitlines()
for k, line in enumerate(eq):
    if line.replace(" ", "") in ("(x◇y)◇(x◇y)=(x◇x)◇(y◇y)", "(x◇x)◇(y◇y)=(x◇y)◇(x◇y)"): print("squaring-is-a-morphism law number:", k+1, line)
