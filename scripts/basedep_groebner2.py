"""Reduced Groebner classification: eliminate a by hand.  With b00 = b11 = 1 (torus normalisation) put
  alpha_x = a[x][x+1] = 1/b[1][x+2] - b[x][x+1] b[0][x]                (I1 at y = 0)
  a[x+2][x+2] = -alpha_x b[x+2][x+2] b[x][x+2]                         (I2, orbit relation, using I1 at y = x+2)
  d_z = a[z][z] + b[z][z],  a[x][x+2] = -b[x][x+2] b[x][x+1] alpha_{x+2} / d_{x+2}
and impose ALL 18 identities I1, I2 as rational functions of the 7 free b entries; the numerators, together with a Rabinowitsch
variable z making prod(b) * prod(d) * prod(b[1][x+2]) invertible, generate the ideal.  Expected: zero-dimensional of degree 8
(T, R0, R1, R2, I+, I-, F+, F-).  Usage: venv/bin/python basedep_groebner2.py"""
import sympy as sp, time
b = [[sp.Symbol(f"b{x}{y}") for y in range(3)] for x in range(3)]
b[0][0] = sp.Integer(1); b[1][1] = sp.Integer(1)
free = [b[0][1], b[0][2], b[1][0], b[1][2], b[2][0], b[2][1], b[2][2]]
m = lambda k: k % 3
alpha = [1/b[1][m(x+2)] - b[x][m(x+1)]*b[0][x] for x in range(3)]
a = [[None]*3 for _ in range(3)]
for x in range(3): a[x][m(x+1)] = alpha[x]
for x in range(3): a[m(x+2)][m(x+2)] = -alpha[x]*b[m(x+2)][m(x+2)]*b[x][m(x+2)]
d = [a[z][z] + b[z][z] for z in range(3)]
for x in range(3): a[x][m(x+2)] = -b[x][m(x+2)]*b[x][m(x+1)]*alpha[m(x+2)] / d[m(x+2)]
eqs = []
for x in range(3):
    for y in range(3):
        eqs.append(b[m(y+1)][m(x+2)]*(a[x][m(x+1)] + b[x][m(x+1)]*b[y][x]) - 1)
        eqs.append(a[m(y+1)][m(x+2)]*d[y] + b[m(y+1)][m(x+2)]*b[x][m(x+1)]*a[y][x])
nums = []
for e in eqs:
    n_, _ = sp.fraction(sp.together(e)); n_ = sp.expand(n_)
    if n_ != 0: nums.append(n_)
z = sp.Symbol("z")
den = sp.Mul(*free) * sp.Mul(*[sp.fraction(sp.together(dz))[0] for dz in d]) * sp.Mul(*[b[1][m(x+2)] for x in range(3)])
nums.append(sp.expand(z*sp.expand(den) - 1))
gens = free + [z]
print(f"{len(nums)} polynomials in {len(gens)} variables, degrees {[sp.Poly(n_, *gens).total_degree() for n_ in nums]}", flush=True)
t0 = time.time()
G = sp.groebner(nums, *gens, order="grevlex", domain="QQ")
print(f"grevlex basis: {len(G.exprs)} polynomials, zero-dimensional: {G.is_zero_dimensional}  [{time.time()-t0:.0f}s]", flush=True)
if G.is_zero_dimensional:
    lead = [sp.Poly(g, *gens).monoms(order="grevlex")[0] for g in G.exprs]
    def divisible(mn): return any(all(mi >= li for mi, li in zip(mn, l)) for l in lead)
    count = 0; frontier = [tuple([0]*len(gens))]; seen = set(frontier)
    while frontier:
        mn = frontier.pop()
        if divisible(mn): continue
        count += 1
        for k in range(len(gens)):
            m2 = list(mn); m2[k] += 1; m2 = tuple(m2)
            if m2 not in seen and sum(m2) <= 60: seen.add(m2); frontier.append(m2)
    print(f"degree of the ideal (solutions over the closure with multiplicity): {count}", flush=True)
t0 = time.time()
G2 = sp.groebner(nums, *gens, order="lex", domain="QQ")
print(f"lex basis: {len(G2.exprs)} polynomials  [{time.time()-t0:.0f}s]", flush=True)
for g in G2.exprs:
    if len(g.free_symbols) <= 2: print("  ", sp.factor(g), flush=True)
