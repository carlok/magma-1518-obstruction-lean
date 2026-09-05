"""Q1 adversary, third round, prompted by T. Tao's Zulip message of 2024-11-28 (Equational stream, 'Austin pairs', message
484839156): the ETP's 12-element model for 879 !=> 4065 is (x,b,i)◇(y,c,j) = (x+y+f(b,c,j-i), b+c, j+1) on Z/2 x Z/2 x Z/3,
a constant-coefficient extension (alpha = beta = 1 on Z/2) of the 6-element base (b,i)◇(c,j) = (b+c, j+1).
That base is affine over Z/6 with a nonzero constant, outside both Parsimagma's linear-base grid and the size <= 5 sweep.

Here: (1) reproduce that setting exactly; (2) sweep every affine base (a*x + b*y + c) mod n, n <= 8, satisfying each
hypothesis, against scalar fibres Z/p (p <= 13) and rank-2 fibres over F_2, F_3; verify every separation on the full table.
Standard library only."""
import itertools, re, sys, time
S = sys.argv[1]
exec(open(__file__.replace("affine_bases.py", "adversary_size5.py")).read().split("PAIRS = {")[0])

PAIRS = {879: [4065], 1518: [47, 614, 817, 3862], 2054: [255, 2644, 2847, 3456], 2650: [3253]}
FIBRE_SHAPES = [(p, 1) for p in (2, 3, 5, 7, 11, 13)] + [(2, 2), (3, 2)]
def affine(n, a, b, c): return [[(a*x + b*y + c) % n for y in range(n)] for x in range(n)]

def separations(h, base, fibres, targets):
    out = []
    for f in fibres:
        st = Setting(base, f); rh = st.rows(h)
        if rh is None: continue
        NH = nullspace(rh, st.nv, f.p); dim = len(NH)
        for t in targets:
            if not fibre_satisfies(t, f.k, f.p, f.A, f.B): out.append((t, f, [0]*st.nv, dim)); continue
            rt = st.rows(t)
            if rt is None or len(nullspace(rh + rt, st.nv, f.p)) < dim:
                probe = next(c for c in NH if rt is None or any(sum(r[j]*c[j] for j in range(st.nv)) % f.p for r in rt))
                out.append((t, f, probe, dim))
    return out

# (1) Tao's setting
base6 = [[0]*6 for _ in range(6)]   # element (b,i) -> 3*b + i
for b in range(2):
    for i in range(3):
        for c in range(2):
            for j in range(3):
                base6[3*b+i][3*c+j] = 3*((b+c) % 2) + (j+1) % 3
print("Tao base (b,i)◇(c,j) = (b+c, j+1): satisfies E879:", holds_table(base6, 879), "| equals affine 3x+y+4 mod 6 up to the CRT relabelling:",
      sorted(map(tuple, base6)) == sorted(map(tuple, [[ (3*x + y + 4) % 6 for y in range(6)] for x in range(6)])) or "(different labelling; checked below by isomorphism class)")
def canonical6(T):
    n = len(T); best = None
    for perm in itertools.permutations(range(n)):
        inv = {perm[i]: i for i in range(n)}
        U = tuple(tuple(perm[T[inv[i]][inv[j]]] for j in range(n)) for i in range(n))
        if best is None or U < best: best = U
    return best
print("  isomorphic to affine 3x+y+4 mod 6:", canonical6(base6) == canonical6(affine(6, 3, 1, 4)))
f2 = Fibre(2, 1, [1], [1]); st = Setting(base6, f2)
rh = st.rows(879); NH = nullspace(rh, st.nv, 2); rt = st.rows(4065); both = nullspace(rh + rt, st.nv, 2)
print(f"  Z^2_879(base6, Z/2, alpha=beta=1): dimension {len(NH)}; also E4065-cocycles: dimension {len(both)}; separating cocycles: {2**len(NH) - 2**len(both)} of {2**len(NH)}")
sep = separations(879, base6, [f2], [4065])
assert sep, "expected a separation"
T12 = st.table(sep[0][2]); assert holds_table(T12, 879) and not holds_table(T12, 4065)
print("  constructed 12-element table verified: E879 holds, E4065 fails")
open(f"{S}/tao12.json", "w").write(str(T12))

# (2) affine bases with constants, n <= 8
t0 = time.time(); print("\naffine bases (a*x+b*y+c) mod n, n <= 8, satisfying the hypothesis, all (a,b,c):")
fibres = {h: [Fibre(p, k, list(A), list(B)) for p, k in FIBRE_SHAPES for A in itertools.product(range(p), repeat=k*k) for B in itertools.product(range(p), repeat=k*k) if fibre_satisfies(h, k, p, A, B)] for h in PAIRS}
for h, targets in PAIRS.items():
    bases = [(n, a, b, c) for n in range(2, 9) for a in range(n) for b in range(n) for c in range(n) if holds_table(affine(n, a, b, c), h)]
    nonlinear = [x for x in bases if x[3]]
    found = {}
    for (n, a, b, c) in bases:
        for t, f, probe, dim in separations(h, affine(n, a, b, c), fibres[h], targets):
            T = Setting(affine(n, a, b, c), f).table(probe); assert holds_table(T, h) and not holds_table(T, t)
            found.setdefault(t, []).append((n, a, b, c, f, dim, len(T)))
    print(f"  E{h}: {len(bases)} affine bases ({len(nonlinear)} with c != 0), {len(fibres[h])} fibres; separations: " +
          (", ".join(f"E{t}: {len(v)} settings" for t, v in found.items()) if found else "none"))
    for t, v in found.items():
        for (n, a, b, c, f, dim, N) in v[:5]:
            print(f"     E{h} -/-> E{t}: base ({a}x+{b}y+{c}) mod {n}, fibre F_{f.p}^{f.k} A={f.A} B={f.B}, dim Z2_E = {dim}, carrier {N}   VERIFIED")
print(f"\n{time.time()-t0:.1f}s")
