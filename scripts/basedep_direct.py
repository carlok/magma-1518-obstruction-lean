"""Base-dependent extensions of the Z/3 shift by Z/p satisfying 1518: direct O(1) determination of a from b.
Derivation (I1, I2 as in L2_NOTE.md, all b entries nonzero):
  I1(x, y):  a[x][x+1] = inv(b[y+1][x+2]) - b[x][x+1]*b[y][x]                      (constant in y; y = x+2 gives a[x][x+1] + b[x][x+1]*b[x+2][x] = inv(b[x][x+2]))
  I2 with (u, v) = (y+1, x+2):  a[u][v]*d[u+2] = -b[u][v]*b[v+1][v+2]*a[u+2][v+1],  d[z] = a[z][z] + b[z][z]
     (u, v) = (x, x+1):  a[x+2][x+2] = -a[x][x+1]*b[x+2][x+2]*b[x][x+2]              (using I1 at y = x+2; d[x+2] != 0 always)
     (u, v) = (x, x+2):  a[x][x+2] = -b[x][x+2]*b[x][x+1]*a[x+2][x] * inv(d[x+2])
     (u, v) = (x, x):    a[x][x]*d[x+2] + b[x][x]*b[x+1][x+2]*a[x+2][x+1] = 0        (consistency check)
So each beta gives at most one a; the p^3 search over the diagonal in the earlier script was redundant.
Also records D = d[0]*d[1]*d[2] (squaring cubed acts on the fibre by D) against the 47 / 3862 verdicts.
Validated against the earlier enumerations: p=5 -> 128 pairs, 32 refuting; p=13 -> 1152 / 288; p=17 -> 2048 / 512.
Usage: basedep_direct.py <data> <p> [<p> ...]"""
import sys, time, itertools
S = sys.argv[1]
src = open(__file__.replace("basedep_direct.py", "basedep_smart.py")).read().split("t0 = time.time(); nb = 0")[0]
for p in map(int, sys.argv[2:]):
    sys.argv = [sys.argv[0], S, str(p)]
    exec(src)
    def mult_order(D):
        k = 1; w = D % p
        while w != 1: w = w*D % p; k += 1
        return k
    t0 = time.time(); nb = 0; npairs = 0; nref = 0; cyc_types = {}; Dtab = {}; mismatch = 0
    for b in betas():
        nb += 1
        a = [[None]*3 for _ in range(3)]
        for x in range(3):
            a[x][(x+1) % 3] = (inv[b[1][(x+2) % 3]] - b[x][(x+1) % 3]*b[0][x]) % p        # I1 at y = 0 (constant in y by construction)
        for x in range(3):
            x2 = (x+2) % 3
            a[x2][x2] = (-a[x][(x+1) % 3]*b[x2][x2]*b[x][x2]) % p
        d = [(a[z][z] + b[z][z]) % p for z in range(3)]
        if any(v == 0 for v in d): continue
        for x in range(3):
            x2 = (x+2) % 3
            a[x][x2] = (-b[x][x2]*b[x][(x+1) % 3]*a[x2][x] * inv[d[x2]]) % p
        if any((a[x][x]*d[(x+2) % 3] + b[x][x]*b[(x+1) % 3][(x+2) % 3]*a[(x+2) % 3][(x+1) % 3]) % p for x in range(3)): continue
        # verify both identities on all 9 pairs directly, then the full table for the first few and a random sample
        ok = all((b[(y+1) % 3][(x+2) % 3]*(a[x][(x+1) % 3] + b[x][(x+1) % 3]*b[y][x])) % p == 1 and
                 (a[(y+1) % 3][(x+2) % 3]*d[y] + b[(y+1) % 3][(x+2) % 3]*b[x][(x+1) % 3]*a[y][x]) % p == 0
                 for x in range(3) for y in range(3))
        assert ok, "derivation error (I1/I2)"
        npairs += 1
        D = d[0]*d[1]*d[2] % p; oD = mult_order(D)
        T = table(a, b, [[0]*3 for _ in range(3)])
        if npairs <= 20 or npairs % 97 == 0: assert holds(T, 1518), "derivation error (table)"
        f47 = holds(T, 47); f3862 = holds(T, 3862)
        if f47 != f3862: mismatch += 1
        key = (oD, f47); Dtab[key] = Dtab.get(key, 0) + 1
        if not f47:
            nref += 1
            sq = [T[z][z] for z in range(N)]; seen = set(); cyc = []
            for z in range(N):
                if z in seen: continue
                k = 0; w = z
                while w not in seen: seen.add(w); w = sq[w]; k += 1
                cyc.append(k)
            ct = tuple(sorted(cyc, reverse=True)); cyc_types[ct] = cyc_types.get(ct, 0) + 1
    print(f"p={p} ({p % 4} mod 4): beta {nb}; pairs {npairs}; refuting {nref}; 47/3862 mismatches {mismatch}; (ord D, holds 47) -> count {dict(sorted(Dtab.items()))}; squaring types of refuters {cyc_types}   [{time.time()-t0:.0f}s]", flush=True)
