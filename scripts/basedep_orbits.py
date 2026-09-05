"""Orbit representatives of the (a, b) solutions under the torus action (fibre rescaling s -> lambda_x s over base point x):
a'[x][y] = lam[y+1] a[x][y] / lam[x],  b'[x][y] = lam[y+1] b[x][y] / lam[y].  Constant lambda acts trivially, so the group is
(F_p^*)^2; normalizing b[0][0] = b[1][1] = 1 picks one representative per orbit.  Prints the representatives with entries
written as small signed integers, or as multiples of i (a fixed square root of -1) when that is shorter.
Usage: basedep_orbits.py <data> <p> [<p> ...]"""
import sys, time
S = sys.argv[1]
src = open(__file__.replace("basedep_orbits.py", "basedep_smart.py")).read().split("t0 = time.time(); nb = 0")[0]
def pretty(v, p, i):
    cands = []
    for k in range(-(p // 2), p // 2 + 1):
        if k % p == v: cands.append(str(k))
        if i is not None and (k*i) % p == v: cands.append(f"{k}i" if k not in (1, -1) else ("i" if k == 1 else "-i"))
    for k in (2, 3, 4):
        if (pow(k, -1, p)) % p == v: cands.append(f"1/{k}")
        if (-pow(k, -1, p)) % p == v: cands.append(f"-1/{k}")
        if i is not None and (i*pow(k, -1, p)) % p == v: cands.append(f"i/{k}")
        if i is not None and (-i*pow(k, -1, p)) % p == v: cands.append(f"-i/{k}")
    return min(cands, key=len)
for p in map(int, sys.argv[2:]):
    sys.argv = [sys.argv[0], S, str(p)]
    exec(src)
    i = next((v for v in range(1, p) if v*v % p == p-1), None)
    reps = []
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
        reps.append((a, b, D, holds(T, 47)))
    print(f"p={p}, i={i}: {len(reps)} orbit representatives (b[0][0] = b[1][1] = 1)")
    for a, b, D, f47 in sorted(reps, key=lambda r: (r[3], pretty(r[2], p, i))):
        fa = " ".join(f"[{','.join(pretty(v, p, i) for v in row)}]" for row in a)
        fb = " ".join(f"[{','.join(pretty(v, p, i) for v in row)}]" for row in b)
        print(f"  D={pretty(D, p, i):>3}  47 {'holds' if f47 else 'FAILS'}   a = {fa}   b = {fb}")
