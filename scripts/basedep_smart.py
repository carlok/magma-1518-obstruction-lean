"""Base-dependent extensions of the Z/3 shift by Z/p satisfying 1518, for larger p, with the I1 identities used to enumerate β
in O(p^5) instead of (p-1)^9:  I1(x,y): inv(b[y+1][x+2]) = K_x + b[x][x+1]*b[y][x] for a constant K_x independent of y.
Enumerate column 0 of b and b[0][1]; K_0 gives column 2; then x=1 forces K_1 from b[0][1] and gives the rest of column 1;
x=2 is a consistency check.  Then a and c by linear algebra.  Reports the counts of solutions refuting 47 / 3862.
Validated: p=5 -> 160 β, 6400 solutions; p=7 -> 432 β, 7056 solutions.  Usage: basedep_smart.py <data> <p>"""
import sys, itertools, re, time, json
S = sys.argv[1]; p = int(sys.argv[2]); N = 3*p
units = list(range(1, p)); inv = {u: pow(u, -1, p) for u in units}
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
LAWS = {n: (sorted(set(re.findall(r"[a-z]", eq[n-1]))), parse(eq[n-1].split(" = ")[0]), parse(eq[n-1].split(" = ")[1])) for n in (1518, 47, 3862)}
def holds(T, n):
    vs, L, R = LAWS[n]
    def ev(t, env): return env[t] if isinstance(t, str) else T[ev(t[0], env)][ev(t[1], env)]
    return all(ev(L, dict(zip(vs, v))) == ev(R, dict(zip(vs, v))) for v in itertools.product(range(N), repeat=len(vs)))
def table(a, b, c):
    T = [[0]*N for _ in range(N)]
    for x in range(3):
        for s in range(p):
            for y in range(3):
                for t in range(p): T[p*x+s][p*y+t] = p*((y+1) % 3) + (a[x][y]*s + b[x][y]*t + c[x][y]) % p
    return T
def solve_affine(rows, rhs, n):
    M = [r[:] + [rh % p] for r, rh in zip(rows, rhs)]; piv = []; rk = 0
    for col in range(n):
        pr = next((i for i in range(rk, len(M)) if M[i][col] % p), None)
        if pr is None: continue
        M[rk], M[pr] = M[pr], M[rk]; iv = pow(M[rk][col], -1, p); M[rk] = [v*iv % p for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col] % p:
                f = M[i][col]; M[i] = [(u - f*v) % p for u, v in zip(M[i], M[rk])]
        piv.append(col); rk += 1
    if any(all(v == 0 for v in row[:n]) and row[n] for row in M): return
    free = [c for c in range(n) if c not in piv]
    for fv in itertools.product(range(p), repeat=len(free)):
        vec = [0]*n
        for c_, v in zip(free, fv): vec[c_] = v
        for i, c_ in enumerate(piv): vec[c_] = (M[i][n] - sum(M[i][j]*vec[j] for j in free)) % p
        yield vec
def betas():
    """all b in (units)^{3x3} satisfying I1 for x = 0, 1, 2 (each I1(x) has a constant K_x)"""
    for col0 in itertools.product(units, repeat=3):            # b[y][0]
        for b01 in units:                                       # b[0][1]
            for K0 in range(p):                                 # x = 0: inv(b[y+1][2]) = K0 + b[0][1]*b[y][0]
                col2 = {}
                ok = True
                for y in range(3):
                    v = (K0 + b01*col0[y]) % p
                    if v == 0: ok = False; break
                    col2[(y+1) % 3] = inv[v]
                if not ok: continue
                # x = 1: inv(b[y+1][0]) = K1 + b[1][2]*b[y][1]; y = 0 fixes K1 from b[0][1]
                b12 = col2[1]
                K1 = (inv[col0[1]] - b12*b01) % p                 # from y=0: inv(b[1][0]) = K1 + b[1][2]*b[0][1]
                col1 = {0: b01}
                for y in (1, 2):
                    # b[y][1] = (inv(b[y+1][0]) - K1) * inv(b[1][2])
                    v = ((inv[col0[(y+1) % 3]] - K1) * inv[b12]) % p
                    if v == 0: ok = False; break
                    col1[y] = v
                if not ok: continue
                b = [[col0[y], col1[y], col2[y]] for y in range(3)]
                # x = 2 consistency: inv(b[y+1][1]) - b[2][0]*b[y][2] constant in y
                if len({(inv[b[(y+1) % 3][1]] - b[2][0]*b[y][2]) % p for y in range(3)}) != 1: continue
                yield b
t0 = time.time(); nb = 0; count = 0; flags = {}; refuters = []; nref = 0; cycles_seen = {}
others = [(x, (x+2) % 3) for x in range(3)]
for b in betas():
    nb += 1
    a_diag1 = {x: (inv[b[1][(x+2) % 3]] - b[x][(x+1) % 3]*b[0][x]) % p for x in range(3)}   # y = 0 instance of I1
    for dvals in itertools.product(range(p), repeat=3):
        a = [[0]*3 for _ in range(3)]
        for x in range(3): a[x][(x+1) % 3] = a_diag1[x]; a[x][x] = dvals[x]
        rows = []; rhs = []
        for x in range(3):
            for y in range(3):
                row = [0]*3; const = 0
                for (i, j, coef) in (((y+1) % 3, (x+2) % 3, (a[y][y] + b[y][y]) % p), (y, x, (b[(y+1) % 3][(x+2) % 3]*b[x][(x+1) % 3]) % p)):
                    if j == (i+2) % 3: row[others.index((i, j))] = (row[others.index((i, j))] + coef) % p
                    else: const = (const + coef*a[i][j]) % p
                rows.append(row); rhs.append((-const) % p)
        for sol in solve_affine(rows, rhs, 3):
            for (i, j), v in zip(others, sol): a[i][j] = v
            crows = []
            for x in range(3):
                for y in range(3):
                    row = [0]*9
                    row[3*y+y] = (row[3*y+y] + a[(y+1) % 3][(x+2) % 3]) % p
                    row[3*y+x] = (row[3*y+x] + b[(y+1) % 3][(x+2) % 3]*b[x][(x+1) % 3]) % p
                    row[3*x+(x+1) % 3] = (row[3*x+(x+1) % 3] + b[(y+1) % 3][(x+2) % 3]) % p
                    row[3*((y+1) % 3)+(x+2) % 3] = (row[3*((y+1) % 3)+(x+2) % 3] + 1) % p
                    crows.append(row)
            for cvec in solve_affine(crows, [0]*9, 9):
                c = [cvec[3*x:3*x+3] for x in range(3)]; T = table(a, b, c)
                assert holds(T, 1518), "derivation error"
                count += 1; key = (holds(T, 47), holds(T, 3862)); flags[key] = flags.get(key, 0) + 1
                if not key[0] or not key[1]:
                    nref += 1
                    sq = [T[z][z] for z in range(N)]; seen = set(); cyc = []
                    for z in range(N):
                        if z in seen: continue
                        k = 0; w = z
                        while w not in seen: seen.add(w); w = sq[w]; k += 1
                        cyc.append(k)
                    ct = tuple(sorted(cyc, reverse=True)); cycles_seen[ct] = cycles_seen.get(ct, 0) + 1
                    if len(refuters) < 3: refuters.append(T)
print(f"p={p}: beta assignments {nb}; solutions {count}; (47, 3862) flags {flags}; refuting tables {nref}   [{time.time()-t0:.0f}s]", flush=True)
if nref: print(f"  squaring cycle types of refuters: {cycles_seen}"); json.dump(refuters, open(f"{S}/fifteen/refuters_p{p}_sample.json", "w"))
