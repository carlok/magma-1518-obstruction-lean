"""Is every 1518-cocycle over the Z/3 shift a coboundary, for every finite fibre?  H^2_1518(shift, M) = 0.
Certificate sought: matrices P (3x9) and Q (9x9) over R = Z[b]/(b^5+b^3-b^2-1) with  I_9 = E*P + Q*D,
where D is the 9x9 cocycle matrix of 1518 and E the 9x3 coboundary matrix g -> (g(x◇y) - a g(x) - b g(y)).
Given such P, Q: D v = 0 implies v = E (P v), so v is a coboundary, for every R-module M. Standard library only."""
import sys, itertools, json, time
S = sys.argv[1]
exec(open(__file__.replace("h2_vanishing.py", "l2_symbolic.py")).read().split("HYP = 1518; TARGETS")[0])
t0 = time.time()
D = rows(1518)                              # 9 rows in R^9
def dot(row, vec):
    acc = ZERO[:]
    for e, v in zip(row, vec): acc = radd(acc, rmul(e, v))
    return acc
E = [[ZERO[:] for _ in range(3)] for _ in range(9)]   # 9 x 3
for x in range(3):
    for y in range(3):
        for k in range(3):
            v = ZERO[:]
            if base[x][y] == k: v = radd(v, ONE)
            if x == k: v = rsub(v, A)
            if y == k: v = rsub(v, B)
            E[3*x+y][k] = v
assert all(dot(row, [E[i][k] for i in range(9)]) == ZERO for k in range(3) for row in D), "coboundaries must be cocycles"

# Unknowns: P[k][j] (3x9) and Q[i][l] (9x9), each in R = Z^5. Linear map (P,Q) -> E P + Q D in R^{9x9}; target I_9.
# Build Z-generators: for each unknown entry and each power b^i, the image matrix flattened to Z^{405}.
def matmul(X, Y, n, m, l):   # X n x m, Y m x l
    return [[ (lambda acc: acc)( [0]*5 ) for _ in range(l)] for _ in range(n)] if False else \
           [[ (lambda i, j: (lambda acc: acc)(None))(i, j) for j in range(l)] for i in range(n)]
def mm(X, Y):
    n, m, l = len(X), len(Y), len(Y[0]); out = [[ZERO[:] for _ in range(l)] for _ in range(n)]
    for i in range(n):
        for k in range(m):
            if X[i][k] != ZERO:
                for j in range(l): out[i][j] = radd(out[i][j], rmul(X[i][k], Y[k][j]))
    return out
def flat(Mx): return [c for row in Mx for e in row for c in e]
gens = []; labels = []
for k in range(3):
    for j in range(9):
        for i in range(5):
            P = [[ZERO[:] for _ in range(9)] for _ in range(3)]; P[k][j] = rpow(B, i)
            gens.append(flat(mm(E, P))); labels.append(("P", k, j, i))
for r_ in range(9):
    for l in range(9):
        for i in range(5):
            Q = [[ZERO[:] for _ in range(9)] for _ in range(9)]; Q[r_][l] = rpow(B, i)
            gens.append(flat(mm(Q, D))); labels.append(("Q", r_, l, i))
I9 = [[ONE[:] if i == j else ZERO[:] for j in range(9)] for i in range(9)]
ech = echelon(gens); combo = member(ech, flat(I9))
print(f"[{time.time()-t0:.0f}s] homotopy certificate I = E P + Q D over R:", "FOUND" if combo is not None else "does not exist over R")
if combo is not None:
    P = [[ZERO[:] for _ in range(9)] for _ in range(3)]; Q = [[ZERO[:] for _ in range(9)] for _ in range(9)]
    for c, lab in zip(combo, labels):
        if c:
            if lab[0] == "P": _, k, j, i = lab; P[k][j] = radd(P[k][j], [c*x for x in rpow(B, i)])
            else: _, r_, l, i = lab; Q[r_][l] = radd(Q[r_][l], [c*x for x in rpow(B, i)])
    check = [[radd(u, v) for u, v in zip(ru, rv)] for ru, rv in zip(mm(E, P), mm(Q, D))]
    assert check == I9, "certificate re-verification failed"
    print("  re-verified by direct multiplication in R: E P + Q D = I_9")
    print("  nonzero entries: P", sum(1 for r in P for e in r if e != ZERO), " Q", sum(1 for r in Q for e in r if e != ZERO))
    json.dump({"ring": "Z[b]/(b^5+b^3-b^2-1)", "D_1518": D, "E_coboundary": E, "P": P, "Q": Q}, open(f"{S}/h2_certificate.json", "w"))

# Non-field fibre by brute force: M = Z/4, beta = 1 (1+1-1-1 = 0 mod 4), alpha = 1 - 1 = 0
p4 = 4; al, be = 0, 1
keys = [(x, y) for x in range(3) for y in range(3)]
def is_cocycle(f):
    return all((al*f[(y, y)] + be*be*f[(y, x)] + be*f[(x, (x+1) % 3)] + f[((y+1) % 3, (x+2) % 3)]) % p4 == 0 for x in range(3) for y in range(3))
coc = [f for f in (dict(zip(keys, v)) for v in itertools.product(range(p4), repeat=9)) if is_cocycle(f)]
cob = {tuple((g[base[x][y]] - al*g[x] - be*g[y]) % p4 for x in range(3) for y in range(3)) for g in itertools.product(range(p4), repeat=3)}
print(f"\nZ/4, beta=1, alpha=0: cocycles {len(coc)}, coboundaries {len(cob)}, every cocycle a coboundary: {all(tuple(f[k] for k in keys) in cob for f in coc)}")

# Contrast: 879 over the affine base 3x+y+1 mod 6 with fibre Z/2, alpha = beta = 1
exec(open(__file__.replace("h2_vanishing.py", "adversary_size5.py")).read().split("PAIRS = {")[0].replace("S = sys.argv[1]", "pass"))
b6 = [[(3*x + y + 1) % 6 for y in range(6)] for x in range(6)]; f2 = Fibre(2, 1, [1], [1]); st = Setting(b6, f2)
Z879 = len(nullspace(st.rows(879), 36, 2))
E6 = [[((1 if b6[x][y] == k else 0) - (1 if x == k else 0) - (1 if y == k else 0)) % 2 for k in range(6)] for x in range(6) for y in range(6)]
def rank2(rowsM):
    A=[r[:] for r in rowsM]; rk=0
    for c in range(len(A[0])):
        piv=next((i for i in range(rk,len(A)) if A[i][c]),None)
        if piv is None: continue
        A[rk],A[piv]=A[piv],A[rk]
        for i in range(len(A)):
            if i!=rk and A[i][c]: A[i]=[(u+v)%2 for u,v in zip(A[i],A[rk])]
        rk+=1
    return rk
B879 = rank2([[E6[i][k] for i in range(36)] for k in range(6)])
print(f"contrast, 879 over 3x+y+1 mod 6 with Z/2: dim Z^2 = {Z879}, dim B^2 = {B879}, dim H^2 = {Z879-B879} (nonzero: the method could and did work there)")
