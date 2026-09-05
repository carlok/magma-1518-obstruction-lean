"""Do ETP's Refutation930 (Fin 12, 879 !=> 4065) and Refutation939 (Fin 15, 1518 !=> 47,614,817,3862) admit a relabelling
as a constant-coefficient abelian extension  (x,s)◇(y,t) = (x◇y, αs + βt + c(x,y))  of one of their quotients?
For each congruence with equal class sizes m and each abelian group M of order m (as Z/m or a product of cyclic groups),
each α, β in End(M) is tried; the labelling of one class is enumerated and the others are forced by propagation.
A hit would refute Q1 directly. Standard library only."""
import itertools, re, sys
S = sys.argv[1]

def table(n):
    t = open(f"{S}/etp/Refutation{n}.lean").read(); return eval(re.search(r"\[\[.*?\]\]", t, re.S).group(0))

def congruences(T):
    N = len(T)
    def closure(pairs):
        parent = list(range(N))
        def find(a):
            while parent[a] != a: parent[a] = parent[parent[a]]; a = parent[a]
            return a
        def union(a, b):
            a, b = find(a), find(b)
            if a != b: parent[a] = b; return True
            return False
        for a, b in pairs: union(a, b)
        changed = True
        while changed:
            changed = False
            for a in range(N):
                for b in range(a+1, N):
                    if find(a) == find(b):
                        for c in range(N):
                            changed |= union(T[a][c], T[b][c]); changed |= union(T[c][a], T[c][b])
        roots = [find(a) for a in range(N)]; first = {}
        return tuple(first.setdefault(r, i) for i, r in enumerate(roots))   # canonical: class labelled by its first element
    congs = {closure([(a, b)]) for a in range(N) for b in range(a+1, N)}
    frontier = list(congs)
    while frontier:
        c = frontier.pop()
        for d in list(congs):
            j = closure([(i, k) for i in range(N) for k in range(N) if c[i] == c[k] or d[i] == d[k]])
            if j not in congs: congs.add(j); frontier.append(j)
    return [c for c in congs if 1 < len(set(c)) < N]

# abelian groups of order m as products of cyclic groups; elements are tuples
def groups(m):
    out = {2: [(2,)], 3: [(3,)], 4: [(4,), (2, 2)], 5: [(5,)], 6: [(6,)]}
    return out.get(m, [])
class Ab:
    def __init__(self, mods): self.mods = mods; self.elems = list(itertools.product(*[range(k) for k in mods]))
    def add(self, a, b): return tuple((x+y) % k for x, y, k in zip(a, b, self.mods))
    def sub(self, a, b): return tuple((x-y) % k for x, y, k in zip(a, b, self.mods))
    def endos(self):
        """All endomorphisms, as maps on generators e_i -> image; an assignment is a hom iff order(e_i) kills the image."""
        r = len(self.mods); gens = [tuple(1 if j == i else 0 for j in range(r)) for i in range(r)]
        def mul(n, a): return tuple((n*x) % k for x, k in zip(a, self.mods))
        for images in itertools.product(self.elems, repeat=r):
            if all(mul(self.mods[i], images[i]) == tuple([0]*r) for i in range(r)):
                phi = {}
                for coeffs in itertools.product(*[range(k) for k in self.mods]):
                    v = tuple([0]*r)
                    for i, c in enumerate(coeffs): v = self.add(v, mul(c, images[i]))
                    phi[coeffs] = v
                yield phi

def constant_coefficient_extension(T, cong):
    """Search labellings block -> M and constant alpha, beta with L(a◇b) = alpha L(a) + beta L(b) + c(block a, block b).
    Block 0's labelling is enumerated; further blocks are forced by propagation where possible and enumerated otherwise."""
    N = len(T); classes = {}
    for i, r in enumerate(cong): classes.setdefault(r, []).append(i)
    blocks = list(classes.values()); m = len(blocks[0]); nb = len(blocks)
    if any(len(b) != m for b in blocks): return None
    cls = {e: bi for bi, b in enumerate(blocks) for e in b}
    Q = [[cls[T[blocks[a][0]][blocks[b][0]]] for b in range(nb)] for a in range(nb)]
    hits = []
    for mods in groups(m):
        G = Ab(mods); endos = list(G.endos()); zero = tuple([0]*len(mods))
        def propagate(L, labelled, alpha, beta):
            L = dict(L); labelled = set(labelled); c = {}; changed = True
            while changed:
                changed = False
                for x in range(nb):
                    for y in range(nb):
                        if x not in labelled or y not in labelled: continue
                        z = Q[x][y]; a0, b0 = blocks[x][0], blocks[y][0]
                        if z not in labelled:
                            newL = {}
                            for a in blocks[x]:
                                for b in blocks[y]:
                                    v = G.add(alpha[L[a]], beta[L[b]]); e = T[a][b]
                                    if e in newL and newL[e] != v: return None
                                    newL[e] = v
                            if len(set(newL.values())) != m: return None
                            L.update(newL); labelled.add(z); c[(x, y)] = zero; changed = True
                        else:
                            cxy = G.sub(L[T[a0][b0]], G.add(alpha[L[a0]], beta[L[b0]]))
                            if (x, y) in c and c[(x, y)] != cxy: return None
                            for a in blocks[x]:
                                for b in blocks[y]:
                                    if L[T[a][b]] != G.add(G.add(alpha[L[a]], beta[L[b]]), cxy): return None
                            c[(x, y)] = cxy
            return L, labelled
        def search(L, labelled, alpha, beta):
            r = propagate(L, labelled, alpha, beta)
            if r is None: return False
            L, labelled = r
            if len(labelled) == nb: return True
            z = min(set(range(nb)) - labelled)
            for lab in itertools.permutations(G.elems):
                L2 = dict(L); L2.update({e: v for e, v in zip(blocks[z], lab)})
                if search(L2, labelled | {z}, alpha, beta): return True
            return False
        for alpha in endos:
            for beta in endos:
                for lab0 in itertools.permutations(G.elems):
                    if search({e: v for e, v in zip(blocks[0], lab0)}, {0}, alpha, beta):
                        hits.append((mods, alpha, beta)); return Q, m, hits
    return Q, m, hits

def report(name, T, h):
    congs = congruences(T)
    print(f"{name} (carrier {len(T)}, hypothesis E{h}): {len(congs)} nontrivial congruences")
    for cong in sorted(congs, key=lambda c: (len(set(c)), c)):
        r = constant_coefficient_extension(T, cong)
        if r is None: print("  unequal class sizes, skipped"); continue
        Q, m, hits = r
        print(f"  quotient size {len(Q)}, fibre size {m}: " + (f"CONSTANT-COEFFICIENT EXTENSION FOUND, fibre group {hits[0][0]}" if hits else
              f"no relabelling as a constant-coefficient abelian extension (all groups of order {m}, all alpha, beta, all labellings)"))

# Positive control first: the model built from Tao's formula (affine_bases.py writes it) must show its structure.
import os
if os.path.exists(f"{S}/tao12.json"):
    T12 = eval(open(f"{S}/tao12.json").read())
    report("POSITIVE CONTROL: constructed 12-element model from Tao's formula", T12, 879)
    assert any(constant_coefficient_extension(T12, c) and constant_coefficient_extension(T12, c)[2] for c in congruences(T12)), "positive control failed"
    print("positive control passed\n")
else:
    print("positive control skipped: run affine_bases.py first to create tao12.json\n")
for n, h in ((930, 879), (939, 1518)):
    report(f"ETP Refutation{n}", table(n), h)
