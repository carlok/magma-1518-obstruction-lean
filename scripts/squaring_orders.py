"""Squaring map S(x) = x*x in finite 1518-magmas: cycle types, bijectivity, order.  Reads Mace4 output files (interpretation
blocks) and JSON/JSONL tables.  Motivation: the refuting base-dependent extensions all have S of order 12 (cycle type
(12, ..., 12, 3)) while 1518+3862 forces S^3 = id (Theorem A); question: what orders does S have in finite 1518-magmas in general?
Usage: squaring_orders.py <file> [<file> ...]"""
import sys, re, json
def mace4_tables(path):
    txt = open(path).read()
    for m in re.finditer(r"interpretation\( (\d+), .*?function\(\*\(_,_\), \[(.*?)\]\)", txt, re.S):
        n = int(m.group(1)); vals = list(map(int, re.findall(r"\d+", m.group(2))))
        yield [vals[i*n:(i+1)*n] for i in range(n)]
def json_tables(path):
    if path.endswith(".jsonl"):
        for line in open(path):
            line = line.strip()
            if line:
                obj = json.loads(line); yield obj["table"] if isinstance(obj, dict) else obj
    else:
        obj = json.load(open(path))
        for T in (obj if isinstance(obj, list) and obj and isinstance(obj[0][0], list) else [obj]): yield T
def holds1518(T):
    n = len(T)
    return all(x == T[T[y][y]][T[x][T[y][x]]] for x in range(n) for y in range(n))
def cycle_type(f):
    n = len(f); seen = set(); cyc = []; bij = len(set(f)) == n
    for z in range(n):
        if z in seen: continue
        w = z; path = []
        while w not in seen: seen.add(w); path.append(w); w = f[w]
        if w in path: cyc.append(len(path) - path.index(w))   # cycle length (tail elements are not periodic)
        else: cyc.append(0)                                    # tail merging into an earlier orbit
    return tuple(sorted(cyc, reverse=True)), bij
from math import lcm
stats = {}
for path in sys.argv[1:]:
    tables = mace4_tables(path) if path.endswith(".out") else json_tables(path)
    for T in tables:
        assert holds1518(T), f"table in {path} does not satisfy 1518"
        n = len(T); sq = [T[x][x] for x in range(n)]; ct, bij = cycle_type(sq)
        key = (n, ct, bij); stats[key] = stats.get(key, 0) + 1
for (n, ct, bij), c in sorted(stats.items()):
    per = lcm(*[k for k in ct if k]) if bij else None
    print(f"size {n:3d}  models {c:5d}  bijective {str(bij):5s}  order {per}  cycle type {ct}")
