"""Tao's conjecture (Lean Zulip, Austin pairs, 2024-11-29, message 485148288): the only nontrivial one-generated 1518-magma
satisfying 47, 614, 817 and 3862 is the cyclic shift x◇y = y+1 on Z/3. Check it against Mace4's complete-up-to-isomorphism
enumerations (lnh on) at sizes 2..7: stream the models, keep the one-generated ones, canonicalize those, test the targets."""
import re, sys, time, itertools
S = sys.argv[1]
exec(open(__file__.replace("monogenic_1518.py", "adversary_size5.py")).read().split("PAIRS = {")[0])
def generated(T, g):
    seen = {g}; frontier = [g]
    while frontier:
        new = []
        for a in list(seen):
            for b in list(seen):
                c = T[a][b]
                if c not in seen: seen.add(c); new.append(c)
        frontier = new
    return len(seen)
def monogenic(T): return any(generated(T, g) == len(T) for g in range(len(T)))
def stream(path, n):
    buf = []; inside = False
    with open(path) as fh:
        for line in fh:
            if "function(*(_,_), [" in line: inside = True; buf = []; continue
            if inside:
                buf.extend(map(int, re.findall(r"\d+", line)))
                if "])" in line:
                    inside = False; assert len(buf) == n*n; yield [buf[i*n:(i+1)*n] for i in range(n)]
t0 = time.time(); targets = [47, 614, 817, 3862]
for n in range(2, 8):
    path = f"{S}/m4/e1518_{n}_nolnh.out" if n <= 4 else f"{S}/m4/e1518_{n}.out"
    total = 0; mono = {}
    for T in stream(path, n):
        total += 1
        if monogenic(T): mono.setdefault(canonical(T), T)
    line = f"size {n}: {total} Mace4 models, one-generated classes: {len(mono)}"
    for T in mono.values():
        assert holds_table(T, 1518)
        line += f"\n    {T}  satisfies {[t for t in targets if holds_table(T, t)]}"
    print(line + f"   [{time.time()-t0:.0f}s]", flush=True)
