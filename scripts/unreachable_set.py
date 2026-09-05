"""Which finite non-implications 1518 !=> E' can a constant-coefficient extension of the Z/3 shift never witness?
By H^2 = 0, such an extension satisfies every law true in the shift and in all finite linear 1518-magmas (the latter
decided in the ring R at once). Compare with the ETP finite implication graph (finite_graph.json, RLE 4694 x 4694;
status 3/7 = true, 2/6 = false, 8 = unknown). Controls: every finitely implied E' must pass both checks."""
import json, re, itertools, sys
S = sys.argv[1]
exec(open(__file__.replace("unreachable_set.py", "l2_symbolic.py")).read().split("HYP = 1518; TARGETS")[0])
N = 4694
arr = json.load(open(f"{S}/etpgraph/finite_graph.json"))["rle_encoded_array"]
flat = []
for v, run in zip(arr[0::2], arr[1::2]): flat.extend([v]*run)
assert len(flat) == N*N, len(flat)
row = flat[(1518-1)*N:(1518)*N]            # status of 1518 => E' for E' = 1..4694 (finite)
status = {n+1: row[n] for n in range(N)}
def shift_satisfies(n):
    vs, L, Rr = law(n)
    def ev(t, env): return env[t] if isinstance(t, str) else base[ev(t[0], env)][ev(t[1], env)]
    return all(ev(L, dict(zip(vs, v))) == ev(Rr, dict(zip(vs, v))) for v in itertools.product(range(3), repeat=len(vs)))
true_ = [n for n in status if status[n] in (3, 7)]; false_ = [n for n in status if status[n] in (2, 6)]; unk = [n for n in status if status[n] == 8]
print(f"finite graph row 1518: implied {len(true_)}, not implied {len(false_)}, unknown {len(unk)}")
bad = [n for n in true_ if not (shift_satisfies(n) and linear_satisfies(n))]
print(f"control: finitely implied laws failing the shift or the R-linear check: {len(bad)} {bad[:10]}")
unreach = sorted(n for n in false_ if shift_satisfies(n) and linear_satisfies(n))
by_shift_only = sorted(n for n in false_ if not shift_satisfies(n))
by_linear_only = sorted(n for n in false_ if shift_satisfies(n) and not linear_satisfies(n))
print(f"\nnon-implications 1518 !=>_fin E': {len(false_)}")
print(f"  refuted by the shift itself:                 {len(by_shift_only)}")
print(f"  shift ok, refuted by some finite linear 1518-magma: {len(by_linear_only)}  {by_linear_only[:20]}")
print(f"  UNREACHABLE by any constant-coefficient extension of the shift (shift and all finite linear fibres satisfy E'): {len(unreach)}")
nvars = {n: len(law(n)[0]) for n in unreach}
print("  by number of variables:", {k: sum(1 for n in unreach if nvars[n] == k) for k in sorted(set(nvars.values()))})
print("  list:", unreach)
print("  one-variable members:", [n for n in unreach if nvars[n] == 1])
json.dump({"unreachable": unreach, "refuted_by_shift": by_shift_only, "refuted_by_linear": by_linear_only}, open(f"{S}/unreachable_1518.json", "w"))
# sanity: the four targets are in the unreachable list
print("  contains 47, 614, 817, 3862:", all(t in unreach for t in (47, 614, 817, 3862)))
