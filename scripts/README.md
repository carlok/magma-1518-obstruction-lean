Standard-library Python 3 unless noted. `data` is the directory created by `fetch_inputs.sh` (needs `gh`).

| Script | Purpose | Needs |
| --- | --- | --- |
| `fetch_inputs.sh` | pinned ETP law list and witness tables, Parsimagma's uncovered-pairs file | gh |
| `l2_symbolic.py` | finite-fibre ring, cocycle rows, containment certificates, numeric cross-check; second arg `"one-element base"` for the trivial base | |
| `h2_vanishing.py` | homotopy certificate `E·P + Q·D = I`; Z/4 brute force; 879 contrast | |
| `rederive_rows.py` | independent noncommutative re-derivation of every cocycle row | |
| `unreachable_set.py` | the 13 laws no constant-coefficient extension of the shift can reach (needs `data/etpgraph/finite_graph.json`, fetch from the ETP site) | |
| `witness_structure.py`, `witness939_varying.py` | congruences and (constant / base-dependent) extension structure of the ETP witnesses | |
| `h2_all_bases.py` | `H²` over every 1518-base of size ≤ 5 (needs Mace4 outputs in `data/m4`, see `run_mace4.sh`) | Mace4 |
| `adversary_size5.py`, `affine_bases.py`, `repro_refutation938.py` | the search rounds that preceded the theorems | Mace4 for the census inputs |
| `monogenic_1518.py`, `z3_census.py`, `run_mace4.sh`, `gen_census_lean.py` | the census by Mace4, by z3, and the generator of the Lean census files | Mace4, z3 |
