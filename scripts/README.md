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
| `basedep_smart.py` | shared helpers for the scripts below (law parser, `betas()` enumeration of `b` in O(p⁵), table builder); its own main body is the slow first enumeration | |
| `basedep_direct.py` | all `(a, b)` pairs per prime, refuting count, `D`, squaring types: `basedep_direct.py data 5 13 17` | |
| `basedep_orbits.py` | orbit representatives under fibre rescaling (`b00 = b11 = 1`) | |
| `basedep_family.py` | CRT lift of the representatives to `Q(i)`; exact check of 1518 and of the target defects; writes `data/fifteen/family_Qi.json` | |
| `basedep_groebner2.py`, `basedep_groebner_modp.py` | Gröbner classification over `Q` and over `F_p` (run with a venv: `pip install sympy`) | sympy |
| `family_vs_fifteen.py` | isomorphism of the two refuting classes over `F₅` with Le Floch's models 5 and 6 (needs his `1518-anti-47-models-size-15.jsonl` in `data/fifteen/`, Zulip message 547744137, not redistributed) | |
| `family_more_fibres.py`, `family_squaring_morphism.py`, `squaring_orders.py` | brute force over `F₉` and `Z/25`; squaring as an endomorphism; squaring cycle types of Mace4 models | Mace4 for the last |
| `gen_family_lean.py` | generates `lean/FamilyF<p>.lean` from `data/fifteen/family_Qi.json` | |
