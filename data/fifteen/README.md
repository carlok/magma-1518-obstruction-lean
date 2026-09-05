Results of the base-dependent-extension classification (README, Theorems F and F′; `paper/l2_note.pdf`, Section 7).

- `family_Qi.json`: the eight orbit representatives lifted to Q(i) (`scripts/basedep_family.py`); entries as strings like `1/2-1/2i`.
- `direct_out_*.txt`: pairs / refuting pairs per prime, 5 ≤ p ≤ 61 (`scripts/basedep_direct.py`).
- `groebner2_out.txt`, `groebner_modp_out.txt`: Gröbner bases over Q and over F_p, 5 ≤ p ≤ 257 (sympy 1.14).
- `family_vs_fifteen_out.txt`, `family_more_fibres_out.txt`: isomorphism with Le Floch's 15-element models 5 and 6; brute force over F_9 and Z/25.

Not included: Le Floch's file `1518-anti-47-models-size-15.jsonl` (the six 15-element countermodels computed by Jose Brox; Lean Zulip, stream Equational, topic "Shrinking the size-232 magma for law 1518 to size 15", 2025-10-29, message 547744137). `scripts/family_vs_fifteen.py` expects it here.
