Vampire 5.1.0 inputs (TPTP fof) and proof objects.

- `eq_<u>_<v>.p`: from 1518 and 3862 alone, `u ◇ v ∈ {x, S x, S S x}` for `u, v ∈ {x, S x, S S x}`; `.proof` files are the refutations (`-p tptp`). All nine: SZS Theorem, milliseconds.
- `min_*.p`: all nine statements at once under various hypothesis sets (which targets, which finiteness axioms). 3862 alone suffices; 47/614/817 alone need `left_inj`.
- `imp_<A>_<B>_{0,2}.p`: does 1518 + A imply B, without (0) or with (2) the left-quasigroup axioms. With them all twelve implications among 47, 614, 817, 3862 are theorems; without, 3862 implies the other three and 47 ⇔ 614.
- `axioms.p`, `control_no_targets.p`: the full axiom set used first, and a control that must not be proved.

Run: `vampire --mode casc -t 60 <file>`.
