# L1: one-generated 1518-magmas satisfying 3862 are trivial or the Z/3 shift

Research note, 5 September 2026. Status: **proved and Lean-checked.** The nine equational proofs found by Vampire 5.1.0 were transcribed into core Lean 4.33.1 (`lean/OneGenerated1518.lean`): the multiplication table of `{x, S x, S S x}` and the closure of words carry **no axioms at all**; the one-or-three-elements statement uses only `propext`, `Classical.choice`, `Quot.sound`. No finiteness, no solver, no census. Companion to `paper/L2_NOTE.md` and the lab's audit (not published). Everything in `atp/` and `lean/census/`.

## 1. Statement

Write `S(x) = x ◇ x`. Law 1518 is `x = (y ◇ y) ◇ (x ◇ (y ◇ x))`; law 3862 is `x ◇ x = (x ◇ (x ◇ x)) ◇ x`.

**Theorem L1 (table).** In every magma satisfying 1518 and 3862, for every `x` and all `u, v ∈ T = {x, S(x), S(S(x))}`: `u ◇ v = S(v)`, and `S(S(S(x))) = x`. So `T` is closed under `◇` and carries the multiplication table of the cyclic shift.

**Corollary L1′.** In every magma satisfying 1518 and 3862, every one-generated submagma has at most 3 elements. Every one-generated magma satisfying 1518 and 3862 is, up to isomorphism, the trivial magma or the cyclic shift `x ◇ y = y + 1` on Z/3. (Lean: `one_or_three` shows `T` has one element or three distinct ones; `table` gives the shift on `T`. The census files are now corroboration only.)

This is Tao's conjecture of 2024-11-29 (Lean Zulip, "Austin pairs", message 485148288), in a stronger form: no finiteness, and only one of the four target laws is needed. It is *not* true without a target: the ETP's 15-element table `Refutation939` is a one-generated 1518-magma (checked: `<g>` has 15 elements for 12 of its 15 generators), and it violates 3862.

## 2. Proof

Vampire 5.1.0 in CASC mode proves each of the nine closure statements

```
∀x.  u ◇ v = x  ∨  u ◇ v = S(x)  ∨  u ◇ v = S(S(x))        for u, v ∈ {x, S(x), S(S(x))}
```

from the two equational axioms alone, in milliseconds; the nine statements conjoined are proved in one run (`atp/min_e3862.p`). Proof objects with 9 to 42 lines are in `atp/closure_*.proof` (those were produced with the four targets and the left-quasigroup axioms present; the minimisation runs show 1518 + 3862 suffice). Hypothesis minimisation, 60 s per run, all nine statements at once:

| Extra axioms beyond 1518 | Result |
| --- | --- |
| 3862 | Theorem |
| 47 + 3862, 614 + 3862, 817 + 3862, all four | Theorem |
| 47 alone, 614 alone, 817 alone | Timeout (with or without left-quasigroup axioms) |
| 47, 614 or 817 alone **plus** left injectivity | Theorem |
| none of the targets (control) | Timeout |

So in finite 1518-magmas, where left multiplications are injective (Tao, 2024-11-24), any one of the four targets suffices; in arbitrary magmas 3862 suffices.

The corollary follows by induction on words: every word in `x` lies in `{x, S(x), S(S(x))}`, so `|<x>| ≤ 3`; a one-generated magma of size 1 is trivial, none of size 2 satisfies 1518, and the only one-generated 1518-magmas of size 3 are the two labelled shifts.

## 3. Consequences

**The obstruction theorem becomes unconditional for 3862.** Combining with `paper/L2_NOTE.md` (every constant-coefficient 1518-extension of the shift by a finite fibre is a direct product):

> Let `H` be any 1518-magma satisfying 3862, `M` a finite abelian group with `α, β` making `αs + βt` a 1518-magma, and `f` a 1518-cocycle on `H`. Then `H ×_f M` satisfies 47, 614, 817 and 3862.

Proof: a violation at `(x, s)` lives in the sub-extension over `<x>`, which is trivial or the shift by L1′, and over those bases every 1518-cocycle is a coboundary (or, for the trivial base, a target cocycle), so the sub-extension satisfies the targets. Hence constant-coefficient cohomology can never refute `1518 ⇒ 3862` from any base: if the extension violates 3862, the base already did.

**All four targets, finite bases.** Vampire also proves (`atp/imp_*.p`, 60 s each) that under 1518 plus left injectivity and left surjectivity, which hold in every finite 1518-magma, the four targets are pairwise equivalent (all twelve implications are theorems); without finiteness, 3862 implies each of 47, 614, 817, and 47 and 614 imply each other, while the remaining six directions time out. Therefore:

> **Theorem (full obstruction, finite bases).** Let `H` be a finite 1518-magma, `M` a finite abelian group with `α, β` making `αs + βt` a 1518-magma, and `f` a 1518-cocycle on `H`. If `H ×_f M` violates one of 47, 614, 817, 3862, then `H` already violates it.

Proof: if `H` satisfies the target `E'`, then being finite it satisfies 3862, so every `<x>` is trivial or the shift by L1′, and the sub-extension over `<x>` satisfies all four targets; a violation at `(x, s)` would live there. Constant-coefficient cohomology therefore never refutes any of these four implications from any finite base.

**What the "false" branch would have meant, for the record.** Had a one-generated 1518-magma satisfying the targets existed beyond the shift, say at size `n ≥ 9`, then: the census bound in the L2 corollary would have been sharp there; `H²_1518` over that base would have been the object to compute, and a cocycle outside a target's cocycle space would have given a new constant-coefficient cohomological countermodel of size `n·|M|`; the free one-generated (1518 + targets)-magma would have been larger than 3. The nine ATP proofs close this branch.

**Rigidity does not extend to other bases.** `H²_1518(G, M)` is nonzero for the right projection on 2 elements and for every 1518-base of sizes 4 and 5 (`h2_all_bases.py`), so non-split constant-coefficient 1518-extensions exist in abundance. By the theorem above they satisfy the four one-variable targets. They do reach two-variable laws: extensions of the 3-element base `[[0,1,2],[0,1,2],[1,0,2]]` by Z/2 refute `1518 ⇒ 632` and `1518 ⇒ 879` at carrier 6, both among the 13 laws unreachable over the shift. The seven laws 65, 375, 679, 872, 1491, 3915, 4118 remain unreached over bases of size ≤ 4.

## 4. Verification status

| Layer | Status |
| --- | --- |
| Nine closure equalities from 1518 + 3862 | Vampire 5.1.0, SZS Theorem, proofs saved; **replayed in core Lean** (`lean/OneGenerated1518.lean`), `table` and `words_in_T` with no axioms |
| Census sizes 2, 3 | Lean `bv_decide` (native axiom) and, at size 2, kernel `decide` |
| Closure on enumerated models | all 1518-magmas of size ≤ 6 (1 + 6 + 54 + 632 + 41,319 tables, all satisfy 3862): `{x, Sx, SSx}` closed for every `x`, max size of `<x>` is 3; on `Refutation939` (violates 3862) the closure fails at 60 of 135 products |
| Target equivalences under 1518 | Vampire: with left-quasigroup axioms all 12 implications among 47, 614, 817, 3862 are theorems; equationally 3862 ⇒ 47, 614, 817 and 47 ⇔ 614; the other six directions time out at 60 s |
| Control | without any target the closure conjecture is not proved (timeout); `Refutation939` is a one-generated counterexample without 3862 |

Lean anchoring done for the classification. Still prose: the finite-base equivalence of the four targets (Vampire, left-quasigroup axioms) and the full obstruction theorem's assembly with the H² theorem.

## 5. Prior art

Tao conjectured the classification (with all four targets, for finite magmas) on 2024-11-29 and noted the reduction of one-variable targets to one-generated bases. Nielsen classified the linear 1518-models the same day. No proof of the classification, and no statement with 3862 alone or without finiteness, was found in the ETP blueprint, paper, commentary, either Zulip or arXiv (searches of 2026-09-04). Originality unresolved; the proof is machine-found.
