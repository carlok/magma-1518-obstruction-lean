# L2: constant-coefficient abelian extensions of the Z/3 shift cannot refute 1518 ⇒ 47, 614, 817, 3862

Research note, 4 September 2026. Status: **proved by a verified computation and a short written argument; not formally verified in Lean beyond its algebraic core; originality unresolved.** Companion to the lab's audit (not published), which records how the question was selected and what was searched.

## 1. Statement

Notation follows the Equational Theories Project (ETP) at commit `88088faa`: law 1518 is `x = (y ◇ y) ◇ (x ◇ (y ◇ x))`, and the four targets are the one-variable laws 47 `x = x ◇ (x ◇ (x ◇ x))`, 614 `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`, 817 `x = x ◇ ((x ◇ x) ◇ (x ◇ x))`, 3862 `x ◇ x = (x ◇ (x ◇ x)) ◇ x`. All four are consequences of 1518 in finite magmas of fewer than 15 elements and are refuted by a 15-element magma (ETP, `Refutation939`).

An **extension** of a magma `G` by an abelian group `M` with endomorphisms `α, β ∈ End(M)` and a function `f : G × G → M` is the magma on `G × M` with `(x,s) ◇ (y,t) = (x ◇ y, αs + βt + f(x,y))` (ETP blueprint, chapter "Magma cohomology"; the coefficients are constant, not depending on `x, y`). If `G` and the linear magma `(M, αs + βt)` both satisfy a law `E`, the extension satisfies `E` iff `f` is an `E`-cocycle, a linear condition on `f`.

**Theorem L2.** Let `G` be the three-element magma `x ◇ y = y + 1` on Z/3, or the one-element magma. Let `M` be a **finite** abelian group and `α, β ∈ End(M)` such that `(M, αs + βt)` satisfies 1518. Then every 1518-cocycle `f : G × G → M` is a 47-cocycle, a 614-cocycle, an 817-cocycle and a 3862-cocycle. Equivalently, no extension of `G` by `(M, α, β, f)` refutes `1518 ⇒ E'` for `E' ∈ {47, 614, 817, 3862}`.

**Corollary (weak form, census-based).** Let `H` be any finite 1518-magma and `H × M` an extension as above that refutes `1518 ⇒ E'` for one of the four targets. Then `H` contains a one-generated submagma with at least 9 elements.

**Theorem (full obstruction, 2026-09-05; see `paper/L1_NOTE.md`).** The hypothesis on the base is unnecessary: if `H` is a finite 1518-magma and a constant-coefficient extension `H ×_f M` by a finite 1518-fibre violates one of 47, 614, 817, 3862, then `H` already violates it. Proof: one-generated (1518 + 3862)-magmas are trivial or the shift (core Lean, no axioms for the table), the four targets are equivalent in finite 1518-magmas (Vampire), and over the shift every 1518-cocycle is a coboundary (Theorem L2⁺). (Dually, the same holds for 2054 ⇒ 255, 2847, 2644, 3456 with the dual shift `x ◇ y = x + 1`.)

The corollary uses two external inputs: Tao's reduction to one-generated bases (Lean Zulip, "Austin pairs", 2024-11-29, message 485146097) and a census, computed for this note, showing that the only one-generated 1518-magmas with at most 8 elements are the trivial magma and the Z/3 shift.

## 2. Proof of Theorem L2

**Step 1, the finite-fibre ring.** Write the linear magma as `s ◇ t = αs + βt`. Expanding 1518 with the blueprint's coefficient polynomials gives, as identities in `End(M)`,

```
βα + β³ = 1            (coefficient of x)
α² + αβ + β²α = 0      (coefficient of y)
```

From the first, `β(α + β²) = 1`, so `β` is surjective; `M` is finite, so `β` is bijective and `α + β² = β⁻¹`, i.e. `α = β⁻¹ − β²`. Hence `α` is a polynomial in `β, β⁻¹` and commutes with `β`. Substituting into the second identity and multiplying by `β²` gives `β⁵ + β³ − β² − 1 = 0`, i.e. `(β² + 1)(β³ − 1) = 0`. Conversely these two facts imply both identities. Therefore `M` is a module over

```
R = Z[b] / (b⁵ + b³ − b² − 1),    with  a := b⁴ − b  (= b⁻¹ − b²,  since b⁻¹ = b⁴ + b² − b in R)
```

via `b ↦ β`, and then `a ↦ α`. `R` is commutative and free of rank 5 over Z. Every `R`-module is such a fibre. (Nielsen's classification of 2024-11-29 is the special case of an integral domain: `α = 0, β³ = 1` or `β = 1 − α, α² − 2α + 2 = 0`.)

**Step 2, the cocycle conditions over R.** Over the base `G` (three elements, or one), the fibre component of any word in the extension is `Σ_i P_{w,i}(a,b) s_i + Σ_{subterms} Q(a,b) f(·,·)`. The linear magma over `R` satisfies 1518 and each of the four targets (checked: the coefficient polynomials of both sides agree in `R`), so the `s_i` terms cancel and the `E`-cocycle condition is a matrix `D_E` with entries in `R`, acting on the 9 (or 1) unknowns `f(x,y)`. For each `R`-module `M`, `Z²_E(G,M) = ker(D_E on M^9)`.

**Step 3, containment by certificate.** For each target `E'` there is a matrix `C_{E'}` over `R` with `C_{E'} · D_1518 = D_{E'}` entrywise in `R`. Hence for every `R`-module `M` and every `f ∈ M^9`, `D_1518 f = 0` implies `D_{E'} f = C_{E'} D_1518 f = 0`. That is the theorem. The certificates are 3 × 9 matrices over `R` (15 to 18 nonzero entries); for the one-element base they are 1 × 1. They are listed in `certificates/l2_certificate_3.json` and `certificates/l2_certificate_1.json`.

**Remark.** Step 3 was found, not guessed: over the rank-5 ring the `R`-span of the nine 1518 rows is a Z-lattice of rank 35 in Z⁴⁵, and membership of the target rows was decided by integer row reduction. As a by-product, `Z²_1518(G, M)` has `R`-rank 2 for the Z/3 shift, and all of it consists of target cocycles. The certificate direction is the only one used: containment for all modules is also *equivalent* to the lattice containment (take `M = R⁹ / rowspan(D_1518)` and a finite quotient), so a failure would have produced an explicit finite countermodel.

## 2b. The stronger statement: $H^2$ vanishes over the shift

Theorem L2 turns out to be a corollary of something cleaner. Let `E : M³ → M⁹` be the coboundary map `g ↦ (g(x ◇ y) − αg(x) − βg(y))_{x,y}`. Over `R` there are matrices `P` (3 × 9, two nonzero entries) and `Q` (9 × 9) with

```
E · P + Q · D_1518 = I_9      in R
```

(`certificates/h2_certificate.json`, re-verified by multiplication in `R`, kernel-checked in `lean/H2Cert.lean`). Hence for every `R`-module `M` and every 1518-cocycle `f` (so `D_1518 f = 0`), `f = E(Pf)` is a coboundary: `H²_1518(G, M) = 0` for the Z/3 shift `G` and every finite 1518 fibre `M`.

**Consequence (L2⁺).** Every constant-coefficient extension of the Z/3 shift by a finite 1518 linear magma is isomorphic, via `(x,s) ↦ (x, s + g(x))`, to the direct product. It therefore satisfies every law that both the shift and the fibre satisfy, which includes 47, 614, 817, 3862 and any other law true in the shift and in all finite linear 1518-magmas. Theorem L2 is the special case of four laws.

Checks: at every root of `b⁵ + b³ − b² − 1` in `F_p`, `p ≤ 47`, `dim Z² = dim B² = 2`; over `Z/4` with `β = 1` there are 16 cocycles and 16 coboundaries. The one-element base is different: there `H²` can be nonzero (e.g. `M = Z/3`, `β = 1`, `α = 0`, where every constant is a cocycle and no nonzero constant a coboundary), yet the containment of Theorem L2 still holds by its own certificate. For contrast, 879 over the affine base `3x + y + 1 mod 6` with fibre `Z/2` has `dim Z² = 7`, `dim B² = 5`, `dim H² = 2`: that is the room the method used in November 2024. Script: `scripts/h2_vanishing.py`.

## 2c. Conservative second pass (2026-09-04)

- **Statements re-derived from scratch.** A second implementation with noncommutative coefficients (words in `α, β`, no commutativity assumed until the finite-fibre reduction) reproduces the two 1518 identities `βα + β³ = 1`, `α² + αβ + β²α = 0` and every stored cocycle row for 1518, 47, 614, 817, 3862 exactly (`rederive_rows.py`).
- **Finiteness is used only to make β injective.** The theorems hold for any abelian fibre on which β is injective; finite M is the case that matters.
- **The wider set, exactly.** From the ETP finite graph (fetched 2026-09-04): 1518 has 5 finite implications and 4689 finite non-implications. Of the non-implications, 4347 are refuted by the shift itself, 329 by some finite linear 1518-magma alone, and exactly **13** are unreachable by every constant-coefficient extension of the shift: `47, 65, 375, 614, 632, 679, 817, 872, 879, 1491, 3862, 3915, 4118` (four one-variable laws, nine two-variable laws). Control: all 5 finite implications pass both checks (`unreachable_set.py`).
- **The census, independently and in Lean.** z3 with a reachability encoding: a one-generated 1518-magma exists at size 3 (the shift) and at no other size from 2 to 8; labelled counts 1, 6, 54, 1500 at sizes 2 to 5 agree with Mace4's complete enumeration (`z3_census.py`). Sizes 2 to 8 are Lean theorems (`lean/census/Census1518_n.lean`, generated by `gen_census_lean.py`): bitvector encoding, `bv_decide`, per-theorem native-evaluation axiom; size 3 is proved to be exactly the two labelled shifts. Each file carries kernel-`decide` encoding controls (a real 1518 table satisfies the encoded law hypotheses; at size 3 the shift satisfies the reachability chain), added after a first size-8 file turned out vacuous through 3-bit wraparound of `8#3`. `CensusBridge.lean` proves size 2 for functions on `Fin 2` by kernel `decide` alone; the same at size 3 was stopped after 2h45m.
- **The ETP witness is an extension of the shift with base-dependent coefficients.** `Refutation939` (15 elements) has a unique nontrivial congruence, quotient isomorphic to the Z/3 shift, classes of size 5; labelling each class by Z/5 (unique up to affine relabelling) writes it as `(x,s) ◇ (y,t) = (y+1, α_{xy}s + β_{xy}t + c_{xy})` with `α_{xy} ∈ {1,2,4}`, `β_{xy} ∈ {1,2,3,4}`. So the minimal countermodel lives in the blueprint's general form over exactly the base where constant coefficients give nothing (`witness939_varying.py`).

## 2d. L1 settled (2026-09-05)

See `paper/L1_NOTE.md`: the classification of one-generated 1518-magmas satisfying 3862 is a theorem (nine equational proofs by Vampire plus the Lean census), with no finiteness assumption. With it, the corollary above is unconditional for 3862: no constant-coefficient abelian extension of any 1518-magma refutes 1518 ⇒ 3862 unless the base already does.

## 3. Verification status

| Layer | Method | Status |
| --- | --- | --- |
| Certificate identities `C · D_1518 = D_{E'}` in `R` | Lean 4.33.1 kernel, `decide` on integer coefficient lists, `lean/L2Cert.lean` | checked; axioms `[propext]` only |
| Same identities | Python re-multiplication in `R`, `l2_symbolic.py` | checked |
| Rows `D_E` are the cocycle conditions; ring `R` is the finite-fibre ring | Written argument above; rows generated by `l2_symbolic.py` from the ETP law text | not formalized |
| Consistency with numeric method | 39 specializations `β = r ∈ F_p`, `m(r) = 0`, `p ≤ 47`, against the independent numeric containment test used for the search rounds | all blocked, dimensions agree |
| Control | Law 359, which 1518 implies universally, is contained with a certificate | passes |
| Census for the corollary | Mace4 2009-11A, sizes 2 to 4 complete labelled enumeration (audited against plain enumeration at sizes 2, 3), sizes 5 to 7 complete up to isomorphism (least-number heuristic, audited at size 4), `monogenic_1518.py` | one-generated classes: size 3: 1 (the shift); sizes 4 to 7: 0 |

A full Lean proof of Theorem L2 would need: the definition of extensions, the derivation of the cocycle rows from the law terms, and Step 1. None of that is done. The plan's formal gate is therefore **not** passed; the plan's counterexample and search-result gates do not apply, since this is a positive statement.

## 4. Prior art and originality

- The method, the cocycle formalism and the statement `H²_E ⊆ H²_{E'}` when `E ⇒ E'` are the ETP's (blueprint chapter "Magma cohomology"; paper arXiv:2512.07087 §5).
- The reduction to one-generated bases and the observation that idempotent linear bases are useless: Tao, 2024-11-29 (message 485146097).
- The classification of linear and affine 1518-models over an integral domain: Nielsen, 2024-11-29 (message 485154828). Step 1 above is the same computation over an arbitrary finite abelian group, where invertibility of `β` replaces the integral-domain assumption.
- That the Z/3 shift is the only nontrivial one-generated 1518-magma satisfying the four targets: conjectured by Tao, 2024-11-29 (message 485148288); verified here through size 7.
- Failed attempts to refute the 1518 implications cohomologically over the Z/3 shift with product fibres: Bolan, 2024-11-29 (message 485027669); Tao: "perhaps sometimes the linear algebra just doesn't work out" (485133886).
- The only comparable no-go theorem in the corpus: blueprint Lemma "No counterexamples via linear extension" for 677 ⇒ 255, proved by hand and, per Tao (June 2025), surviving fibres that vary with the base point.

No statement of Theorem L2, as a claim or a theorem, was found in: the pinned ETP repository (blueprint, paper, commentary, Lean sources, GitHub code search), the Lean Zulip Equational stream (twenty searches, operator-run), the SAIR Foundation Zulip (full history of all channels, zero hits), Parsimagma, the Omega Institute solver repository, arXiv and web search. **Originality: unresolved.** The searchable venues are exhausted; a private communication or an unindexed file could still contain it. The result explains, rather than merely records, why the November 2024 attempts failed, which is the kind of contribution the plan calls an obstruction. Its scope is narrow: one base (plus the trivial one), constant coefficients, finite fibres.

## 5. What this is not

- Not a proof that 1518 ⇒ E' has no cohomological refutation at all: bases with a one-generated submagma of 8 or more elements, coefficients varying with the base pair (`α_{x,y}, β_{x,y}`), and iterated extensions are all outside the theorem.
- Not Lean-verified as a theorem; only its algebraic core is kernel-checked.
- Not a Palomar submission or a registration; no Comparator or NanoDa replay has been run, and no external review has occurred.
- Not new mathematics of independent interest beyond the ETP context.

## 6. Reproduction

```
sh scripts/fetch_inputs.sh audit-data
sh scripts/run_mace4.sh audit-data
python3 scripts/l2_symbolic.py audit-data
python3 scripts/l2_symbolic.py audit-data "one-element base"
python3 scripts/monogenic_1518.py audit-data
lean +v4.33.1 -M 4096 scripts/L2Cert.lean
```

Outputs as run on 2026-09-04 are in `OUTPUT.md`. All scripts are standard-library Python, independent of `algebra_lab`, and do not touch any campaign's frozen code hashes.

## 7. Suggested next steps, in order

1. One round of outside eyes on Step 1 and the row derivation, for example a Zulip post in the Equational stream quoting the theorem, the ring, and one certificate, and asking whether it is already known. Posting is an operator decision.
2. Extend the census to size 8, where the corollary would start to bite harder; each further size is roughly 200 times the previous Mace4 output.
3. Attempt Lemma L1 (the classification of one-generated 1518-magmas satisfying the four targets) as a structural statement rather than a census.
4. Only after 1 to 3: a Lean formalization of L2 with the extension defined generically, as the first candidate for a Palomar-shaped package.
