# A day of parallel mathematical development: what the theorem count does not say

**2026-08-25.** 3–5 lanes running continuously against the kernel. Production
moved **1,096 → 1,175 distinct theorems, every one axiom-free, 0 axiom-bearing**;
the trusted base did not move (30, all `axreal`, none reached by any shipped
route). Kernel `--lib` sweep 656 → 695 green.

This note records the part the count does not: **the structural findings, which
came from lanes FAILING to prove things and reporting why.**

## What landed

*Analysis.* The comparison test for series, the Cauchy→Converges bridge, the
**Archimedean squeeze bridge** (`le_of_forall_le_add_small`,
`equiv_zero_of_small`), multiplicative cancellation for `CReal.le` with
`inv_nonneg`, the quotient-form geometric tail bound, `geom_tail_within`, and
**`CReal.monotone_of_nonneg_deriv`** — the first theorem here that gets *global*
information from a *local* hypothesis, proved constructively with no Mean Value
Theorem (MVT rests on the extreme value theorem and fails constructively).

*Number theory.* CRT uniqueness over ℕ, `Nat.mod_eq_cancel`, the divisor sum
(`sumDivisors 28 → 56` by real reduction), the finite geometric sum,
`sumDivisors_two_pow`, the prime-power and two-family divisor classifications,
non-overlap between the families, `pow_lt_pow_of_lt` / `pow_injective` /
`pow_mul_prime_injective`, and **the irrationality of √2**.

*Elsewhere.* Exponentiation by squaring proved equal to its specification;
**Cantor's diagonal argument** in three parts; Ptolemy's identity over ℂ and its
squared metric consequence; `Rat.det3` with cofactor expansion and row scaling;
`Nat.prodRangeIf` and the predicate-scoped pigeonhole; `Nat.succ_pred_of_pos`
promoted from three copy-pasted proofs.

## Finding 1: three unrelated results block on one missing definition

`CReal.sqrt` does not exist, and it independently blocked the unsquared triangle
inequality (why `CPoint.distSq_triangle_sq_bound` is stated squared), the metric
form of Ptolemy, and `CPoint.incentre` — which needs side *lengths*, not their
squares. Three lanes on different targets converged on it.

Step A of its regularity proof landed, and the constant survived a genuine
refutation attempt: exact rational arithmetic at `dm = dn`, `dm = 1`, `dm ≫ dn`,
`dn ≫ dm`, margin `4/(dm·dn) + 1/dn²`, strictly positive throughout. The
constant is **uniform in `x`**, which is what makes `sqrt` total and free of a
`PosBound` — and a constructive setting could not have supplied one, since
`0 ≤ x` is undecidable.

## Finding 2: I recorded one primitive's status wrongly FOUR times

Seven lanes reported "no product over a predicate-defined subset". I then
recorded, in order: *missing* → *exists one carrier away* → *missing again* →
*half of it was avoidable*. Only the fourth is right.

- The second was a **name match with the hypotheses unread**:
  `Int.prodRange_permute` requires `MapsInto σ n`, a self-map of the *whole*
  range. A lane refuted it.
- Wilson's theorem does not need the scoped version because its modulus is
  **prime**, so every residue is a unit and the subset *is* the contiguous
  range. Euler's is composite. The two theorems look identical from outside and
  only one is a lemma away.
- The fourth correction: the **pigeonhole** half needed none of the machinery.
  Extend the map to a total one (`f' i := if p i then f i else i`) and hand it
  unmodified to the existing full-range lemma. No induction, no re-indexing, no
  swap. All seven lanes and all three of my revisions had assumed the reduction
  must go *inward*.

**An obstruction reported independently by seven lanes tells you where seven
lanes stopped, not that the path is blocked.** Concurring reports raise
confidence in the *symptom* and say nothing about the *diagnosis* — every one of
those lanes was standing in the same place looking the same direction, which is
exactly when agreement carries no information.

## Finding 3: the blind-evaluation partition was being spent by ordinary work

5 of 57 held-out nursery propositions were already proved in the kernel by hand
development unrelated to autogenesis.
`check-autogenesis-holdout-isolation.py` could not see any of them — it reads
`epistemic_status` and scans for textual references, and reported
`held_out=57|settled=0|verdict=PASS` throughout.

**This is not the vacuous-checker shape this repository keeps finding.** The gate
discriminates correctly on its own predicate. The predicate was the wrong one:
it guarded the ledger's record of itself rather than the information.

Repaired per ADR-0542 by an amendment (never a deletion) moving
`natural-binomial` to `development` as a whole family — 20 rows spent for 5
contaminated facts, which is correct, since the split key is family-based
precisely because a route for one member is evidence about its siblings.
`check-autogenesis-holdout-contamination.py` now reports without failing the
build; failing it would only pressure a lane into not proving a theorem it needs.

## Finding 4: "nothing is missing" is a prediction, not a measurement

A lane ended its `monotone_of_nonneg_deriv` plan with *"none of these needs
anything absent from the codebase"* — written by the lane best placed to know.
The next lane found the gap: the subdivision's endpoint `x_K` is only `Equiv` to
`y`, never syntactically equal, because the count identity is **proved, not
reduced**. Closing to `F x ≤ F y` therefore needs `F` to respect `Equiv`, which
is not free for an arbitrary `F`.

It closed that gap with a trick worth keeping: derive the congruence from
`HasDerivativeOn`'s **own spec at a degenerate accuracy `e := 0`**, because
`u ~ v` makes the piece width `Equiv` to zero outright rather than merely small.

Then a *fourth* lane found the same issue at the **other endpoint** — `x_0 :=
x + ofNat 0 · step` is also only `Equiv` to `x`, since `ofNat Nat.zero` is not
definitionally `CReal.zero`. The congruence is applied **twice, once per end**.

**In a Bishop setoid neither endpoint of a constructed subdivision is free, and
noticing one does not mean you have noticed the other.**

## The mechanism

Every brief told the lane to report precisely what blocked it and treated a
refutation as a complete result. **Five targets this coordinator named were
refuted, resized, or improved on by lanes doing exactly that** — including a
better domination for `e` (`1/n! ≤ 2·(1/2)^n`, true for every `n ≥ 0` with no
case split, against my `1/2^(n−1)` which needed the first terms split off), and
a cheaper route to IX.36's non-overlap lemma than the `euclid_lemma` one I
proposed.

A wrong brief with an escape hatch is recoverable. One that demands success is
not.
