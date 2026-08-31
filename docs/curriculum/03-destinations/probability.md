# Probability

> Layer 3 · destinations · decidability: `computable` · axeyum theory: LRA (exact rational, finite distributions) · status: `planned`

## What it is

**Finite probability** over exact rationals: a probability mass function
`p : Nat → Rat` on `[0, n)`, **expectation** of a random variable, **variance**
and **covariance**, the classical tail bounds — **Markov's** and
**Chebyshev's** inequalities — and a **limit theorem**, the weak law of large
numbers.

## Role in the tour

A destination resting on the rationals (the exact carrier every probability
below is stated and computed over) and counting (`Rat.sumRange`, the finite
aggregate every distribution/expectation/variance definition folds over). It
needs no measure theory or analysis: a finite distribution is a bounded
function plus a nonnegativity-and-total-mass condition, exactly the shape
`Rat.sumRange` and its monotonicity lemmas (`sumRange_le`, `sumRange_nonneg`)
were built for.

## Prerequisites

- [Rational Numbers](../01-number-systems/rationals.md) — probabilities, expectations, and variances are exact rationals.
- [Counting & Combinatorics](../02-structures/counting.md) — `Rat.sumRange` is the aggregate every definition here folds over.

## Unlocks

(Destination.)

## Testable in axeyum

Everything here is **bounded and computable**: a concrete finite distribution
(a table of rationals with `sumRange p n = 1`), its expectation, variance and
covariance are ordinary rational arithmetic, and Markov's/Chebyshev's
inequalities at a concrete distribution and threshold are exact-rational
comparisons — the same `QF_LRA` fragment the `Rational` family already
exercises. A validated foundational example pack already covers this ground:
`artifacts/examples/math/finite-probability-v0` (mass tables, conditional
expectation, kernels, Bayes rule, and checked bad-value evidence).

**Not yet built**: no `axeyum-scenarios::Family` variant exists for this node,
so `status = "planned"` rather than `covered` — `Status::Covered` in
`crates/axeyum-scenarios/src/mathtour.rs` means *has a self-checking exercise
family today*, and a test (`covered_nodes_have_a_family_realized_by_a_self_checking_scenario`)
enforces exactly that. The natural next self-checking exercise is a concrete
Markov/Chebyshev instance with the distribution and threshold as witnesses,
refuted-by-negation for a bad bound — the same shape `NumberTheory`'s
`bezout_identity`/`modular_inverse` exercises already use.

## Proved in the kernel — general, quantified, axiom-free

Measured 2026-08-31 against a freshly built `kernel_declaration_projection`
(release): **47 `Rat.*` declarations**, 8 `Definition`s and 39 `Theorem`s, all
axiom-free, forming a coherent Spivak-shaped spine:

| stage | kernel declarations |
|---|---|
| Distributions | `Rat.IsDistribution`, `Rat.prob_le_one`, `Rat.prob_complement`, `Rat.uniform` / `uniform_is_distribution`, `Rat.bernoulli` |
| Expectation | `Rat.expectation` with linearity (`expectation_add`, `expectation_smul`, `expectation_const`), monotonicity (`expectation_le`), positivity (`expectation_nonneg`), and `expectation_sumVars` |
| Indicators | `Rat.indicator` with `indicator_nonneg`, `indicator_le`, `expectation_indicator_le_one` |
| Variance & covariance | `Rat.variance` (`variance_eq`, `variance_nonneg`, `variance_smul`, `variance_add_of_uncorrelated`, `variance_sumVars`), `Rat.covariance` with **`covariance_sq_le_variance_mul`** — Cauchy-Schwarz for random variables — plus `covariance_comm`, `covariance_add_right`, `Rat.PairwiseUncorrelated` |
| Tail inequalities | `Rat.markov_inequality` / `markov_constructed`, `Rat.chebyshev_inequality`, `Rat.chebyshev_sampleMean_uncorrelated` |
| Limit theorem | **`Rat.weak_law_of_large_numbers`**, `Rat.bernoulli_law_of_large_numbers`, `Rat.bernoulli_harmonic_bound` |

Read these from the kernel, not from this table — it is a snapshot:

```sh
cargo run --release -p axeyum-lean-kernel --example kernel_declaration_projection \
  | awk -F'\t' '$1 == "rat" && $3 ~ /^Rat\.(IsDistribution|expectation|variance|covariance|markov|chebyshev|weak_law|bernoulli|uniform|indicator|prob_|sumVars|PairwiseUncorrelated)/'
```

Source: `crates/axeyum-lean-kernel/src/rat_prelude/probability.rs`.

## Still open

- **General measure theory / infinite probability spaces** — out of scope for
  this ladder entirely; `ℚ`-valued mass tables on `[0, n)` are the whole
  carrier this kernel has.
- **A self-checking `Family`** — the gap this node exists to name (see
  [ADR-1082](../../research/09-decisions/adr-1082-add-a-probability-node-the-kernel-had-the-spine-the-map-did-not.md)).
- **Chebyshev without the pairwise-uncorrelated hypothesis**, and a strong law
  — both natural next rungs once a scenario family exists to dispatch against.

## References

- Ross, *A First Course in Probability*.
- axeyum: `crates/axeyum-lean-kernel/src/rat_prelude/probability.rs`, `artifacts/examples/math/finite-probability-v0`.
