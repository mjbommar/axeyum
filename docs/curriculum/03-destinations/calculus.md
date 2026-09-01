# Calculus

> Layer 3 · destinations · decidability: `bounded` · axeyum theory: NRA · status: `lean-horizon`

> **2026-08-31 — `status: lean-horizon` is about the SCENARIO family, and a
> third route is not represented here at all.** Lane `cas-coverage-audit`.
> ADR-1075 already separates "carries no self-checking scenario family" from
> "the kernel node is small", and this node is the largest kernel node after
> `naturals`. There is a third axis neither of those measures:
> `crates/axeyum-cas` decides much of classical calculus **exactly** on the
> polynomial and rational fragment — ADR-0603 row 3 — including Taylor with
> Lagrange remainder (`taylor.rs`), the classical MVT (`mvt.rs`), IVT and EVT
> (`real_algebraic.rs`, `extremum.rs`), self-certifying integration
> (`lib.rs::integrate`), elementary integration by partial fractions and
> Horowitz–Ostrogradsky (`partial_fractions.rs`, `ratint.rs`), and exact limits
> of rational functions (`lib.rs::limit`).
>
> Nothing above is retracted — `lean-horizon` is accurate about what it
> measures. The audited chapter-by-chapter map is
> [`spivak.md`](../foundational-books/spivak.md)'s `C` column.

## What it is

The mathematics of change and accumulation: **limits**, **continuity**,
**derivatives** (instantaneous rates), **integrals** (accumulated area), and
**series**. Built on the real numbers and the limit concept.

## Role in the tour

The analytic destination, and the one most dependent on genuinely infinitary
machinery (ε–δ limits). It carries no self-checking scenario family, which is
what `status = "lean-horizon"` records — and it is simultaneously the *largest*
kernel node after `naturals`, at 349 axiom-free declarations. Those are two
different axes and the file states both (ADR-1075).

## Prerequisites

- [Real Numbers](../01-number-systems/reals.md)
- [Sequences & Limits](../02-structures/sequences-and-limits.md)
- [Polynomials](../02-structures/polynomials.md)

## Unlocks

(Destination.)

## Testable in axeyum

The decidable islands: **symbolic differentiation as computation** — compute a
derivative by the rules, then *verify* it (e.g. check the product rule
`(f·g)′ = f′g + fg′` on polynomial instances as an NRA identity); **polynomial/
rational identities**; and **RCF inequalities** (AM–GM, Cauchy–Schwarz at fixed
arity; monotonicity facts) decided by NRA — the same real-closed-field reasoning
as the geometry suite.

Example exercise: verify `d/dx (x³) = 3x²` by checking the limit-free polynomial
identity the power rule predicts; prove `x² + y² ≥ 2xy` over NRA. These teach
calculus's *algebra* with machine-checked certainty. They used to be described
as "flagging the limit layer as out of reach"; that is no longer true — the
limit layer is proved in the kernel (next section), and these exercises are the
bounded, self-checking *scenario* shadow of it rather than its ceiling.

## Proved in the kernel — the ε–δ layer, general and axiom-free

**This section corrects what stood here before.** The paragraph below used to
read: *"The definitions and theorems built on ε–δ — continuity,
differentiability, the mean value theorem, the fundamental theorem of calculus,
convergence of series — are Lean-horizon (Mathlib `Analysis`); only the
algebraic shadow is decidable."* Every item in that list is landed. Its
siblings ([linear algebra](linear-algebra.md), [number
theory](number-theory.md)) were corrected on 2026-08-30 and this page was
missed; measured 2026-08-31, `calculus` attributes **349 kernel declarations**
(294 theorems, 46 definitions), all axiom-free — the largest single node in the
curriculum after `naturals`.

The carrier is `CReal`, the **constructed** reals: a Bishop setoid over the
constructed rationals, trusted surface 0. It is not `AxReal`, the legacy
axiomatized ordered field (30 axioms), and the two differ by one letter.

| classical result | kernel declaration | axioms |
|---|---|---|
| Continuity, ε–δ with an explicit modulus | `CReal.UniformlyContinuousOn`, `.modulus` | 0 |
| Differentiability | `CReal.HasDerivativeOn` (inductive, with `.modulus`, `.spec`) | 0 |
| Sum / product / chain / power rules | `hasDerivative_add`, `_mul`, `_chain`, `_pow` | 0 |
| Uniqueness of the derivative | `CReal.hasDerivative_unique` | 0 |
| Fermat's interior-extremum lemma | `CReal.fermat_interiorExtremum` | 0 |
| Rolle's theorem | `CReal.rolle_interiorExtremum` | 0 |
| Mean value theorem | `CReal.mvt_interiorExtremum` | 0 |
| Monotonicity from the sign of the derivative | `monotone_of_nonneg_deriv`, `strict_mono_of_pos_deriv`, `antitone_of_nonpos_deriv` | 0 |
| Constancy from a zero derivative | `CReal.constant_of_zero_deriv` | 0 |
| The Riemann integral | `CReal.integral`, `CReal.riemannSum`, `integral_converges` | 0 |
| Additivity and linearity of the integral | `integral_split`, `integral_add`, `integral_scale`, `integral_le` | 0 |
| Fundamental theorem of calculus | `CReal.integral_eq_antideriv_diff`, `hasDerivative_antiderivative` | 0 |
| Integration by parts | `CReal.integral_by_parts` | 0 |
| Intermediate value theorem, with an exact root | `CReal.ivt_exact_root`, `ivt_bisect` | 0 |
| Extreme value theorem | `CReal.evt_approx_max`, `evt_attained_max_decides_sign` | 0 |
| Suprema on a compact interval | `CReal.supOn`, `supOn_approx_lub`, `supSeq_converges_supOn` | 0 |
| Uniform convergence, and that it preserves continuity | `CReal.UniformConvergesOn`, `uniform_limit_uniformly_continuous` | 0 |
| Differentiating a uniform limit | `CReal.hasDerivative_uniform_limit` | 0 |
| Weierstrass M-test | `CReal.weierstrassMTest` | 0 |
| Comparison and ratio tests | `sumRange_comparisonTest`, `sumRangeRatioTest` | 0 |
| Alternating-series bounds | `alternatingUpperBound`, `alternatingLowerBound` | 0 |
| exp, sin, cos as power series; `e` | `CReal.expFn`, `sinFn`, `cosFn`, `CReal.e`, `e_le_three` | 0 |
| Square root | `CReal.sqrt`, `sqrt_sq`, `mul_self_sqrt`, `sqrt_mul` | 0 |

Read these from the kernel, not from this table — it is a snapshot:

```sh
cargo run --release -p axeyum-lean-kernel \
  --example kernel_declaration_projection > /tmp/proj.tsv
python3 scripts/measure-curriculum-kernel-coverage.py /tmp/proj.tsv \
  --require-node calculus
```

`prelude_theorem_inventory` will **not** answer "does `CReal.integral` exist" —
it filters to `Declaration::Theorem`, so every definition above returns zero
rows from it.

## Still Lean-horizon, and why

The node's `status = "lean-horizon"` is **correct and stays**, because that
value means *"primarily a proof-reconstruction target, not a benchmark"* — the
scenario axis, not the kernel axis (ADR-1075). What is genuinely unbuilt:

- **Non-constructive limit reasoning.** `CReal` is a constructive carrier, so
  every existence result above carries a witness and a modulus. Statements that
  need excluded middle over the reals — an arbitrary bounded set has a
  supremum, a monotone bounded sequence converges without a rate — are not
  merely unproved but unstatable in this form. `CReal.lub_decides_em` records
  exactly that reduction.
- **Multivariable and metric-space calculus.** Partial derivatives, the
  implicit function theorem, and anything over a general metric space.
- **Measure theory.** The integral here is Riemann over uniformly continuous
  functions on a compact interval; Lebesgue is untouched.
- **Transcendence and closed-form evaluation.** `CReal.e` is constructed and
  bounded (`two_le_e`, `e_le_three`); its irrationality is not proved.

## References

- Spivak, *Calculus*; Rudin, *Principles of Mathematical Analysis*.
- axeyum: NRA (ADR-0024); MetiTarski (RCF inequalities) as the yardstick.
