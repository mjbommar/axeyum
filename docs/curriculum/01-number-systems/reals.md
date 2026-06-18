# Real Numbers

> Layer 1 · number systems · decidability: `bounded` · axeyum theory: LRA / NRA (real-closed fields) · status: `planned`

## What it is

The complete ordered field: the rationals "filled in" so every bounded set has a
least upper bound (the **completeness axiom**), constructed via Dedekind cuts or
Cauchy sequences. The setting for all of analysis.

## Role in the tour

The destination-bearing number system for calculus, and the site of a beautiful
decidability fact: the **first-order theory of real-closed fields is decidable**
(Tarski) — polynomial (in)equalities over ℝ can be decided — even though
*completeness* (a second-order property) cannot.

## Prerequisites

- [Rational Numbers](rationals.md)

## Unlocks

- [Sequences & Limits](../02-structures/sequences-and-limits.md)
- [Calculus](../03-destinations/calculus.md)
- [Complex Numbers](complex.md)

## Testable in axeyum

Two decidable layers: **linear** real facts via the exact-rational simplex
(LRA), and the **nonlinear** (polynomial) fragment via NRA — sign/zero lemmas,
McCormick relaxations, monotonicity lemmas (axeyum's incremental linearization),
the decidable real-closed-field theory in the Tarski sense.

Example exercise: `x ≥ 1 ∧ y ≥ 1 ⇒ x·y ≥ 1` (decided by NRA monotonicity
lemmas); AM–GM for two terms `x² + y² ≥ 2xy` (a sum-of-squares fact). These are
genuine real-analysis-adjacent theorems decided without floating point.

## Lean-horizon

The **completeness axiom** itself (a statement about all bounded subsets) is
second-order and Lean-horizon, as are limits/continuity defined via ε–δ.

## References

- Tarski, *A Decision Method for Elementary Algebra and Geometry* (RCF decidability).
- axeyum: NRA linearization (ADR-0024), `check_with_lra`; P2.5.
