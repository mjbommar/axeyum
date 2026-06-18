# Mathematical Induction

> Layer 0 · foundations · decidability: `bounded` · axeyum theory: LIA / BV (base + step instances) · status: `planned`

## What it is

The principle that, to prove `P(n)` for all natural numbers `n`, it suffices to
prove the **base case** `P(0)` and the **inductive step** `P(k) → P(k+1)`.
Variants: strong induction, structural induction (over datatypes), well-founded
induction.

## Role in the tour

The engine of number theory and the first genuinely *infinitary* tool: it proves
infinitely many statements from two finite obligations. It is also the sharpest
illustration of the decidable/undecidable boundary — the *schema* is not
decidable, but each *obligation* often is.

## Prerequisites

- [Proof Methods](proof-methods.md)
- [Natural Numbers (Peano)](../01-number-systems/naturals.md) — induction is a Peano axiom.

## Unlocks

- [Number Theory](../03-destinations/number-theory.md)

## Testable in axeyum

The induction *schema* (`∀P …`) quantifies over predicates and is not a
decidable SMT query. But the **two obligations of a specific induction** usually
are: `P(0)` is a ground check, and `P(k) → P(k+1)` is a quantifier-free (or
finite-domain) implication a solver can discharge.

Example exercise: to teach `1 + 2 + … + n = n(n+1)/2`, give the learner the two
obligations — base `0 = 0`, and step `S(k) = n(n+1)/2 ⇒ S(k+1) = (k+1)(k+2)/2`
— and have axeyum discharge the (algebraic) step over LIA/BV. The learner sees
induction decomposed into machine-checkable pieces.

## Lean-horizon

Tying the obligations into a single `∀n` theorem (applying the induction axiom
itself) is the proof-assistant step — a P3.6/P3.7 reconstruction target. axeyum
checks the pieces; Lean assembles them into the universal statement.

## References

- Velleman, *How to Prove It* (ch. on induction).
- axeyum: LIA (`check_with_lia_simplex`), BV evaluator; ADR-0014.
