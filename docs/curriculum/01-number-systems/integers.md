# Integers

> Layer 1 · number systems · decidability: `computable` · axeyum theory: LIA / BV · status: `covered`

## What it is

The naturals extended with negatives: …, −2, −1, 0, 1, 2, …, forming a
commutative **ring** under + and ×, totally ordered. Constructed as equivalence
classes of pairs of naturals (`(a, b)` ≡ `a − b`).

## Role in the tour

The setting for divisibility and number theory, and the prototypical ring. The
jump from ℕ to ℤ is the first "quotient construction" (via an equivalence
relation), foreshadowing ℚ and ℤ/nℤ.

## Prerequisites

- [Natural Numbers (Peano)](naturals.md)

## Unlocks

- [Rational Numbers](rationals.md)
- [Divisibility & the Euclidean Algorithm](../02-structures/divisibility-and-euclid.md)
- [Rings](../02-structures/rings.md)

## Testable in axeyum

Linear integer arithmetic is decidable and is a core axeyum theory: equalities,
inequalities, and systems are decided by the integer simplex with
branch-and-bound, and **unsatisfiable** linear Diophantine equations are caught
by the GCD divisibility test (`2x + 4y = 3` is `unsat` because `gcd(2,4) ∤ 3`).

Example exercise: ring identities (`(a + b) − b = a`), the ordering trichotomy on
instances, and the GCD-test refutation of an unsolvable linear Diophantine
equation — the latter a genuinely number-theoretic, certificate-bearing `unsat`.

**Built** (`Family::NumberSystem`): `signed_trichotomy` (exactly one of `a<b`,
`a=b`, `a>b`) and `order_transitivity` (`a<b ∧ b<c ⇒ a<c`), the total-order
axioms as exhaustive UNSAT-of-negation theorems over signed bit-vectors.

## Lean-horizon

General quantified integer theorems requiring induction (Lean's `Int`).

## References

- axeyum: `check_with_lia_simplex`, `prove_lia_unsat_by_gcd` (ADR-0020/0021).
- Hardy & Wright, *An Introduction to the Theory of Numbers* (ch. 1).
