# Natural Numbers (Peano)

> Layer 1 · number systems · decidability: `bounded` · axeyum theory: LIA / BV · status: `covered`

## What it is

The numbers 0, 1, 2, … axiomatized by **Peano**: a zero, a **successor**
function, and the **induction axiom**. Addition and multiplication are defined
recursively (`a + 0 = a`, `a + S(b) = S(a + b)`).

## Role in the tour

The first number system and the home of induction. Everything numeric is built
upward from here: integers (signed naturals), rationals (pairs of integers),
reals (limits of rationals).

## Prerequisites

- [Sets](../00-foundations/sets.md) — the Peano structure is built set-theoretically.

## Unlocks

- [Integers](integers.md)
- [Mathematical Induction](../00-foundations/induction.md)

## Testable in axeyum

Concrete arithmetic and ordering over naturals are decidable: as bounded
`BitVec(n)` or as `Int` constrained non-negative, axeyum decides equalities,
inequalities, and the recursive defining equations on instances. The Peano
*induction axiom* (second-order / a schema) is **not** an SMT query — see
[Induction](../00-foundations/induction.md).

Example exercise: the recursive law `a + S(b) = S(a + b)` over `BitVec(8)` is an
identity, refuted-by-negation exhaustively; `a + b = b + a` (commutativity)
likewise. These teach that the *defining equations* hold, while leaving the
universal-over-all-ℕ statements to induction.

**Built** (`Family::NumberSystem`): `unsigned_non_negative` (every unsigned value
is `≥ 0` — the naturals have no negatives) and `successor_injective`
(`x+1 = y+1 ⇒ x = y` — the Peano successor axiom), both exhaustive UNSAT of the
negation.

## Lean-horizon

Peano arithmetic with the full induction schema is incomplete (Gödel) and
undecidable; universal theorems live in Lean (Mathlib's `Nat`).

## References

- Landau, *Foundations of Analysis* (Peano construction).
- axeyum: `Int` sort + LIA (ADR-0014); BV evaluator.
