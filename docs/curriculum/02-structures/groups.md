# Groups

> Layer 2 · structures · decidability: `bounded` · axeyum theory: BV / enumeration (finite groups) · status: `covered`

## What it is

A set with one associative operation, an **identity** element, and **inverses**
for every element. Examples: integers under addition, nonzero rationals under
multiplication, symmetries of a shape, ℤ/nℤ.

## Role in the tour

The first abstract algebraic structure — the point where mathematics shifts from
*numbers* to *structures satisfying axioms*. The base of the algebraic hierarchy
(group → ring → field) that Mathlib and the whole tour build upward from.

## Prerequisites

- [Relations & Functions](../00-foundations/relations-and-functions.md) — the operation is a function.

## Unlocks

- [Rings](rings.md)

## Testable in axeyum

For a **finite** group given by a Cayley table, the axioms are decidable checks:
closure, associativity (a triple-nested finite check), identity, inverses.
Encoding the table over `BitVec` indices makes axiom-checking a finite,
exhaustively-verifiable query.

Example exercise: present ℤ/4ℤ as a `4×4` table and verify the group axioms;
present a non-associative table and watch the associativity check produce a
counter-triple. Teaches axioms as *checkable predicates*.

**Built** (`Family::Algebra`, realized over the concrete group ℤ/2ʷℤ under
addition, self-checked exhaustively/by witness): `addition_associative`
((a+b)+c = a+(b+c)), `additive_inverse` (a + (−a) = 0), and
`subtraction_not_associative` — a SAT counterexample (witness `(0,1,1)`) showing
subtraction is *not* a group operation. The full Cayley-table / quasigroup
(Latin-square) encoding (cf. CSPLib prob003, Zhang's QG benchmarks) is the next
increment. Teaches the axioms as checkable predicates and the
counterexample-as-witness pattern.

## Lean-horizon

Lagrange's theorem, the classification of groups, Sylow theory, and anything
quantifying over all groups are Lean-horizon (Mathlib `GroupTheory`).

## References

- Dummit & Foote, *Abstract Algebra* (ch. 1–3).
- axeyum: BV/enumeration; EUF for the operation.
