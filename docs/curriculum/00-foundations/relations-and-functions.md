# Relations & Functions

> Layer 0 · foundations · decidability: `bounded` · axeyum theory: BV / EUF (finite domains) · status: `planned`

## What it is

A **relation** on sets is a subset of their Cartesian product; key kinds are
**equivalence relations** (reflexive, symmetric, transitive) and **orders**. A
**function** is a relation pairing each input with exactly one output, with
properties **injective**, **surjective**, **bijective**.

## Role in the tour

The connective tissue of structure: homomorphisms, linear maps, sequences, and
operations are all functions. Equivalence relations give quotients (ℤ/nℤ,
constructing ℚ from ℤ); orderings give ≤ on the number systems.

## Prerequisites

- [Sets](sets.md) — relations and functions are sets of pairs.

## Unlocks

- [Cardinality](cardinality.md)
- [Groups](../02-structures/groups.md)
- [Linear Algebra](../03-destinations/linear-algebra.md)

## Testable in axeyum

On a **finite domain**, a function is a finite table and its properties are
decidable checks. Equivalence-relation axioms and the congruence property
(`a = b ⇒ f(a) = f(b)`) are exactly what axeyum's EUF (uninterpreted functions +
congruence closure) decides — and the `Family::Function` scenarios already
exercise this.

Example exercise: declare an uninterpreted `f` over `BitVec(3)` and check
congruence (`a = b ⇒ f(a) = f(b)`) — `valid`, refuting its negation via the
e-graph — versus injectivity (`f(a) = f(b) ⇒ a = b`), which is *not* forced,
yielding a counter-model. Teaches the difference between a function and an
injection.

## Lean-horizon

General (infinite-domain) function theory, choice-dependent constructions, and
cardinality of function spaces are Lean-horizon.

## References

- Velleman, *How to Prove It* (relations, functions).
- axeyum: `axeyum-egraph`, `check_qf_uf`, `Family::Function`; ADR-0013/0032.
