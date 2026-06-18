# Counting & Combinatorics

> Layer 2 · structures · decidability: `computable` · axeyum theory: LIA / enumeration · status: `covered`

## What it is

Techniques for counting finite structures: the **rules of sum and product**,
**permutations** `n!/(n−k)!`, **combinations** `C(n, k)`, the **binomial
theorem**, and the **pigeonhole principle** (`n+1` items in `n` boxes force a
collision).

## Role in the tour

A supporting tool for number theory (counting residues, divisors) and a clean
source of finite, decidable theorems — including the pigeonhole principle, a
favourite SAT/SMT encoding and a genuine "impossibility" result.

## Prerequisites

- [Sets](../00-foundations/sets.md)
- [Natural Numbers (Peano)](../01-number-systems/naturals.md)

## Unlocks

- [Number Theory](../03-destinations/number-theory.md)

## Testable in axeyum

Finite counting identities are compute-and-verify, and the **pigeonhole
principle at fixed sizes** is a classic decidable `unsat`: "an injection from an
`(n+1)`-set into an `n`-set" encoded over `BitVec` indices is unsatisfiable, with
a proof. Binomial identities (e.g. `C(n,k) = C(n,k−1) + C(n−1,k−1)` at fixed `n`)
are checkable.

Example exercise: encode "place 5 pigeons in 4 holes, no two sharing" and obtain
`unsat` — the combinatorial impossibility *certified*, not just asserted. (PHP
is also a proof-complexity landmark: **Haken 1985** proved it has no
polynomial-size resolution refutation, and **Beame–Pitassi–Impagliazzo 1993**
sharpened the bound to 2^Ω(n) — so it is a genuine stress test for proof
logging.)

**Built** (`Family::Counting`, self-checked by exhaustive enumeration / witness):
`pigeonhole(holes)` (n+1 pigeons → distinct hole indices is UNSAT) and
`permutation_exists(items)` (n into n distinct *is* SAT, witnessed by the
identity placement) — the SAT/UNSAT boundary, exhibited.

## Lean-horizon

General combinatorial identities (∀n), generating functions, and asymptotics are
Lean-horizon (Mathlib `Combinatorics`).

## References

- axeyum: BV/LIA, DRAT/Alethe proof for the pigeonhole `unsat`.
- Concrete Mathematics (Graham, Knuth, Patashnik).
