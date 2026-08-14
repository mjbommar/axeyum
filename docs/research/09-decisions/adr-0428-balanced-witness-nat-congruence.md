# ADR-0428: Balanced-witness Nat congruence

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.4.

## Context

R4.4 needs congruence modulo a natural divisor as reusable number-theory
infrastructure. Defining it with truncated Nat subtraction would lose the sign
of a difference; defining it through equal `divMod` remainders would make the
basic relation depend on positive divisors and nested decomposition witnesses.
Neither boundary is suitable for a general congruence relation.

The subtraction-free prefix argument learned from the Rado development is
relevant, but the public API must support proofs beyond that paper rather than
encode its particular rigidity theorem.

## Decision

Define balanced-witness congruence by

```text
modEq d a b := exists u v, a + d*u = b + d*v.
```

Add checked reflexivity, symmetry, and transitivity laws. Transitivity composes
the two witness pairs as `u+x` and `y+v`; its equality proof uses only the
already proved distributivity, associativity, commutativity, and equality
transport laws.

Do not add signed subtraction, `%`, choice, a positive-modulus precondition, or
Rado-specific predicates. Addition and multiplication compatibility belong to
the next increment so their own mutation and downstream-use evidence remains
auditable.

## Evidence

Concrete witnesses prove `2 ≡ 7 (mod 5)` and transitivity through
`7 ≡ 12 (mod 5)`. NC46--NC48 independently alter the endpoints of reflexivity,
symmetry, and transitivity; the trusted declaration gate rejects all three.
All 20 focused Nat tests pass, including 48 negative controls, the deterministic
87-definition/theorem census, and the zero-axiom audit.

## Consequences

R4.4 now has a constructive equivalence relation that is meaningful even at
modulus zero and does not depend on executable division. It is an algebraic
foundation rather than a complete congruence library: compatibility with
addition and multiplication, links to divisibility, and remainder
characterizations remain explicit follow-up work.
