# ADR-0433: Multiplicative closure of Nat congruence

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.4.

## Context

ADR-0432 proves preservation beneath a common left multiplication. A complete
semiring congruence interface also needs common right factors and multiplication
of two independently congruent pairs. As with additive closure, these laws
should validate composition through the public API rather than repeat the
balanced-witness calculation.

## Decision

Add the zero-axiom theorems

```text
mod_eq_mul_right : modEq d a b -> modEq d (a*c) (b*c)
mod_eq_mul       : modEq d a b -> modEq d c e -> modEq d (a*c) (b*e).
```

Derive right-factor compatibility by applying ADR-0432 and transporting both
endpoints across checked multiplication commutativity. Derive pairwise
multiplication by right-scaling the first relation, left-scaling the second,
and composing them with checked transitivity.

## Evidence

The concrete relation `2 ≡ 7 (mod 5)` survives a common right factor of four.
Together with `3 ≡ 8 (mod 5)`, pairwise multiplication proves
`2*3 ≡ 7*8 (mod 5)`. NC53 changes the right factor and NC54 changes one pairwise
endpoint; the trusted gate rejects both. All 20 focused Nat tests pass,
including 54 negative controls, the deterministic 93-definition/theorem census,
and the zero-axiom audit.

## Consequences

`Nat.modEq` is now a proved semiring congruence: it is an equivalence relation
closed under pairwise addition and multiplication. The next general
number-theory boundary is relating it to divisibility and relational Euclidean
remainders, including modulus-zero behavior explicitly rather than hiding it
behind executable `%`.
