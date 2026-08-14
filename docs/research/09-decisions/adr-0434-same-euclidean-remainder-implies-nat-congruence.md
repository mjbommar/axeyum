# ADR-0434: Equal Euclidean remainders imply Nat congruence

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.4 and R4.7.

## Context

The proved `Nat.modEq` relation and relational `Nat.divMod` interface currently
form separate general-purpose library layers. Mathematical reconstruction needs
to move between them without adding executable quotient/remainder reduction or
specializing the API to the Rado shell argument that exposed the gap.

The first direction is constructive and does not need a positive-divisor side
condition: if supplied `divMod` witnesses give two dividends the same
remainder, their opposite quotients are balanced witnesses of congruence.
Impossible modulus-zero `divMod` premises remain impossible rather than being
hidden by an extra hypothesis.

## Decision

Add the zero-axiom theorem

```text
div_mod_same_remainder_mod_eq :
  divMod d a qa r -> divMod d b qb r -> modEq d a b.
```

Eliminate both relational conjunctions and use `qb` and `qa` as the balanced
congruence witnesses. The checked equality chain uses only the supplied
decomposition equations plus proved associativity/commutativity of addition:

```text
a + d*qb = (d*qa+r) + d*qb
           = (d*qa+d*qb) + r
           = (d*qb+d*qa) + r
           = (d*qb+r) + d*qa
           = b + d*qa.
```

## Evidence

Concrete relational witnesses for `7 = 5*1+2` and `12 = 5*2+2` derive
`modEq 5 7 12`. NC55 changes the second dividend in the conclusion; the trusted
admission gate rejects it. The deterministic prelude census covers the new
theorem and the zero-axiom audit still covers the whole environment.

## Consequences

Relational Euclidean division can now produce modular facts without `%`, signed
subtraction, or a Rado-specific wrapper. The converse direction remains next:
under two `divMod` witnesses, a `modEq` proof should force equality of their
remainders by lifting both decompositions to one balanced dividend and applying
`div_mod_unique`.
