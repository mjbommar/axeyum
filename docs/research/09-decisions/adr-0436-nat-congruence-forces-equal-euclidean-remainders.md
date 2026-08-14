# ADR-0436: Nat congruence forces equal Euclidean remainders

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.4 and R4.7.

## Context

ADR-0434 proves that two relational divisions with one remainder produce a
`modEq` fact. Mathematical algorithms also need the converse: congruent inputs
must have the same canonical Euclidean remainder. This is the point where the
balanced-witness congruence definition and the uniqueness theorem for
relational division must compose, without adding an executable `%` operation.

ADR-0435 supplies the general closure lemma needed to avoid duplicating the
order argument inside division uniqueness.

## Decision

Add the zero-axiom theorem

```text
div_mod_remainder_eq_of_mod_eq :
  modEq d a b ->
  divMod d a qa ra ->
  divMod d b qb rb ->
  ra = rb.
```

Eliminate the balanced witnesses `u`, `v`, and
`a+d*u = b+d*v`. Shift the two supplied divisions to quotients `qa+u` and
`qb+v` with ADR-0435, transport the right relation across the witness equation,
then apply `div_mod_unique` at the common dividend and project its remainder
equality.

No separate positivity premise is needed. Each `divMod` premise already
contains a strict remainder bound, so impossible modulus-zero inputs remain
uninhabited at the relation boundary.

## Evidence

Concrete decompositions `7 = 5*1+2` and `12 = 5*2+2`, together with
`modEq 5 7 12`, derive `2 = 2`. NC57 changes the conclusion to `2 = 1`; the
trusted admission gate rejects it. The deterministic prelude census covers 96
definitions and theorems, including this bridge, and the zero-axiom audit still
covers the complete environment.

## Consequences

For supplied relational Euclidean decompositions, `modEq` now characterizes
remainder equality in both directions. A small `Iff` packaging theorem can make
that equivalence directly reusable. The next number-theory bridge should then
connect congruence to divisibility, using zero remainders and exact relational
decompositions rather than signed subtraction or executable modulus.
