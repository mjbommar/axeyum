# ADR-0437: Relational Euclidean remainders characterize Nat congruence

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.4 and R4.7.

## Context

ADRs 0434 and 0436 prove the two directions between `Nat.modEq` and equality
of remainders from supplied `Nat.divMod` witnesses. Leaving only directional
lemmas makes every downstream modular argument select and wire the direction
manually, even though the combined statement is the stable mathematical API.

## Decision

Add the zero-axiom theorem

```text
mod_eq_iff_div_mod_remainder_eq :
  divMod d a qa ra ->
  divMod d b qb rb ->
  (modEq d a b <-> ra = rb).
```

The forward implication applies ADR-0436. For the reverse implication,
transport the left `divMod` relation across `ra = rb`, then apply ADR-0434 to
the two relations with their now-shared remainder. The theorem adds no new
arithmetic or positivity premise; it packages already checked relational laws.

## Evidence

Concrete decompositions of seven and twelve by five instantiate the exact
equivalence `modEq 5 7 12 <-> 2 = 2`. NC58 changes the right-hand remainder
endpoint to one; the trusted admission gate rejects it. The deterministic
prelude census now covers 97 definitions and theorems, and the whole environment
remains covered by the zero-axiom audit.

## Consequences

Clients can reason about canonical remainders through a single relational
equivalence without an executable `%` operator. The next general number-theory
boundary is congruence versus divisibility, especially the theorem that
congruence to zero is equivalent to divisibility while preserving explicit
modulus-zero behavior.
