# ADR-0413: Relational Nat valuation at two

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.9 / R7.1.

## Context

R4.9 requires valuation to be stated relationally so theorem developments do
not depend on division or an unproved total valuation function. The sharpness
witness needs only the exact statement `v_a(Z)=2`: divisibility by `a^2` and
nondivisibility by `a^3`.

## Decision

Add the zero-axiom definition and checked theorem

```text
valuationAt a n e := a^e|n and Not (a^(e+1)|n)
valuation_at_two_mul_sq :
  2<=a -> Not (a|u) -> valuationAt a ((a*a)*u) 2.
```

Normalize the powers at exponents two and three with the proved power laws.
Introduce the square-divisibility witness directly. For nondivisibility by the
cube, expose its witness, reassociate to a common `a*a` factor, prove that
factor positive, cancel it with ADR-0411, and contradict `a does not divide u`.

## Evidence

The positive control proves that `4*7` has exact base-two valuation two from
the independently checked fact `2 does not divide 7`. NC32 changes the claimed
exponent to one; declaration checking rejects it without insertion. The
deterministic inventory now contains 60 theorems and 9 definitions, with zero
axioms.

## Consequences

The framework now has the relational valuation representation prescribed by
R4.9 and the exact generic lemma needed by `thm:sharp`. Existence and
uniqueness for arbitrary positive naturals remain separate R4.9 obligations;
the next step is specializing this theorem to the paper's closed-form `u'`.
