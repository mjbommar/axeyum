# ADR-0432: Left multiplication preserves Nat congruence

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.4.

## Context

ADR-0431 establishes additive closure. General modular arithmetic also needs
scaling: a congruence must remain true after multiplication by an arbitrary
natural, including zero. This law should follow constructively from the
balanced witnesses and must not acquire positivity, cancellation, or division
preconditions.

## Decision

Add the zero-axiom theorem

```text
mod_eq_mul_left : modEq d a b -> modEq d (c*a) (c*b).
```

If `a+d*u=b+d*v`, use `c*u` and `c*v` as the new balanced witnesses. Prove
`d*(c*u)=c*(d*u)` and its right-side analogue from multiplication
associativity and commutativity, distribute `c` across the source equality,
and compose the checked equality chain.

The law is unconditional in both `d` and `c`. In particular, modulus zero and
factor zero are ordinary cases rather than side-condition exceptions.

## Evidence

Scaling `2 ≡ 7 (mod 5)` by four proves `4*2 ≡ 4*7 (mod 5)`. NC52 changes only
one occurrence of the common factor and the trusted declaration gate rejects
it. All 20 focused Nat tests pass, including 52 negative controls, the
deterministic 91-definition/theorem census, and the zero-axiom audit.

## Consequences

`Nat.modEq` supports multiplication by a common left factor. Right-factor and
pairwise multiplication closure can now be derived compositionally using
commutativity and transitivity, as the additive API was under ADR-0431.
