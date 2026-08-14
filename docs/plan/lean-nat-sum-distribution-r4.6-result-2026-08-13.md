# Lean Nat finite-sum distribution R4.6 result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1;
[ADR-0394](../research/09-decisions/adr-0394-checked-scalar-distribution-over-finite-sums.md).

## Result

`Nat.mul_sumRange` proves, for every scalar, summand, and half-open range,

```text
a * sumRange f n = sumRange (fun i => a * f i) n.
```

The kernel checks a structural induction using only the existing proved
`left_distrib` law. This is reusable finite-sum algebra rather than another
Rado-specific recurrence or assumption.

The focused Nat run passes ten tests. The exact package inventory now contains
six definitions and 29 checked theorems. A positive control applies the theorem
to `3 * sumRange identity 4`, which computes to 18. The thirteenth mutation
control requires rejection when a scalar-two proof is assigned the inferred
scalar-three proposition. Determinism and the zero-axiom walk remain green.

All 212 kernel library tests, every kernel integration suite and doctest,
strict all-target/all-feature Clippy, strict rustdoc, the 65-row axiom ledger
and eight controls, foundational resources, plan authority, and links pass
locally.

## Boundary

This supplies scalar distribution, not the complete `thm:sharp` factorization
and not R4.6 closure. Generic sum congruence, the pointwise scaled-power step,
and additive normalization remain. No paper theorem is credited.
