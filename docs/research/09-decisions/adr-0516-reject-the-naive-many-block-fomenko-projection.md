# ADR-0516: Reject the naive many-block Fomenko projection

Status: accepted
Date: 2026-08-19
Index-summary: Prove that projecting every binary Witt block to its first slot has kernel order `2^floor(ell/2)`, so the fixed-coordinate Fomenko mechanism does not scale with the Lemire conductor

## Context

Fomenko's treatment of three prescribed binary coefficients obtains a useful
low-degree `L`-function family by mapping Hayes characters to a fixed number of
additive coordinates with a small kernel.  A natural Lemire analogue projects
each odd-indexed 2-typical Witt block of the principal-unit group to its first
binary slot.

Before computing any grouped `L`-polynomials, the source, image, and kernel of
that map must be exact.  A growing kernel would fail the stopping test recorded
in the proof-unblocking audit: characterwise bounds inside exponentially large
fibres merely repackage the missing family cancellation.

## Decision

Add `binary_witt_first_slot_projection_report` to the bounded native Hayes CAS
API.  For the checked decomposition

```text
E_ell = product_(m odd, m<=ell) Z/2^L_m,
```

project each cyclic coordinate modulo two.  The operation checks that every
factor is a nontrivial power of two and independently reconciles source,
image, and kernel orders.  Its exhaustive small-level control enumerates every
fibre and every pair, verifying both uniform fibre size and

```text
epsilon(a+b)=epsilon(a)+epsilon(b).
```

The exact ledger is

```text
image rank  = ceil(ell/2),
kernel rank = floor(ell/2),
kernel size = 2^floor(ell/2).
```

Stop the naive first-slot generalization here.  Do not compute finite
`L`-factor tables and call their grouping a small-kernel reduction.

## Evidence

The focused native test checks levels `1..=8`, including every source pair at
each level.  The public report derives the general ranks from the already
checked power-of-two cyclic decomposition and fails closed if the three orders
do not multiply back to `2^ell`.

Fomenko's fixed-coordinate construction remains useful as a pattern only if a
different quotient has a bounded kernel or if an additional orthogonality
theorem cancels the large fibres.  Neither is supplied here.

## Consequences

- The direct many-block Fomenko route is structurally rejected, not merely
  unsupported by finite data.
- No SMT surface is added: this is exact finite-group algebra in the CAS.
- The live proof obligation remains the signed aggregate connected-cumulant
  bound, equivalently the `L2` estimate for binary Witt-refinement imbalances.
- A future quotient must expose new cross-block structure; selecting one bit
  independently from every block cannot inherit Fomenko's small-kernel gain.
