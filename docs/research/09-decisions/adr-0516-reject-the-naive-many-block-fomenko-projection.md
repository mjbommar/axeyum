# ADR-0516: Reject elementary-abelian many-block Fomenko projections

Status: accepted
Date: 2026-08-19
Index-summary: Prove that every elementary-abelian quotient has kernel at least `2^floor(ell/2)`, so the fixed-coordinate Fomenko mechanism does not scale with the Lemire conductor

## Context

Fomenko's treatment of three prescribed binary coefficients obtains a useful
low-degree `L`-function family by mapping Hayes characters to a fixed number of
additive coordinates with a small kernel.  A natural Lemire analogue projects
each odd-indexed 2-typical Witt block of the principal-unit group to its first
binary slot.  Fomenko's actual map restricts characters to a square-zero
additive subgroup, so the relevant stopping test is broader: could *any*
homomorphism to an elementary abelian binary group have a smaller kernel?

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

This is optimal among all elementary-abelian targets.  Every homomorphism
`phi:E_ell -> GF(2)^r` kills `2 E_ell` and therefore factors through

```text
E_ell / 2 E_ell = GF(2)^ceil(ell/2).
```

Each cyclic Witt block contributes exactly one bit to this quotient.  Thus
`rank(image phi)<=ceil(ell/2)` and
`dim(kernel phi)>=floor(ell/2)`; the checked first-slot map attains equality.

Stop every elementary-abelian generalization here.  Do not compute finite
`L`-factor tables and call their grouping a small-kernel reduction.

## Evidence

The focused native test checks levels `1..=8`, including every source pair at
each level.  The public report derives the general ranks from the already
checked power-of-two cyclic decomposition and fails closed if the three orders
do not multiply back to `2^ell`.

Fomenko's fixed-coordinate construction remains useful as a pattern only if a
non-elementary target retains higher Witt slots together with an additional
orthogonality theorem that cancels the large fibres.  Merely choosing a
different collection of additive binary coordinates cannot improve the
kernel.  No such higher-Witt orthogonality theorem is supplied here.

## Consequences

- Every elementary-abelian many-block Fomenko route is structurally rejected,
  not merely unsupported by finite data.
- No SMT surface is added: this is exact finite-group algebra in the CAS.
- The live proof obligation remains the signed aggregate connected-cumulant
  bound, equivalently the `L2` estimate for binary Witt-refinement imbalances.
- A future quotient must retain non-elementary higher-Witt structure and
  expose new cross-block cancellation; no additive binary coordinate map can
  inherit Fomenko's small-kernel gain.
