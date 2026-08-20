# ADR-0553: Distinguish projective eigenlines from affine fixed vectors

Status: accepted
Date: 2026-08-20
Index-summary: Classify the long-cycle projective eigenlines and reject a free cyclic-quotient shortcut

## Context

ADR-0552 separates the affine cone vertex from its projectivization and leaves
the binary Frobenius--long-cycle trace on the projective fibre as the endpoint
obligation.  A tempting next step is to reuse the affine fixed-locus
calculation to assert that the long cycle, or its odd part, acts freely on the
projectivization.  That inference is invalid: a projective fixed point is an
eigenline and need not contain an affine fixed vector.

## Decision

Add the bounded native report `sawin_projective_eigenline_report` and classify
the full-cycle eigenlines before considering cyclic quotients.

Write

```text
n=q b,  q=2^v2(n),  b odd.
```

Over the algebraic closure the cyclic shift has one geometric eigenline for
each `b`th root of unity.  If the eigenvalue has exact order `e|b`, the
coordinates on that line form a geometric progression.  Their root polynomial
is

```text
(x^e-A^e)^(n/e).
```

Because `n/e=q(b/e)` and `b/e` is odd, Lucas's theorem makes the first
potentially nonzero nonleading coefficient occur at index `eq`.  The
projective eigenline lies in the zero-coefficient endpoint fibre exactly when

```text
eq > ell,  ell=ceil(n/2)-1.
```

If `e<b`, then `e<=b/3`, hence `eq<=n/3<=ell`.  Such an eigenline is excluded.
For `e=b`, one has `eq=n>ell`, and the root polynomial reduces to

```text
(x^b-A^b)^q=x^n-A^n.
```

Thus exactly the primitive `b`th-root eigenlines survive.  The reduced
projective fixed locus has `phi(b)` geometric points, including one when
`b=1`.  The full projective long-cycle action is therefore never free.  When
`n` is odd the action is tame, so the fixed scheme is reduced and its ordinary
projective Euler trace is `phi(n)`.  At even degree the report does not assert
scheme reducedness or apply tame Lefschetz to the wild cycle.

## Evidence

- The native report factors the odd cycle order, enumerates every divisor
  `e|b`, and requires `eq>ell` to select exactly `e=b`.
- It computes `phi(b)` from the independently used Foulkes factorization
  helpers and checks the endpoint decomposition `n=qb`.
- Pinned rows give `400`, `132`, `2`, and `1` reduced geometric fixed points
  at degrees `401`, `402`, `12`, and `512` respectively.
- The focused test and all-target, all-feature `axeyum-cas` Clippy gate pass.
- The report retains `frobenius_weighted_trace_bound_certified=false`: a
  fixed-locus classification for the cycle alone does not bound
  `Frob*c`, as already witnessed in degree five by ADR-0552.

## Alternatives

- **Promote the affine fixed-point calculation to projective freeness:**
  rejected because nontrivial scalar eigenvectors define projective fixed
  points.
- **Count all `b` eigenvalues:** rejected because eigenvalues of proper order
  produce a coefficient at index `eq<=ell` and are excluded.
- **Use the reduced point count for wild Lefschetz:** rejected because the
  even-degree fixed scheme may be nonreduced and the cycle order is divisible
  by the characteristic.

## Consequences

- A finite-etale cyclic-torsor proof cannot be built from the full projective
  long-cycle action.
- The surviving eigenlines are explicitly the primitive tame eigenvalues;
  any equivariant stratification must include them rather than silently treat
  the action as free.
- This is a stopping theorem, not the missing positive Frobenius estimate.
  The endpoint fact remains open.
