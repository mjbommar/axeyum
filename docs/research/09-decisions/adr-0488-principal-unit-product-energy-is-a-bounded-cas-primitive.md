# ADR-0488: Expose principal-unit product energy as a bounded CAS primitive

Status: accepted
Date: 2026-08-19
Index-summary: Add an exact closed-form Type-II product-energy report for bounded principal-unit intervals without promoting an unproved prime-cancellation claim

## Context

The exact half-level Möbius calculation in ADR-0487 stops at the parity
barrier.  The next legitimate input is bilinear: for

```text
V_d={1+a_1x+...+a_dx^d} subset E_ell,
E_ell=(1+x GF(2)[x])/(x^(ell+1)),
```

count collisions `ab=ce` with `a,b,c,e in V_d`.  This is the multiplicative
energy of the coefficient interval and, by finite-group Parseval, the fourth
moment of its nonprincipal character sums.  It is reusable in Type-II and
Hayes-character arguments, but it is not by itself a prime lower bound.

The collision count has an elementary closed form.  If `2d<=ell`, modular
equality is ordinary polynomial equality and

```text
E(ell,d)=(d+2)2^(2d-1).
```

If `2d>ell`, then

```text
E(ell,d)=2^(4d-ell)+(ell-d)2^(2d-1).
```

## Decision

Add `principal_unit_product_energy` to the bounded `gf2_hayes` CAS surface.
Its report records the interval and pair sizes, the exact collision energy,
the integral nonprincipal Fourier fourth-moment numerator, and whether the
ordinary-product regime applies.

The operation evaluates the proved closed form with exact bignums.  It checks
`ell`, degree, and group-order admission before arithmetic and rejects
`degree=0` or `degree>=ell`.  It allocates no transform table.

Keep the operation CAS-local.  Do not add a Type-II predicate or analytic
bound to SMT, and do not register the still-open endpoint cancellation as an
Autogenesis operation.

## Evidence

For a coprime reduced ordered pair `(a,c)` of height
`s=max(deg a,deg c)`, every pair `(A,C)` with reduced ratio `a/c` is
`(ga,gc)` for one of `2^(d-s)` choices of `g`.  The number of reduced ordered
pairs of height exactly `s` is one for `s=0` and `2^(2s-1)` for `s>=1`.

For fixed reduced `(a,c)`, solutions of

```text
aB+cD = x^(ell+1) H,   B,D in V_d,
```

number

```text
2^max(d-s, 2d-ell).
```

Indeed `H=0` gives the syzygies `(B,D)=(ck,ak)`.  When `H` is nonzero,
division by whichever of `a,c` has degree `s` supplies a degree-bounded
particular solution for every `deg H<=s+d-ell-1`; adding a syzygy fixes both
constant terms.  Summing over `s` gives the two displayed formulas.

Unit tests independently enumerate all products for every
`2<=ell<=8` and `1<=d<ell`, then compare the collision tables with the closed
form.  Separate controls pin one ordinary and one projected value and exercise
invalid and resource-limited inputs.  Warning-denied all-target, all-feature
CAS Clippy passes.

## Alternatives

- Retain only an exponential product-table experiment: rejected because the
  collision count has a closed form and the table would obscure its proof.
- Treat fourth energy of `V_d` as the missing fourth moment of the Mangoldt
  distribution: rejected because logarithmic differentiation and connected
  cross-degree correlations remain.  These are different moments.
- Encode product collisions in SMT: rejected because exact bignum evaluation
  is sufficient and SMT would not establish the required uniform analytic
  cancellation.

## Consequences

- Axeyum has a native, replayable Type-II quantity immediately beyond the
  pointwise sieve barrier.
- Future proof attempts can use an exact Fourier fourth-moment input without
  recomputing exponential collision tables.
- The remaining paper obligation stays explicit: control the connected
  cross-degree/logarithmic correlations, or find a construction.  This ADR
  grants no credit to the universal Lemire conjecture.
