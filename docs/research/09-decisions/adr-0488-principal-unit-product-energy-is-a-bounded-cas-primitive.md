# ADR-0488: Expose principal-unit mixed product energy as a bounded CAS primitive

Status: accepted
Date: 2026-08-19
Index-summary: Add exact closed-form Type-II mixed product-energy reports for bounded principal-unit intervals without promoting an unproved prime-cancellation claim

## Context

The exact half-level Möbius calculation in ADR-0487 stops at the parity
barrier.  The next legitimate input is bilinear: for

```text
V_d={1+a_1x+...+a_dx^d} subset E_ell,
E_ell=(1+x GF(2)[x])/(x^(ell+1)),
```

count collisions `ab=ce` with `a,b,c,e in V_d`.  More generally, a bilinear
decomposition needs collisions between `V_a V_b`.  These are the
multiplicative and mixed energies of the coefficient intervals and, by
finite-group Parseval, the fourth and mixed `L^2 x L^2` moments of their
nonprincipal character sums.  They are reusable in Type-II and
Hayes-character arguments, but they are not by themselves a prime lower bound.

The collision count has an elementary closed form.  If `2d<=ell`, modular
equality is ordinary polynomial equality and

```text
E(ell,d)=(d+2)2^(2d-1).
```

If `2d>ell`, then

```text
E(ell,d)=2^(4d-ell)+(ell-d)2^(2d-1).
```

The same gcd count gives the full mixed formula.  For `a<=b`,

```text
E(ell;a,b)=(a+2)2^(a+b-1),                         a+b<=ell,
E(ell;a,b)=2^(2a+2b-ell)+(ell-b)2^(a+b-1),         a+b>ell.
```

## Decision

Add `principal_unit_mixed_product_energy` and its equal-degree wrapper
`principal_unit_product_energy` to the bounded `gf2_hayes` CAS surface.  Their
reports record the interval and pair sizes, the exact collision energy, the
integral nonprincipal Fourier-moment numerator, and whether the
ordinary-product regime applies.

The operation evaluates the proved closed form with exact bignums.  It checks
`ell`, both degrees, and group-order admission before arithmetic and rejects a
zero degree or a degree at least `ell`.  It allocates no transform table.

Keep the operation CAS-local.  Do not add a Type-II predicate or analytic
bound to SMT, and do not register the still-open endpoint cancellation as an
Autogenesis operation.

## Evidence

For a coprime reduced ordered pair `(u,w)` of height
`s=max(deg u,deg w)`, every pair `(A,C) in V_a^2` with reduced ratio `u/w` is
`(gu,gw)` for one of `2^(a-s)` choices of `g`.  The number of reduced ordered
pairs of height exactly `s` is one for `s=0` and `2^(2s-1)` for `s>=1`.

For fixed reduced `(u,w)` of height `s`, solutions of

```text
uB+wD = x^(ell+1) H,   B,D in V_b,
```

number

```text
2^max(b-s, 2b-ell).
```

Indeed `H=0` gives the syzygies `(B,D)=(wk,uk)`.  When `H` is nonzero,
division by whichever of `u,w` has degree `s` supplies a degree-bounded
particular solution for every `deg H<=s+b-ell-1`; adding a syzygy fixes both
constant terms.  Summing these solution counts with the common-factor and
reduced-ratio counts gives the mixed formula; setting `a=b=d` gives the
equal-degree cases.

Unit tests independently enumerate all mixed products for every
`2<=ell<=8` and every ordered pair `1<=a,b<ell`, then compare the collision
tables with the closed form.  Separate controls pin ordinary and projected
values, symmetry, the equal-degree wrapper, and invalid/resource-limited
inputs.  Warning-denied all-target, all-feature CAS Clippy passes.

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

- Axeyum has native, replayable Type-II mixed quantities immediately beyond
  the pointwise sieve barrier.
- Future proof attempts can use exact Fourier mixed-moment inputs without
  recomputing exponential collision tables.
- The remaining paper obligation stays explicit: control the connected
  cross-degree/logarithmic correlations, or find a construction.  This ADR
  grants no credit to the universal Lemire conjecture.
