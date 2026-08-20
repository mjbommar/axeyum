# ADR-0562: Reduce dyadic fibre L2 to restricted Mobius parallelograms

Status: accepted
Date: 2026-08-20
Index-summary: Expand the exact inverse-difference fibre square and isolate a nilpotent four-shift Mobius correlation as the next dyadic theorem target

## Context

ADR-0507 combines dyadic autocorrelation fibres by their Artin--Schreier
product parameter before taking absolute values. The resulting connected bound
survives the tested endpoint tail, but neither the finite tables nor a positive
Fourier moment explain why it should hold uniformly.

For one exact affine fibre `F`, write

```text
c_F = sum_(f in F) mu(f) mu(f+h).
```

The proposed counting half of the connected estimate is

```text
sum_F c_F^2 <= sum_F #F.                              (E2')
```

Its left side was not previously retained, so the sign of the within-fibre
off-diagonal contribution was invisible.

## Decision

Retain the exact square sum, point count, nonzero-fibre count, and the split
between at-most-quadratic and nonquadratic product-discriminant phases in
`BinaryDyadicAutocorrelationFibreReport`. Report

```text
sum_F c_F^2 - sum_F #F
```

as the exact within-fibre off-diagonal correlation. Keep `(E2')` conjectural:
a finite nonpositive value is a diagnostic, not a theorem.

Also expose the algebraic identity that removes the opaque fibre-equality
predicate. In

```text
R_ell = GF(2)[x]/(x^(ell+1)),
delta_h(f) = f^(-1) + (f+h)^(-1),
```

where `f`, `f+h`, `f+t`, and `f+h+t` are units, one has

```text
delta_h(f) = delta_h(f+t)  <=>  h t(t+h) = 0 in R_ell. (P)
```

Indeed `delta_h(f)=h/(f(f+h))`; clearing the unit denominators and using
characteristic two leaves

```text
h((f+t)(f+t+h)+f(f+h)) = h t(t+h).
```

The factor `h` cannot be cancelled in the truncated ring. The native checker
therefore retains it and includes a mutation witness modulo `x^4` where
`h*t*(t+h)=0` but `t*(t+h)` is nonzero.

Consequently `(E2')` is exactly a sign assertion for a restricted four-shift
Mobius sum

```text
sum mu(f)mu(f+h)mu(f+t)mu(f+h+t),
```

where the high input coset is fixed and the translations satisfy
`h*t*(t+h)=0`. The `t=0` terms are precisely `sum_F #F`; proving `(E2')`
means proving that the remaining nilpotent parallelograms have nonpositive
total correlation.

## Evidence

The public identity checker exhausts every packed `f,h,t` through `ell=6` and
checks both directions of `(P)`. A separate pinned dyadic test requires at
`(ell,k,d)=(9,11,8)`

```text
sum_F c_F^2 = 120680,
sum_F #F    = 130048,
difference  = -9368.
```

The same test splits the square sum as `62948+57732` over the
at-most-quadratic and nonquadratic sectors, whose point counts are
`68784+61264`. Thus neither sector hides a positive defect. Exhaustive
endpoint rows through `ell=7` and the maximal-interval fleet rows through
`ell=14` satisfy `(E2')`; these finite rows remain uncredited.

The closest Newton-over-Hodge references do not prove this statement. The
Kramer--Miller and Kramer--Miller--Upton theorems assume `p>=3` or `p` odd,
and their Newton-polygon conclusions concern a different aggregate from the
restricted signed parallelogram above.

## Consequences

- The local dyadic target is now a precise four-point correlation theorem,
  not an unexplained spectrum pattern.
- A generic positive-moment, Cauchy, or absolute-value argument is unlikely to
  prove the required sign; the nilpotent strata and the Mobius phase must be
  used together.
- Even a proof of `(E2')` would address only the local energy input. The
  complementary signed cross-order Mobius convolution remains independently
  open, so this ADR grants no endpoint or Lemire theorem credit.
