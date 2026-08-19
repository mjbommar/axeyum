# ADR-0490: Expose exact classwise Möbius distributions as a bounded CAS diagnostic

Status: accepted
Date: 2026-08-19
Index-summary: Add exact signed principal-unit Möbius distributions with dual-modulus reconstruction and independent factorization controls, without claiming weighted cancellation

## Context

The half-interval sieve in ADR-0487 proves exact Type-I divisibility but meets
the parity barrier.  A Vaughan-style repair would require cancellation in
Möbius-weighted class sums.  The existing Hayes machinery computed the class
series `A`, its logarithmic derivative `Lambda`, and prime-power inversion, but
did not expose the inverse series `M=A^(-1)` whose coefficients are precisely
the classwise polynomial Möbius sums.

The unweighted wild-Kloosterman estimate in ADR-0489 does not fill that gap.
Arbitrary weights can concentrate on the product fibre, so an unweighted
product-multiplicity bound cannot be substituted for a weighted bilinear
estimate.

## Decision

Add `class_mobius_distribution` to `axeyum-cas::gf2_hayes`.  In every character
coordinate it computes

```text
M_0=1,
M_n=-sum_(1<=d<=n) A_d M_(n-d),
```

then applies the existing inverse principal-unit transform.  Two NTT-modulus
tables are reconstructed as signed integers.  Admission uses the existing
`HayesLimits`; reconstruction requires the coarse interval
`[-2^degree,2^degree]` to fit uniquely in the CRT modulus.

Keep this operation CAS-local.  Do not add a Möbius operator to the term IR or
an SMT predicate for analytic cancellation.  The returned finite table is a
diagnostic and a source of exact conjecture-selection data, not a universal
bound.

Also expose `identity_class_mobius_convolution`, the checked group-ring
logarithmic-derivative identity

```text
Delta_(ell,n)=sum_(1<=d<ell) d sum_(u in V_d) M_(n-d)(u^(-1)).
```

Compute all required Möbius rows once per NTT modulus, reconstruct every
signed summand by CRT, and require their sum to equal the independently
computed identity-class discrepancy.

Expose `inverse_additive_mobius_spectrum` as the exact finite Fourier bridge.
It maps the class table through unit inversion into additive coefficient
coordinates, applies a checked integral Walsh transform, and recovers inverse
interval fibres by summing annihilator frequencies with the exact
`2^(d-ell)` normalization.  Keep this CAS-local and finite; it is not a new IR
operator or a claim of asymptotic cancellation.

## Evidence

Every recovered coordinate is checked against `|M_n(e)|<=2^n`.  Summing the
coordinates must reproduce the polynomial Euler-product identity

```text
sum_(f monic, deg f=1) mu(f)=-2,
sum_(f monic, deg f=n) mu(f)=0  (n>1).
```

An independent test enumerates every monic binary polynomial, factors it with
the existing Berlekamp implementation, derives its Möbius value from distinct
factor multiplicities, and buckets its leading coefficients directly.  It
matches every class for `1<=ell<=5`, `1<=degree<=8`.  A larger transform pin at
`(ell,degree)=(8,17)` records identity value `-22`, maximum magnitude `48`, and
squared norm `85072`.  Invalid, resource-limited, and signed-CRT-ambiguous
requests decline explicitly.

The same factorization oracle independently checks every convolution term at
both endpoints for `2<=ell<=5`.  Mutation controls require at least one case
to reject omission of the interval-degree weight and at least one to reject
replacement of the inverse class by the original class.

The inverse-additive spectrum is checked against direct Berlekamp
factorization and direct character summation for `2<=ell<=5`.  The same oracle
checks frequency-by-frequency the reciprocal/ramified-factor identity
`H_k=B_k-B_(k-1)`, and the Fourier annihilator formula reconstructs every
endpoint fibre through `ell=9`.  Exact Walsh Parseval is an additional runtime
invariant.

## Alternatives

- Infer Möbius values from the Mangoldt table: rejected because logarithmic
  differentiation and series inversion are different operations, and the
  weighted decomposition needs the latter explicitly.
- Record only the identity class: rejected because weighted bilinear and
  moment diagnostics require the complete distribution.
- Promote observed square-root-sized values to a theorem: rejected because a
  finite transform supplies no quantified cancellation proof.

## Consequences

- Axeyum can now measure the exact parity-breaking object selected by a
  characteristic-two Vaughan or Berlekamp-discriminant attack.
- The remaining weighted cancellation is one explicit short signed sum, not
  an unspecified appeal to a Vaughan decomposition.
- Autogenesis and the fact ledger still receive no universal cancellation
  credit from this bounded operation.
- The remaining mathematical choice is explicit: prove a weighted binary
  bilinear estimate, prove a recurrence-wide Möbius bound, or abandon the
  Vaughan route in favor of an aggregate endpoint estimate.
