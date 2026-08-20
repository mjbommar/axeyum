# ADR-0558: Extract exact-degree support by maximal-subfield differences

Status: accepted
Date: 2026-08-20
Index-summary: Replace the overstrong common-period target by an exact product of maximal-subfield differences and distinguish prime-power from mixed-divisor degrees

## Context

ADR-0555 encodes the Lemire coefficient indicator as the Fourier transform of

```text
Gamma_(n,ell)=*_(j=1)^ell (delta_0+delta_j)
```

on `C_N=Z/(2^n-1)`, where `ell=ceil(n/2)-1`.  Its first sufficient target was
that the least period of `Gamma` not divide

```text
M_n=lcm_(d|n,d<n)(2^d-1).
```

That condition is exact when the proper subfields are nested, but it is
stronger than existence in general.  If `n` has distinct prime divisors, the
subgroup of `GF(2^n)^*` killed by exponent `M_n` strictly overcovers the union
of the proper subfields.  Treating the single-period target as an equivalent
reformulation would therefore be unsound.

## Decision

For each distinct prime divisor `p` of `n`, put

```text
T_p=2^(n/p)-1,
Q_n=product_(p|n) (1+tau_(T_p)),
```

where `tau_T` translates a function on `C_N` by `T`.  Use

```text
Q_n Gamma_(n,ell) != 0                              (ED)
```

as the exact characteristic-delta criterion.

Indeed, if `zeta` generates `GF(2^n)^*` and `F(a)` is the Fourier transform of
`Gamma`, Fourier transformation gives

```text
DFT(Q_n Gamma)(a)
 = F(a) product_(p|n) (1+zeta^(a T_p)).             (FD)
```

The factor indexed by `p` vanishes exactly when `zeta^a` lies in the maximal
proper subfield `GF(2^(n/p))`.  Every element of degree less than `n` lies in
one of those maximal proper subfields.  Since `F` is precisely the indicator
of the Lemire coefficient conditions, `(FD)` and invertibility of the DFT
prove

```text
Q_n Gamma != 0
 iff an admissible element has exact degree n
 iff a Lemire irreducible of degree n exists.        (EQ)
```

Extend `tuxanidy_lemire_period_report` with the maximal-subfield periods, the
support and first witness of `Q_n Gamma`, and a flag stating whether the older
single-period test is exact at that degree.  Charge the additional
`omega(n)(2^n-1)` translation cells to the existing fail-closed work budget.

The single-period and exact criteria coincide precisely when `n` is a prime
power: then every proper divisor of `n` divides `n/p`, so all proper subfields
lie in the unique maximal one and `M_n=T_p`.  For a mixed-divisor degree, the
single-period test remains a valid sufficient condition but is not presented
as an equivalence.

## Evidence

The bounded native convolution has nonzero exact-degree difference in every
row `3<=n<=12`.  This finite table is only a control.  Through degree eight,
an independent packed extension-field oracle constructs characteristic
polynomials from Frobenius roots, tests the Lemire coefficients, and checks
whether each root lies in any maximal proper subfield; its existence result
agrees with `(ED)` without constructing `Gamma` or its differences.

Focused tests also check the prime-power classification and the implication
from the older period criterion.  The report's universal boundary is explicit:
Fourier inversion proves `(EQ)`, while nonvanishing of `(ED)` for every `n`
remains open.

## Consequences

- The characteristic-delta lane no longer spends proof effort on a condition
  stronger than necessary at mixed-divisor degrees.
- The universal obligation is one explicit nonzero product in
  `GF(2)[C_(2^n-1)]`, involving only `omega(n)` sparse translation
  differences after the existing convolution.
- This is an exact representation of Lemire, not a proof of it.  Finite
  nonvanishing and a small first witness do not grant universal theorem credit.
- At prime-power degrees the earlier least-period formulation remains exact;
  elsewhere it is retained only as a potentially convenient sufficient route.

## References

- Tuxanidy and Wang, [*A new proof of the Hansen--Mullen irreducibility
  conjecture*](https://arxiv.org/abs/1604.04023).
