# ADR-0533: Reject root-number-only control of the endpoint Hayes trace

Status: accepted
Date: 2026-08-20
Index-summary: Use exact integral cyclotomic arithmetic to prove that primitive Hayes characters with the same functional-equation root number have different endpoint power sums

## Context

The selected connected target retains the signed sum of the high power sums of
all Hayes characters in a logarithmic top-conductor window.  A possible
characteristic-two analogue of the primitive/imprimitive Gauss-sum strategy
would be useful only if the functional-equation root number controlled those
power sums.  For a primitive level-`j` binary Hayes character, its
`L`-polynomial has degree `j-1`, and its leading coefficient determines the
root number.  The endpoint power is near `2j`, however, and can depend on the
whole `L`-polynomial.

## Decision

Add `hayes_root_number_fibre_report`.  It constructs every coefficient of the
primitive Hayes `L`-polynomials in the exact integral basis

```text
1, zeta, ..., zeta^(phi-1)  in Z[zeta],
```

for a power-of-two root of unity `zeta`.  It computes logarithmic power sums by
the exact coefficient recurrence, groups primitive characters by their common
leading coefficient, and searches for distinct power sums inside a group.
Every integral result is also reduced through both independent NTT primes and
must agree with the existing character-power-sum transform.  Because the
direct audit has quadratic work in the character-group order, admission prices
`4^level` exact work cells against the caller's explicit table-cell ceiling and
declines before either transform or cyclotomic enumeration.  For every
primitive character the same integral coefficients must also satisfy

```text
2^k A_(d-k) = A_d conjugate(A_k)  (0 <= k <= d),
```

the coefficientwise functional equation.  This verifies inside the report
that the common leading coefficient really fixes the common root number.

At `(level,degree)=(5,11)`, all `16` primitive characters lie in six
leading-coefficient fibres, and every one of the six fibres contains more than
one endpoint power sum.  The first pinned witness is

```text
characters:            26 and 30
common leading term:   -4
power sum at degree 11: -32 + 32 zeta_8^2
                        -32 - 32 zeta_8^2.
```

Thus two characters with the same functional-equation root number contribute
different high traces.

## Consequences

- A characteristic-two primitive Gauss-sum formula that supplies only root
  numbers cannot determine or bound the connected endpoint trace.
- This does not reject a formula retaining the full Hayes `L`-coefficient
  vector, nor cancellation after summing those vectors across characters.
- Cyclotomic zeta factorization does not add that cancellation: its logarithmic
  derivative is the sum of the same individual character power sums.  The
  open route remains a genuinely signed full-coefficient/Witt average or the
  connected fourth-cumulant/gcd stratification.
- The report is a bounded exact obstruction and gives no Lemire theorem credit.
