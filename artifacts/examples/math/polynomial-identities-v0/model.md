# Model

Polynomials are coefficient lists in increasing degree order:

```text
[a0, a1, a2]  means  a0 + a1*x + a2*x^2
```

All coefficients and evaluation points are exact rational strings. The validator
normalizes trailing zeros before comparing polynomials, so `[1, 2, 1]` and
`[1, 2, 1, 0]` denote the same polynomial.

The pack currently checks three operations:

```text
multiply coefficient lists
evaluate at an exact rational point
compare normalized coefficient vectors
```

## Axeyum Route

The intended Axeyum route is fixed-degree exact arithmetic: either rational
arithmetic over an NRA/LRA shadow for coefficient replay, QF_LIA/Diophantine
evidence for integer coefficient contradictions, or bounded BV enumeration for
finite coefficient domains. The false-root row is now source-linked to the
QF_LIA/Diophantine route; the positive rows remain independent replay checks.
