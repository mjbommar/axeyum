# Model

All probabilities and matrix entries are exact rationals written as strings
accepted by Python's `Fraction` type. A matrix-valued distribution is an atom
table:

```json
{
  "atoms": [
    {
      "id": "pp",
      "probability": "1/4",
      "matrix": [["1", "0"], ["0", "1"]]
    }
  ]
}
```

The checker rejects distributions whose atom probabilities do not sum to
exactly `1` or whose matrices have inconsistent shapes.

## Moment Checks

For the uniform distribution over diagonal sign matrices

```text
diag( 1,  1), diag( 1, -1), diag(-1,  1), diag(-1, -1)
```

the validator computes:

```text
E[tr(A)] = 0
E[tr(A)^2] = 2
E[det(A)] = 0
P(A invertible) = 1
```

## Expected Gram Matrix

For each diagonal sign matrix, `A^T A = I`, so the expected Gram matrix is also
the identity:

```text
E[A^T A] = [[1, 0],
            [0, 1]]
```

## Rank Mixture

The rank-mixture distribution contains one zero matrix, one rank-one matrix,
and one identity matrix, each with probability `1/3`. The validator computes
exact rank by rational row reduction and checks:

```text
P(rank = 0) = P(rank = 1) = P(rank = 2) = 1/3
E[rank] = 1
```

These are finite exact replay targets, not claims about asymptotic spectra or
floating-point simulation quality.

## Bad Moment Certificate

The rejected trace-square row is a one-variable exact-rational contradiction:

```text
expected_trace_square = 2
expected_trace_square = 1
```

The pack links this to a `QF_LRA` SMT-LIB artifact and a resource-backed
`UnsatFarkas` regression. The trusted path is still small: finite replay
computes the moment, and the Farkas checker rejects the incompatible claimed
moment.
