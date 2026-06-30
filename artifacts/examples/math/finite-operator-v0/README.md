# Finite Operator V0

This pack covers finite-dimensional normed-space and operator examples for the
`functional_analysis_and_operator_theory` field-extension row. It uses exact
rational vectors, matrices, and polynomial recurrence values; it does not claim
general Banach-space or Hilbert-space theorems.

The examples are the bounded finite slice that Axeyum can eventually encode as
small LRA/NRA/BV obligations:

- an `l1` norm triangle witness;
- an infinity-norm matrix operator bound via the row-sum norm;
- a malformed finite-dimensional operator-bound row checked through
  QF_LRA/Farkas evidence;
- a Chebyshev polynomial recurrence witness at a fixed rational point.

## Concepts

- `field_functional_analysis_and_operator_theory`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_real_analysis`
- `curriculum_linear_algebra`
- `curriculum_reals`
- `curriculum_polynomials`

## Trust Story

The validator parses every vector, matrix entry, norm, and polynomial value as
an exact rational string. It recomputes vector sums, norms, matrix-vector
products, row-sum operator norms, the bad-bound source data, and the Chebyshev
recurrence `T(n+1) = 2*x*T(n) - T(n-1)`.

The malformed operator-bound row is checked by the QF_LRA/Farkas route after
exact replay computes `||A*x||_infty = 3` and rejects the claimed upper bound
`2`. General normed-space theorems, compact operators, approximation theorems,
and Chebyshev-space theorems remain Lean-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
```
