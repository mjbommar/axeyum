# Linear Algebra Rational V0

This pack covers exact rational linear algebra for the `linear-algebra`
curriculum node. It uses small fixed matrices and exact replay, not floating
point and not numerical tolerances.

The examples are the first matrix-shaped shadow that will later map to Axeyum's
LRA route and Farkas evidence:

- matrix-vector solution replay for `Ax = b`;
- LU factorization replay for a fixed rational matrix;
- inconsistency of a singular linear system by an exact row-scaling certificate.

## Concepts

- `curriculum_linear_algebra`
- `curriculum_fields`
- `curriculum_rationals`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_optimization_and_convexity`

## Trust Story

The current validator parses fraction strings exactly with Python rational
arithmetic and checks matrix products, matrix-vector products, and the
inconsistency certificate. It does not yet emit SMT-LIB, call Axeyum's LRA
engine, or check Farkas certificates.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
```
