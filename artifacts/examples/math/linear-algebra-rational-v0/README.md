# Linear Algebra Rational V0

This pack covers exact rational linear algebra for the `linear-algebra`
curriculum node. It uses small fixed matrices and exact replay, not floating
point and not numerical tolerances.

The examples are the first matrix-shaped shadow that will later map to Axeyum's
LRA route and Farkas evidence:

- matrix-vector solution replay for `Ax = b`;
- LU factorization replay for a fixed rational matrix;
- inconsistency of a singular linear system by exact row-scaling replay and
  checked Farkas evidence.

## Concepts

- `curriculum_linear_algebra`
- `curriculum_fields`
- `curriculum_rationals`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_optimization_and_convexity`

## Trust Story

The validator parses fraction strings exactly with Python rational arithmetic
and checks matrix products, matrix-vector products, and the row-scaling
inconsistency certificate. The singular-system row also has an Axeyum
regression that builds the `QF_LRA` equations, emits `UnsatFarkas` evidence,
and rechecks that evidence independently. The same row now also carries a
source-level SMT-LIB artifact that the route regression parses before checking
Farkas evidence. The SAT witness rows remain exact replay-only until they route
through model evidence.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes linear_algebra_singular_system
```
