# Linear Algebra Rational V0

This pack covers exact rational linear algebra for the `linear-algebra`
curriculum node. It uses small fixed matrices and exact replay, not floating
point and not numerical tolerances.

The examples are the first matrix-shaped shadow that will later map to Axeyum's
LRA route and Farkas evidence:

- matrix-vector solution replay for `Ax = b`;
- LU factorization replay for a fixed rational matrix;
- checked rejection of a malformed LU product entry;
- checked rejection of a malformed nullspace component;
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
and checks matrix products, matrix-vector products, nullspace products, and the
row-scaling inconsistency certificate. The bad LU row recomputes `L*U`
exactly, isolates the bottom-right product entry `3`, and rejects the malformed
claim that the same entry is `4`. The bad nullspace row recomputes `A*v = 0`
exactly, isolates the false component claim, and checks a source QF_LRA/Farkas
artifact where the same first component is `1`. The singular-system, bad
nullspace, and bad LU rows also have Axeyum regressions that parse source-level
SMT-LIB artifacts, emit `UnsatFarkas` evidence, and recheck that evidence
independently. The SAT witness rows remain exact replay-only until they route
through model evidence.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
cargo test -p axeyum-solver --test math_resource_lra_routes linear_algebra_singular_system
cargo test -p axeyum-solver --test math_resource_lra_routes linear_algebra_bad_lu_product_entry_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes linear_algebra_bad_nullspace_component_artifact_emits_checked_farkas
```
