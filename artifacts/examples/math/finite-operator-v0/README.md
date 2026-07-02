# Finite Operator V0

This pack covers finite-dimensional normed-space and operator examples for the
`functional_analysis_and_operator_theory` field-extension row. It uses exact
rational vectors, matrices, and polynomial recurrence values; it does not claim
general Banach-space or Hilbert-space theorems.

The examples are the bounded finite slice that Axeyum can eventually encode as
small LRA/NRA/BV obligations:

- an `l1` norm triangle witness;
- a malformed finite-dimensional `l1` norm replay row plus a separate
  QF_LRA/Farkas contradiction row;
- an infinity-norm matrix operator bound via the row-sum norm;
- a malformed finite-dimensional operator-bound replay row plus a separate
  QF_LRA/Farkas contradiction row;
- a Chebyshev polynomial recurrence witness at a fixed rational point;
- a malformed finite Chebyshev-prefix replay row plus a separate
  QF_LRA/Farkas contradiction row.

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
products, row-sum operator norms, the bad norm/bound/prefix source data, and the
Chebyshev recurrence `T(n+1) = 2*x*T(n) - T(n-1)`.

The malformed norm, operator-bound, and Chebyshev-prefix rows are replay-only:
exact replay computes `||u+v||_1 = 5`, `||A*x||_infty = 3`, and `T3(1/2) = -1`,
rejecting claimed values `4`, `2`, and `-1/2`. The separate `qf-lra-*` rows own
the checked proof-object route, parsing the source SMT-LIB artifacts and
requiring rechecked `UnsatFarkas` certificates for the final scalar
contradictions. General normed-space theorems, compact operators, approximation
theorems, and Chebyshev-space theorems remain Lean-horizon material.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_l1_sum_norm_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_operator_bound_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_chebyshev_t3_artifact_emits_checked_farkas
```
