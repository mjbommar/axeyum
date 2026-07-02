# Finite LU Decomposition Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want a focused exact LU factorization transcript separated from the older broad
linear-system pack.

It fixes one rational two-by-two system:

```text
A = [ 2  1 ]   L = [ 1  0 ]   U = [ 2  1 ]
    [ 4  5 ]       [ 2  1 ]       [ 0  3 ]

b = [5, 17]
```

The trusted checker recomputes:

- the unit lower-triangular shape of `L`;
- the upper-triangular shape of `U`;
- the product `L U = A`;
- the determinant/pivot product `2 * 3 = 6`;
- forward and back substitution for `A*x = b`;
- a malformed multiplier claim, separately checked through QF_LRA/Farkas
  evidence.

The resource does not prove general LU existence, pivoting correctness,
rank-deficient behavior, sparse factorization behavior, conditioning, or
floating-point stability. Those remain theorem or numerical-honesty work.

## Concept Rows

- `curriculum_linear_algebra`
- `curriculum_rationals`
- `curriculum_reals`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_optimization_and_convexity`
- `bridge_lu_replay`

## Trust Boundary

```text
untrusted fast search -> candidate L/U factors, pivots, or malformed multiplier
trusted small checking -> exact rational factorization replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-lu-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_lu_decomposition_bad_multiplier_artifact_emits_checked_farkas
```
