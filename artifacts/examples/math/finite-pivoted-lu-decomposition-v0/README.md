# Finite Pivoted LU Decomposition Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want a tiny exact row-pivoting example without claiming a general pivoting
algorithm or numerical stability theorem.

It fixes one rational two-by-two system:

```text
A = [ 1  2 ]   P = [ 0  1 ]   P A = [ 3  4 ]
    [ 3  4 ]       [ 1  0 ]         [ 1  2 ]

L = [ 1    0 ]   U = [ 3   4  ]
    [ 1/3  1 ]       [ 0  2/3 ]
```

The trusted checker recomputes:

- `P` is a row-swap permutation matrix;
- `P*A` and `P*b`;
- the unit lower-triangular shape of `L`;
- the upper-triangular shape of `U`;
- the product `L*U = P*A`;
- the determinant relation `det(P) * det(A) = product(pivots)`;
- forward/back substitution for `A*x = b`;
- a malformed permutation-sign claim, separately checked through QF_LRA/Farkas
  evidence.

The resource does not prove partial-pivoting correctness, complete pivoting,
rank-deficient behavior, sparse pivot policies, growth-factor bounds,
conditioning, or floating-point stability. Those remain theorem or
numerical-honesty work.

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
untrusted fast search -> candidate permutation, factors, pivots, or bad sign
trusted small checking -> exact rational pivoted factorization replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-pivoted-lu-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_pivoted_lu_decomposition_bad_pivot_sign_artifact_emits_checked_farkas
```
