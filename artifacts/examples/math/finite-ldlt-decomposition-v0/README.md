# Finite LDLT Decomposition Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want an exact rational positive-definite factorization that avoids square roots.
It complements the Cholesky and Schur-complement packs without claiming a
general numerical algorithm or stability theorem.

It fixes one rational two-by-two system:

```text
A = [ 4  2 ]   L = [ 1    0 ]   D = [ 4  0 ]
    [ 2  3 ]       [ 1/2  1 ]       [ 0  2 ]
```

The trusted checker recomputes:

- `A` is symmetric;
- `L` is unit lower triangular;
- `D` is diagonal;
- `L*D*L^T = A`;
- `det(A) = product(diag(D))`;
- the leading principal minors are positive;
- the triangular solve `L*z = b`, `D*y = z`, `L^T*x = y`, and `A*x = b`;
- a malformed diagonal-entry claim, separately checked through QF_LRA/Farkas
  evidence.

The resource does not prove LDLT existence, pivoted LDLT, indefinite
factorization policy, rank-deficient behavior, sparse factorization,
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
untrusted fast search -> candidate symmetric factors, pivots, solves, or bad row
trusted small checking -> exact rational LDLT replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-ldlt-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_ldlt_decomposition_bad_diagonal_artifact_emits_checked_farkas
```
