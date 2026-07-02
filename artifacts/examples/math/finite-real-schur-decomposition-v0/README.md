# Finite Real Schur Decomposition Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want an exact rational real-Schur shadow for a non-symmetric matrix. It
complements the orthogonal-diagonalization and Schur-complement packs without
claiming the general Schur theorem or numerical eigensolver stability.

It fixes one rational decomposition:

```text
Q = [  3/5  4/5 ]   T = [ 1  2 ]
    [ -4/5  3/5 ]       [ 0  4 ]

A = Q*T*Q^T = [ 97/25  54/25 ]
              [  4/25  28/25 ]
```

The trusted checker recomputes:

- `Q^T*Q = I` and `Q*Q^T = I`;
- `T` is upper triangular;
- `Q*T*Q^T = A`;
- `A*Q = Q*T`, so the first Schur vector is an eigenvector and the second
  vector has the listed triangular coupling;
- `trace(A) = sum(diag(T))`;
- `det(A) = product(diag(T))`;
- a malformed superdiagonal-entry claim, separately checked through
  QF_LRA/Farkas evidence.

The resource does not prove real Schur existence, complex Schur form,
eigenvalue ordering, multiplicity theory, QR iteration convergence,
perturbation bounds, or floating-point stability. Those remain theorem or
numerical-honesty work.

## Concept Rows

- `curriculum_linear_algebra`
- `curriculum_rationals`
- `curriculum_reals`
- `field_linear_algebra`
- `field_numerical_analysis`
- `field_functional_analysis_and_operator_theory`
- `bridge_eigenpair`
- `bridge_exact_vs_floating_arithmetic`

## Trust Boundary

```text
untrusted fast search -> candidate orthogonal basis, triangular form, or bad row
trusted small checking -> exact rational Schur replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-real-schur-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_real_schur_decomposition_bad_superdiagonal_artifact_emits_checked_farkas
```
