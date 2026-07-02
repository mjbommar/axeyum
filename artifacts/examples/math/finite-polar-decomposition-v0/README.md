# Finite Polar Decomposition Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want an exact rational polar-decomposition shadow for one fixed matrix. It
connects orthogonal-transform, singular-value, and numerical linear-algebra
resources without claiming the general polar decomposition theorem or numerical
algorithm stability.

It fixes one rational decomposition:

```text
U = [  3/5  4/5 ]   P = [ 2  0 ]
    [ -4/5  3/5 ]       [ 0  5 ]

A = U*P = [  6/5  4 ]
          [ -8/5  3 ]
```

The trusted checker recomputes:

- `U^T*U = I` and `U*U^T = I`;
- `P` is symmetric positive diagonal;
- `U*P = A`;
- `A^T*A = P^2`;
- `det(A) = det(U)*det(P)`;
- a malformed positive-factor diagonal claim, separately checked through
  QF_LRA/Farkas evidence.

The resource does not prove polar decomposition existence or uniqueness, square
root functional calculus, SVD theorem coverage, condition-number perturbation
theory, iterative polar algorithms, or floating-point stability. Those remain
theorem or numerical-honesty work.

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
untrusted fast search -> candidate orthogonal factor, positive factor, or bad row
trusted small checking -> exact rational polar replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-polar-decomposition-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_polar_decomposition_bad_diagonal_artifact_emits_checked_farkas
```
