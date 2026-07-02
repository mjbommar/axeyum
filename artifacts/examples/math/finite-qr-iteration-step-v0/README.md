# Finite QR Iteration Step Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want one exact rational unshifted QR-iteration step. It sits between the QR
decomposition, real-Schur, and eigensolver resources without claiming QR
iteration convergence, shift strategy correctness, loss-of-orthogonality
bounds, or floating-point stability.

It fixes one rational QR factorization:

```text
Q = [  3/5  4/5 ]   R = [ 5  2 ]
    [ -4/5  3/5 ]       [ 0  1 ]

A0 = Q*R = [  3   2 ]
           [ -4  -1 ]

A1 = R*Q = Q^T*A0*Q
   = [  7/5  26/5 ]
     [ -4/5   3/5 ]
```

The trusted checker recomputes:

- `Q^T*Q = I` and `Q*Q^T = I`;
- `R` is upper triangular;
- `Q*R = A0`;
- `R*Q = A1`;
- `Q^T*A0*Q = A1`;
- `trace(A0) = trace(A1)` and `det(A0) = det(A1)`;
- a malformed next-step entry claim, separately checked through
  QF_LRA/Farkas evidence.

The resource does not prove general QR iteration convergence, Schur form
existence, shift selection, deflation, Hessenberg reduction correctness,
roundoff behavior, or floating-point eigensolver stability. Those remain
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
untrusted fast search -> candidate QR step, similarity row, or bad entry
trusted small checking -> exact rational QR-step replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-qr-iteration-step-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_qr_iteration_step_bad_entry_artifact_emits_checked_farkas
```
