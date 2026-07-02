# Finite Shifted QR Step Checks

This pack is for learners, solver contributors, and proof-route reviewers who
want one exact rational shifted QR step. It extends the unshifted QR-step
resource with an explicit shift parameter while still avoiding claims about
QR-iteration convergence, shift selection, deflation, roundoff, or
floating-point eigensolver stability.

It fixes one rational shifted factorization with `mu = 1`:

```text
Q = [  3/5  4/5 ]   R = [ 5  2 ]
    [ -4/5  3/5 ]       [ 0  1 ]

A0 = Q*R + mu*I = [  4  2 ]
                  [ -4  0 ]

A1 = R*Q + mu*I = Q^T*A0*Q
   = [ 12/5  26/5 ]
     [ -4/5   8/5 ]
```

The trusted checker recomputes:

- `Q^T*Q = I` and `Q*Q^T = I`;
- `R` is upper triangular;
- `A0 - mu*I = Q*R`;
- `A1 = R*Q + mu*I`;
- `Q^T*A0*Q = A1`;
- `trace(A0) = trace(A1)` and `det(A0) = det(A1)`;
- a malformed shifted-step entry claim, separately checked through
  QF_LRA/Farkas evidence.

The resource does not prove that a shift is well chosen, that QR iteration
converges, that deflation is correct, or that a floating-point implementation
is stable. Those remain theorem or numerical-honesty work.

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
untrusted fast search -> candidate shifted QR step, shift row, or bad entry
trusted small checking -> exact rational shifted-step replay and checked Farkas evidence
```

The pack validates with:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-shifted-qr-step-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_shifted_qr_step_bad_entry_artifact_emits_checked_farkas
```
