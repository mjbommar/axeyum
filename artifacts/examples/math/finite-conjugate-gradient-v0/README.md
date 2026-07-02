# Finite Conjugate Gradient Checks

This pack records one exact rational two-step conjugate-gradient transcript for
the fixed symmetric positive-definite system:

```text
A = [[4, 1],
     [1, 3]]
b = [1, 2]
x0 = [0, 0]
```

The checked slice is deliberately small:

- replay `r0 = b - A*x0` and `p0 = r0`;
- replay the first step size `alpha0 = 1/4`;
- replay `x1`, `r1`, residual orthogonality, `beta0`, and `p1`;
- replay A-conjugacy `p0^T*A*p1 = 0`;
- replay the second step to the exact solution `[1/11, 7/11]`;
- reject the false first step-size claim `alpha0 = 1/3`;
- check the corresponding `QF_LRA` contradiction through Farkas evidence.

It does not claim general CG convergence, finite termination, preconditioner
correctness, Krylov theory, roundoff behavior, or floating-point stability.

Run from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-conjugate-gradient-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_conjugate_gradient_bad_alpha0_artifact_emits_checked_farkas
```
