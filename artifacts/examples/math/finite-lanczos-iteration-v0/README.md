# Finite Lanczos Iteration Checks

This pack records one exact rational Lanczos transcript for a fixed two-by-two
symmetric matrix. It is a small Krylov-subspace resource for linear algebra and
numerical-analysis learners: replay the first two Lanczos steps, check the
orthonormal basis, form the symmetric tridiagonal matrix, and reject one
malformed off-diagonal coefficient with checked QF_LRA/Farkas evidence.

The trust boundary is intentionally narrow:

```text
untrusted fast search -> candidate basis, alpha/beta coefficients, and tridiagonal matrix
trusted small checking -> exact rational dot products and matrix products
proof upgrade -> QF_LRA/Farkas certificate for the false beta1 claim
```

It does not prove general Lanczos convergence, Ritz value theory, breakdown or
restart behavior, finite-precision loss-of-orthogonality bounds, or
floating-point Krylov stability. Those stay in Lean or numerical-honesty
horizon rows.

Run it from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-lanczos-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_lanczos_iteration_bad_beta1_artifact_emits_checked_farkas
```

Learner walkthrough:
[End To End: Finite Lanczos Iteration](../../../docs/learn/math/lanczos-iteration-end-to-end.md).
