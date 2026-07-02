# Finite Arnoldi Iteration Checks

This pack records one exact rational Arnoldi transcript for a fixed two-by-two
matrix. It is a small Krylov-subspace resource for linear algebra and
numerical-analysis learners: replay the first Arnoldi projection, check the
orthonormal basis, form the Hessenberg matrix, and reject one malformed
subdiagonal coefficient with checked QF_LRA/Farkas evidence.

The trust boundary is intentionally narrow:

```text
untrusted fast search -> candidate basis, coefficients, and Hessenberg matrix
trusted small checking -> exact rational dot products and matrix products
proof upgrade -> QF_LRA/Farkas certificate for the false h21 claim
```

It does not prove general Arnoldi convergence, Ritz value theory, restarted
GMRES behavior, reorthogonalization correctness, loss-of-orthogonality bounds,
or floating-point Krylov stability. Those stay in Lean or numerical-honesty
horizon rows.

Run it from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-arnoldi-iteration-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_arnoldi_iteration_bad_h21_artifact_emits_checked_farkas
```

Learner walkthrough:
[End To End: Finite Arnoldi Iteration](../../../docs/learn/math/arnoldi-iteration-end-to-end.md).
