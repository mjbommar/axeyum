# Finite Gram-Schmidt Checks

This pack records one exact rational Gram-Schmidt transcript for two fixed
two-dimensional columns. It is a small inner-product and QR-building-block
resource: replay the first normalization, replay the projection coefficient,
check the residual and second normalization, check orthonormality, check the
upper-triangular factor, check `Q*R = A`, and reject one malformed projection
coefficient with checked QF_LRA/Farkas evidence.

The trust boundary is intentionally narrow:

```text
untrusted fast search -> candidate projection coefficient, Q, and R
trusted small checking -> exact rational dot products and matrix products
proof upgrade -> QF_LRA/Farkas certificate for the false r12 claim
```

It does not prove general Gram-Schmidt or QR correctness, rank-deficient
variants, least-squares theorem use, conditioning, or floating-point
stability. Those stay in Lean or numerical-honesty horizon rows.

Run it from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-gram-schmidt-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gram_schmidt_bad_r12_artifact_emits_checked_farkas
```

Learner walkthrough:
[End To End: Finite Gram-Schmidt](../../../docs/learn/math/gram-schmidt-end-to-end.md).
