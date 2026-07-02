# Finite Givens Rotation Checks

This pack records one exact rational Givens rotation for a fixed two-dimensional
vector. It is a small orthogonal-transform and QR-building-block resource:
replay the rotation, check orthogonality, zero one coordinate, reconstruct with
the transpose, and reject one malformed sine coefficient with checked
QF_LRA/Farkas evidence.

The trust boundary is intentionally narrow:

```text
untrusted fast search -> candidate cosine/sine coefficients and rotation matrix
trusted small checking -> exact rational dot products and matrix products
proof upgrade -> QF_LRA/Farkas certificate for the false sine claim
```

It does not prove general Givens QR algorithms, pivoting policies,
least-squares theorem use, conditioning, or floating-point stability. Those
stay in Lean or numerical-honesty horizon rows.

Run it from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-givens-rotation-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_givens_rotation_bad_sine_artifact_emits_checked_farkas
```

Learner walkthrough:
[End To End: Finite Givens Rotation](../../../docs/learn/math/givens-rotation-end-to-end.md).
