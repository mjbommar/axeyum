# Finite Householder Reflection Checks

This pack records one exact rational Householder reflection for a fixed
two-dimensional vector. It is a small orthogonal-transform and
QR-building-block resource: replay the reflection formula, check symmetry and
orthogonality, zero one coordinate, reconstruct by applying the reflection
again, and reject one malformed matrix entry with checked QF_LRA/Farkas
evidence.

The trust boundary is intentionally narrow:

```text
untrusted fast search -> candidate reflector vector and reflection matrix
trusted small checking -> exact rational dot products and matrix products
proof upgrade -> QF_LRA/Farkas certificate for the false entry claim
```

It does not prove general Householder QR algorithms, pivoting policies,
least-squares theorem use, conditioning, or floating-point stability. Those
stay in Lean or numerical-honesty horizon rows.

Run it from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-householder-reflection-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_householder_reflection_bad_entry_artifact_emits_checked_farkas
```

Learner walkthrough:
[End To End: Finite Householder Reflection](../../../docs/learn/math/householder-reflection-end-to-end.md).
