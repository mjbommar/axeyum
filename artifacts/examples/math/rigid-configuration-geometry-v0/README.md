# Rigid Configuration Geometry V0

This pack extends the `geometry` field with exact-rational finite rigid
configuration checks. It treats small point configurations as distance tables:
candidate coordinates are untrusted, and every squared distance is recomputed
before any solver evidence is trusted.

The pack covers:

- triangle distance-table replay;
- translation isometry replay;
- congruent triangle distance replay;
- checked QF_LRA/Farkas rejection of a malformed distance table;
- a Lean-horizon row for general rigidity and rigid-motion classification
  theorems.

## Concepts

- `field_geometry`
- `field_linear_algebra`
- `field_real_analysis`
- `curriculum_reals`
- `curriculum_linear_algebra`
- `curriculum_polynomials`

## Trust Story

The validator parses all coordinates and squared distances as exact rational
strings. It recomputes pairwise squared distances, checks that the sample
triangles are nondegenerate, and verifies that translations preserve the whole
distance table.

The promoted bad row keeps the geometric computation outside the solver. Exact
replay computes a single squared distance, and the source SMT-LIB artifact
checks only the final linear contradiction through Axeyum's `UnsatFarkas`
evidence path.

This pack does not claim general graph rigidity, rigid-motion classification,
or synthetic geometry theorems.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rigid-configuration-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes rigid_configuration_bad_distance_table_artifact_emits_checked_farkas
```
