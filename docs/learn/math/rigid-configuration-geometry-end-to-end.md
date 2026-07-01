# End To End: Rigid Configuration Geometry

This lesson follows
[rigid-configuration-geometry-v0](../../../artifacts/examples/math/rigid-configuration-geometry-v0/)
from exact triangle distance-table replay to checked malformed translation and
distance-table claims. It is a finite coordinate resource for `field_geometry`,
not a theorem about all rigid graphs or synthetic Euclidean geometry.

Concept rows:

- `field_geometry`, `field_linear_algebra`, and `field_real_analysis` in the
  [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)
- `bridge_coordinate_orientation_geometry` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `triangle-distance-table` | `sat` | replay-only |
| `translation-isometry-witness` | `sat` | replay-only |
| `bad-translation-image-x-rejected` | `unsat` | checked QF_LRA/Farkas |
| `congruent-triangle-distance-witness` | `sat` | replay-only |
| `bad-rigid-distance-table-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-rigidity-geometry-lean-horizon` | `not-run` | lean-horizon |

Every finite row uses exact rational coordinates and squared distances.

## Replay A Distance Table

For the triangle:

```text
A = (0,0)
B = (3,0)
C = (0,4)
```

The squared distances are:

```text
AB^2 = 9
AC^2 = 16
BC^2 = 25
```

The validator recomputes each value exactly and checks that the triangle is
not degenerate.

## Replay An Isometry Shadow

Translation by `(1,-2)` sends the triangle to:

```text
A' = (1,-2)
B' = (4,-2)
C' = (1,2)
```

The target triangle has the same squared distance table. This is a finite
isometry shadow: useful as replay data, but not a proof of the full Euclidean
isometry classification theorem.

## Reject A Bad Translation Image

For source point `B = (3,0)` and translation `(1,-2)`, exact replay gives:

```text
B' = (3,0) + (1,-2) = (4,-2)
```

The malformed claim says the translated x-coordinate is `5`. The SMT-LIB
artifact isolates exactly that conflict:

```text
target_b_x = 4
target_b_x = 5
```

The geometry work is exact replay; the solver only checks the final linear
contradiction with `Evidence::UnsatFarkas`.

## Reject A Bad Distance Table

The bad row uses the segment from `(0,0)` to `(3,0)`. Exact replay gives:

```text
(3 - 0)^2 + (0 - 0)^2 = 9
```

The malformed claim says the same squared distance is `10`. The SMT-LIB
artifact isolates exactly that conflict:

```text
distance_squared = 9
distance_squared = 10
```

Axeyum must emit `Evidence::UnsatFarkas`, and the independent evidence checker
must accept it. This keeps untrusted coordinate search separate from the
trusted small certificate check.

## Horizon

This resource does not prove:

- graph rigidity or generic rigidity theorems;
- rigid-motion classification;
- synthetic rigidity diagram reasoning;
- rigidity over arbitrary fields or higher-dimensional manifolds.

Those belong in Lean-backed geometry resources or explicitly scoped
algebraic proof-certificate routes.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rigid-configuration-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes rigid_configuration_bad_translation_image_x_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes rigid_configuration_bad_distance_table_artifact_emits_checked_farkas
```

## Axeyum Identity

```text
untrusted fast search -> candidate point configurations and distance tables
trusted small checking -> exact translation/distance replay plus QF_LRA/Farkas certificate
remaining horizon -> graph rigidity and synthetic Euclidean proofs
```
