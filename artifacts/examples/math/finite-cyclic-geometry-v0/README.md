# Finite Cyclic Geometry Checks

This pack turns one exact rational cyclic quadrilateral into resource rows. It
checks a square on the unit circle, diagonal intersection and perpendicularity,
opposite right angles, one false diagonal-intersection claim, and one general
theorem horizon. It does not prove general cyclic quadrilateral theorems.

## Audience

- Learners connecting circle geometry, diagonal arithmetic, and angle checks.
- Resource authors who need a small cyclic-configuration example that is not
  just another point-on-circle row.
- Solver developers looking for exact-rational QF_LRA/Farkas rows exposed by
  finite coordinate replay.

## Checks

- `cyclic-quadrilateral-witness`: recomputes that
  `(1,0)`, `(0,1)`, `(-1,0)`, and `(0,-1)` all lie on the unit circle.
- `cyclic-diagonal-intersection-witness`: recomputes both diagonal midpoints,
  the shared intersection, both diagonal directions, and the zero dot product.
- `cyclic-opposite-right-angles-witness`: recomputes angle vectors at the
  opposite vertices `B` and `D` and checks both dot products are zero.
- `bad-cyclic-diagonal-intersection-rejected`: rejects the malformed claim that
  the diagonal intersection has x-coordinate `1/2`.
- `general-cyclic-geometry-lean-horizon`: names the future proof route for
  general cyclic quadrilateral, Ptolemy, and angle-chasing theorems.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cyclic-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_diagonal_intersection_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose a cyclic configuration, angle claim, diagonal
intersection, or general theorem instance. The trusted work is small: exact
rational coordinate replay and checked `UnsatFarkas` evidence over the source
SMT-LIB row for the final false diagonal-intersection coordinate.
