# Finite Circle Geometry Checks

This pack turns exact rational circle-geometry calculations into resource rows.
It checks one point-on-circle witness, one tangent-line witness, one chord
midpoint/perpendicularity witness, one false circle-radius claim, and one
general theorem horizon. It does not prove general Euclidean circle theorems.

## Audience

- Learners connecting coordinate geometry, quadratic distance equations, and
  tangent-line arithmetic.
- Resource authors who need a small polynomial-geometry example with a checked
  linearized contradiction.
- Solver developers looking for exact-rational QF_LRA/Farkas rows after finite
  coordinate replay.

## Checks

- `point-on-circle-witness`: recomputes the squared distance from the center to
  `(3/5,4/5)` and checks it equals the unit radius squared.
- `tangent-line-witness`: checks the tangent line
  `(3/5)x + (4/5)y - 1 = 0`, the radius vector, and perpendicular tangent
  direction.
- `chord-midpoint-perpendicular-witness`: checks that the midpoint of a
  vertical chord is perpendicular to the radius through the midpoint.
- `bad-circle-radius-rejected`: rejects the malformed claim that `(1,1)` lies
  on the unit circle.
- `general-circle-geometry-lean-horizon`: names the future proof route for
  general circle geometry, tangent theorems, and Euclidean geometry facts.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-circle-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_circle_geometry_bad_radius_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose a point, line, tangent direction, or chord table.
The trusted work is small: exact rational coordinate replay and checked
`UnsatFarkas` evidence over the source SMT-LIB row for the final false
radius-squared claim.
