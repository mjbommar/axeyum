# Finite Inversion Geometry Checks

This pack turns one exact rational circle-inversion calculation into resource
rows. It checks a unit-circle inversion image, the inverse-distance product,
collinearity with the center, false inverse-coordinate and distance-product
claims, and one general theorem horizon. It does not prove general inversion
geometry.

## Audience

- Learners connecting circle inversion, rational coordinate arithmetic, and
  finite polynomial geometry.
- Resource authors who need a small exact-rational inversion example with a
  checked linearized contradiction.
- Solver developers looking for QF_LRA/Farkas rows exposed by replaying a
  nonlinear geometry computation first.

## Checks

- `inversion-image-witness`: checks that inversion in the unit circle maps
  `(2,1)` to `(2/5,1/5)`.
- `inverse-distance-product-witness`: checks that the squared radii of a point
  and its inverse multiply to `1`.
- `inversion-collinearity-witness`: checks that the center, point, and inverse
  point are collinear.
- `bad-inversion-image-rejected`: rejects the malformed claim that the inverse
  x-coordinate is `1/2`.
- `bad-inverse-distance-product-rejected`: rejects the malformed claim that the
  squared-distance product is `2`.
- `general-inversion-geometry-lean-horizon`: names the future proof route for
  coordinate-free inversion theorems.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-inversion-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_inversion_geometry_bad_inverse_x_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_inversion_geometry_bad_inverse_distance_product_artifact_emits_checked_farkas
```

## Trust Boundary

Untrusted search may propose a point, inverse image, or inversion theorem
instance. The trusted work is small: exact rational coordinate replay and
checked `UnsatFarkas` evidence over the source SMT-LIB rows for final false
inverse-coordinate and distance-product claims.
