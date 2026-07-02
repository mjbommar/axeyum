# Inversion Geometry Theorem Boundary

This page separates Axeyum's finite inversion-geometry resource from general
Euclidean inversion theorems, circle-line correspondences, angle preservation,
power-of-a-point, generalized circle inversions, synthetic geometry,
projective geometry, and numerical-geometry claims.

Primary pack:

- [finite-inversion-geometry-v0](../../../artifacts/examples/math/finite-inversion-geometry-v0/)

Companion lessons and maps:

- [End To End: Finite Inversion Geometry](finite-inversion-geometry-end-to-end.md)
- [Circle Geometry Theorem Boundary](circle-geometry-theorem-boundary.md)
- [End To End: Finite Circle Geometry](finite-circle-geometry-end-to-end.md)
- [End To End: Finite Cyclic Geometry](finite-cyclic-geometry-end-to-end.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack fixes one exact rational unit-circle inversion witness:

```text
center        = (0, 0)
radius^2      = 1
point         = (2, 1)
|point|^2     = 5
scale factor  = 1/5
inverse point = (2/5, 1/5)
```

The validator checks the inversion image by exact arithmetic:

```text
I(point) = point / |point|^2 = (2/5, 1/5)
```

It also checks the finite distance-product and collinearity shadows:

```text
|point|^2             = 5
|inverse point|^2     = 1/5
radius product        = 1
dot(point, inverse)   = 1
collinearity det      = 0
```

Those rows check one fixed rational coordinate certificate. They do not prove a
general coordinate-free inversion theorem.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `inversion-image-witness` | `sat` | replay-only | The image of `(2,1)` under unit-circle inversion is replayed as `(2/5,1/5)`. |
| `inverse-distance-product-witness` | `sat` | replay-only | The squared distances of the point and inverse image multiply to `1`. |
| `inversion-collinearity-witness` | `sat` | replay-only | The center, point, and inverse image are replayed as collinear by determinant `0`. |
| `bad-inversion-image-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false inverse x-coordinate `1/2`, after replay computes `2/5`. |
| `bad-inverse-distance-product-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false squared-distance product `2`, after replay computes `1`. |
| `general-inversion-geometry-lean-horizon` | `not-run` | lean-horizon | General inversion theorems, circle-line correspondences, angle preservation, power-of-a-point, and generalized circle inversions remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
coordinate or scalar product. They are not proofs of general Euclidean
inversion geometry.

## What Is Not Proved Yet

The current pack does not prove:

- coordinate-free inversion definitions for every center, radius, and point;
- involution of inversion away from the center;
- circle-line and line-circle correspondence theorems;
- angle preservation or conformality;
- power-of-a-point, radical-axis, secant-tangent, or coaxal-family facts;
- generalized circle, Mobius, projective, spherical, or hyperbolic geometry;
- construction soundness, diagrammatic reasoning, or incidence completeness;
- robust floating-point inversion predicates, degeneracy handling, or
  tolerance policies.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
inversion-geometry rows are exact coordinate examples and regression seeds, not
theorem evidence for general geometry.

## Query The Boundary

Find inversion-geometry theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "inversion geometry" \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-inversion-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-inversion-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked inverse-coordinate and distance-product contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-inversion-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text "x-coordinate" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-inversion-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text product \
  --require-any
```

## Graduation Criteria

General inversion-geometry resources graduate only when they add:

1. precise Lean theorem statements for inversion involution, circle-line
   correspondence, angle preservation, power-of-a-point, or generalized circle
   inversion;
2. explicit hypotheses for nonzero radii, excluded centers, points, lines,
   circles, intersections, and coordinate/synthetic translations;
3. no-`sorry` proofs with an axiom audit;
4. links from finite inversion packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, inversion-geometry rows remain bounded/computable resources:

```text
untrusted fast search -> proposed inverse image, product, collinearity, or malformed claim
trusted small checking -> exact coordinate/product/determinant replay and Farkas evidence
theorem horizon       -> involution, circle-line correspondence, angle preservation, and power-of-a-point
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-inversion-geometry-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text "inversion geometry" --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-inversion-geometry-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-inversion-geometry-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-inversion-geometry row remains `lean-horizon`.
