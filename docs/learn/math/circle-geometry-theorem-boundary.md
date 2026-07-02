# Circle Geometry Theorem Boundary

This page separates Axeyum's finite circle-geometry resource from general
Euclidean circle theorems, tangent theorems, chord theorems,
power-of-a-point, cyclic-quadrilateral, inversion, synthetic-geometry,
projective-geometry, and numerical-geometry claims.

Primary pack:

- [finite-circle-geometry-v0](../../../artifacts/examples/math/finite-circle-geometry-v0/)

Companion lessons and maps:

- [End To End: Finite Circle Geometry](finite-circle-geometry-end-to-end.md)
- [End To End: Finite Inversion Geometry](finite-inversion-geometry-end-to-end.md)
- [End To End: Finite Cyclic Geometry](finite-cyclic-geometry-end-to-end.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack fixes exact rational coordinate witnesses. The first witness puts a
point on the unit circle:

```text
center = (0, 0)
point  = (3/5, 4/5)
r^2    = 1
```

The validator checks:

```text
(3/5)^2 + (4/5)^2 = 1
```

The tangent line at that point is:

```text
(3/5)x + (4/5)y - 1 = 0
```

and the tangent direction is perpendicular to the radius:

```text
radius            = (3/5, 4/5)
tangent direction = (-4/5, 3/5)
dot product       = 0
```

The pack also fixes a vertical chord of the radius-five circle and a horizontal
diameter of the unit circle:

```text
chord endpoints      = (3,4), (3,-4)
chord midpoint       = (3,0)
perpendicular dot    = 0

line                 = y = 0
circle intersections = (-1,0), (1,0)
right intersection   = (1,0)
```

Those rows check fixed coordinate arithmetic. They do not prove a general
coordinate-free circle theorem.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `point-on-circle-witness` | `sat` | replay-only | The point `(3/5,4/5)` is replayed on the unit circle. |
| `tangent-line-witness` | `sat` | replay-only | The tangent line contains the point and its direction has zero dot product with the radius. |
| `chord-midpoint-perpendicular-witness` | `sat` | replay-only | The fixed chord midpoint and zero perpendicular dot product are recomputed. |
| `circle-line-intersection-witness` | `sat` | replay-only | The horizontal diameter endpoints are replayed on both the line and the unit circle. |
| `bad-circle-radius-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false claim that `(1,1)` has unit radius, after replay computes squared radius `2`. |
| `bad-circle-line-intersection-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false right-intersection coordinate `2`, after replay computes `1`. |
| `general-circle-geometry-lean-horizon` | `not-run` | lean-horizon | General circle geometry, tangent theorems, power-of-a-point, cyclic quadrilaterals, and inversion remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
radius-squared value or intersection coordinate. They are not proofs of
general Euclidean circle geometry.

## What Is Not Proved Yet

The current pack does not prove:

- coordinate-free tangent-radius perpendicularity for every circle and point;
- chord perpendicular-bisector theorems in general;
- power-of-a-point, secant-tangent, or radical-axis theorems;
- cyclic quadrilateral angle, Ptolemy, or concyclicity theorems;
- inversion theorems, circle-line correspondence, or cross-ratio facts;
- projective, differential, algebraic, spherical, or hyperbolic geometry;
- construction soundness, diagrammatic reasoning, or incidence completeness;
- robust floating-point predicates, degeneracy handling, or numerical
  tolerance policies.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
circle-geometry rows are exact coordinate examples and regression seeds, not
theorem evidence for general geometry.

## Query The Boundary

Find circle-geometry theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "circle geometry" \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-circle-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-circle-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked radius and intersection contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-circle-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text radius \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-circle-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text intersection \
  --require-any
```

## Graduation Criteria

General circle-geometry resources graduate only when they add:

1. precise Lean theorem statements for tangent, chord, power-of-a-point,
   cyclic, inversion, or circle-line correspondence theorems;
2. explicit hypotheses for nondegenerate circles, points, lines, secants,
   tangents, chords, intersections, and coordinate/synthetic translations;
3. no-`sorry` proofs with an axiom audit;
4. links from finite circle packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, circle-geometry rows remain bounded/computable resources:

```text
untrusted fast search -> proposed point, tangent, chord, intersection, or malformed claim
trusted small checking -> exact coordinate/dot-product/intersection replay and Farkas evidence
theorem horizon       -> tangent, chord, power-of-a-point, cyclic, inversion, and synthetic geometry
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-circle-geometry-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text "circle geometry" --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-circle-geometry-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-circle-geometry-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-circle-geometry row remains `lean-horizon`.
