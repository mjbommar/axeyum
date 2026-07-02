# Cyclic Geometry Theorem Boundary

This page separates Axeyum's finite cyclic-geometry resource from general
cyclic quadrilateral theorems, inscribed-angle theorems, Ptolemy, angle
chasing, circle-line correspondences, synthetic geometry, projective geometry,
and numerical-geometry claims.

Primary pack:

- [finite-cyclic-geometry-v0](../../../artifacts/examples/math/finite-cyclic-geometry-v0/)

Companion lessons and maps:

- [End To End: Finite Cyclic Geometry](finite-cyclic-geometry-end-to-end.md)
- [Circle Geometry Theorem Boundary](circle-geometry-theorem-boundary.md)
- [Inversion Geometry Theorem Boundary](inversion-geometry-theorem-boundary.md)
- [End To End: Finite Circle Geometry](finite-circle-geometry-end-to-end.md)
- [End To End: Finite Inversion Geometry](finite-inversion-geometry-end-to-end.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack fixes one exact rational square on the unit circle:

```text
center   = (0, 0)
radius^2 = 1
A        = (1, 0)
B        = (0, 1)
C        = (-1, 0)
D        = (0, -1)
```

The validator checks that every point has squared radius `1`, then replays the
diagonal intersection and opposite right-angle shadows:

```text
midpoint(A,C) = (0,0)
midpoint(B,D) = (0,0)
C - A         = (-2,0)
D - B         = (0,-2)
diagonal dot  = 0

(A - B) . (C - B) = 0
(A - D) . (C - D) = 0
```

The pack also fixes a rational `4 x 3` rectangle centered at the origin for a
finite Ptolemy shadow:

```text
side lengths     = 4, 3, 4, 3
diagonal lengths = 5, 5
Ptolemy lhs      = 25
Ptolemy rhs      = 16 + 9 = 25
```

Those rows check fixed coordinate arithmetic. They do not prove a general
coordinate-free cyclic-quadrilateral theorem.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `cyclic-quadrilateral-witness` | `sat` | replay-only | The four listed square vertices are replayed on the unit circle. |
| `cyclic-diagonal-intersection-witness` | `sat` | replay-only | The square's diagonal intersection and perpendicular diagonal dot product are recomputed. |
| `cyclic-opposite-right-angles-witness` | `sat` | replay-only | The opposite right-angle dot products at `B` and `D` are recomputed as `0`. |
| `cyclic-ptolemy-rectangle-witness` | `sat` | replay-only | The `4 x 3` cyclic rectangle is replayed and satisfies `5*5 = 4*4 + 3*3`. |
| `bad-cyclic-diagonal-intersection-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false diagonal-intersection x-coordinate `1/2`, after replay computes `0`. |
| `bad-cyclic-opposite-angle-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false angle dot product `1`, after replay computes `0`. |
| `bad-cyclic-ptolemy-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false Ptolemy right-hand side `24`, after replay computes `25`. |
| `general-cyclic-geometry-lean-horizon` | `not-run` | lean-horizon | General cyclic quadrilateral theorems, Ptolemy, angle chasing, inscribed-angle facts, and circle-line correspondences remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
coordinate, dot product, or product-sum value. They are not proofs of general
cyclic geometry.

## What Is Not Proved Yet

The current pack does not prove:

- cyclic quadrilateral characterizations for arbitrary points and circles;
- the general inscribed-angle theorem;
- Ptolemy's theorem for every cyclic quadrilateral;
- converse Ptolemy, concyclicity, or angle-chasing schemas;
- circle-line correspondence theorems or inversion/cyclic transfer theorems;
- projective, Mobius, spherical, hyperbolic, or oriented-geometry variants;
- construction soundness, diagrammatic reasoning, or incidence completeness;
- robust floating-point concyclicity predicates, degeneracy handling, or
  tolerance policies.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
cyclic-geometry rows are exact coordinate examples and regression seeds, not
theorem evidence for general geometry.

## Query The Boundary

Find cyclic-geometry theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "cyclic geometry" \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-cyclic-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-cyclic-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked diagonal, opposite-angle, and Ptolemy contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-cyclic-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text diagonal \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cyclic-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text "dot product" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-cyclic-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text Ptolemy \
  --require-any
```

## Graduation Criteria

General cyclic-geometry resources graduate only when they add:

1. precise Lean theorem statements for cyclic quadrilateral criteria,
   inscribed-angle facts, Ptolemy, converse Ptolemy, angle chasing, or
   circle-line correspondence;
2. explicit hypotheses for nondegenerate circles, distinct points, chord and
   diagonal intersections, angle orientation, and coordinate/synthetic
   translations;
3. no-`sorry` proofs with an axiom audit;
4. links from finite cyclic packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, cyclic-geometry rows remain bounded/computable resources:

```text
untrusted fast search -> proposed cyclic configuration, diagonal, angle, Ptolemy, or malformed claim
trusted small checking -> exact radius/coordinate/dot-product/product replay and Farkas evidence
theorem horizon       -> cyclic criteria, inscribed angles, Ptolemy, and circle-line correspondence
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cyclic-geometry-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text "cyclic geometry" --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-cyclic-geometry-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-cyclic-geometry-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-cyclic-geometry row remains `lean-horizon`.
