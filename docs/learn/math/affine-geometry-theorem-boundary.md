# Affine Geometry Theorem Boundary

This page separates Axeyum's finite affine-geometry resource from general
affine-space theorems, incidence theorems, ratio theorems, projective geometry,
synthetic geometry, differential geometry, and numerical-geometry claims.

Primary pack:

- [affine-geometry-v0](../../../artifacts/examples/math/affine-geometry-v0/)

Companion lessons and maps:

- [End To End: Coordinate And Affine Geometry](coordinate-affine-geometry-end-to-end.md)
- [Incidence Geometry](incidence-geometry-end-to-end.md)
- [Rigid Configuration Geometry](rigid-configuration-geometry-end-to-end.md)
- [Circle Geometry Theorem Boundary](circle-geometry-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md)
- [Analysis And Calculus Theorem Horizon Map](analysis-calculus-theorem-horizon-map.md)

## Current Finite Resource

The pack fixes one exact rational affine map:

```text
A = [[2, 1],
     [1, 3]]
b = [1, -1]
T(p) = A*p + b
```

For the point `p = (2,1)`, the validator checks:

```text
T(2,1) = (6,4)
```

For the segment from `(0,0)` to `(4,2)`, it checks that the fixed affine map
preserves the fixed midpoint:

```text
midpoint((0,0), (4,2)) = (2,1)
T(2,1)                  = (6,4)
midpoint(T(0,0), T(4,2)) = (6,4)
```

For the collinear triple `(0,0)`, `(1,1)`, `(3,3)`, the validator recomputes
the transformed determinant as `0`.

Those rows are exact coordinate calculations. They do not prove general
affine-space, incidence, projective, or synthetic-geometry theorems.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `affine-map-point-witness` | `sat` | replay-only | The fixed affine point image is replayed over exact rationals. |
| `affine-midpoint-preservation` | `sat` | replay-only | The fixed segment midpoint and the midpoint of the image segment are recomputed. |
| `affine-collinearity-preservation` | `sat` | replay-only | The fixed collinear triple has transformed determinant `0`. |
| `bad-midpoint-image-y-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false image midpoint y-coordinate `5`, after replay computes `4`. |
| `bad-collinearity-determinant-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false transformed determinant `1`, after replay computes `0`. |
| `bad-distance-preservation-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false claim that this affine map preserves a fixed squared distance. |
| `general-affine-geometry-lean-horizon` | `not-run` | lean-horizon | General affine-combination, incidence, ratio, and synthetic-geometry theorems remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
coordinate, determinant, or squared-distance value. They are not proofs of
general affine geometry.

## What Is Not Proved Yet

The current pack does not prove:

- affine maps preserve affine combinations over arbitrary vector spaces;
- incidence preservation for every affine subspace, line, and flat;
- ratio, parallelism, or barycentric-coordinate theorems in general;
- projective completions, cross-ratio facts, or duality principles;
- synthetic-geometry theorem schemas independent of coordinates;
- Euclidean isometry facts for arbitrary affine maps;
- differential, algebraic, global, or higher-dimensional geometry;
- robust floating-point predicates, degeneracy handling, or tolerance
  policies.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
affine-geometry rows are exact coordinate examples and regression seeds, not
theorem evidence for general geometry.

## Query The Boundary

Find affine-geometry theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "affine geometry" \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack affine-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack affine-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked midpoint, collinearity, and distance contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack affine-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text midpoint \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack affine-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text collinearity \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack affine-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text distance \
  --require-any
```

## Graduation Criteria

General affine-geometry resources graduate only when they add:

1. precise Lean theorem statements for affine-combination preservation,
   incidence preservation, ratios, parallelism, or affine-space maps;
2. explicit hypotheses for base fields, vector spaces, affine spaces, flats,
   nondegenerate points, and coordinate translations;
3. no-`sorry` proofs with an axiom audit;
4. links from finite affine packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, affine-geometry rows remain bounded/computable resources:

```text
untrusted fast search -> proposed affine image, midpoint, determinant, distance, or malformed claim
trusted small checking -> exact coordinate/determinant/distance replay and Farkas evidence
theorem horizon       -> affine-combination, incidence, ratio, projective, and synthetic geometry
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/affine-geometry-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text "affine geometry" --require-any
python3 scripts/query-foundational-resources.py checks --pack affine-geometry-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack affine-geometry-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-affine-geometry row remains `lean-horizon`.
