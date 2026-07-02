# Orientation And Area Geometry Theorem Boundary

This page separates Axeyum's finite orientation/area resource from general
oriented-geometry theorems, affine-volume theorems, determinant/Jacobian
change-of-variables theorems, projective orientation claims, differential
orientation on manifolds, higher-dimensional volume theorems, and
numerical-geometry claims.

Primary pack:

- [orientation-area-geometry-v0](../../../artifacts/examples/math/orientation-area-geometry-v0/)

Companion lessons and maps:

- [End To End: Coordinate And Affine Geometry](coordinate-affine-geometry-end-to-end.md)
- [Affine Geometry Theorem Boundary](affine-geometry-theorem-boundary.md)
- [Incidence Geometry Theorem Boundary](incidence-geometry-theorem-boundary.md)
- [Rigid Configuration Geometry Theorem Boundary](rigid-configuration-geometry-theorem-boundary.md)
- [Circle Geometry Theorem Boundary](circle-geometry-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md)

## Current Finite Resource

The pack fixes one exact rational triangle:

```text
A = (0,0)
B = (4,0)
C = (1,3)
```

The validator recomputes the signed double area:

```text
det(B - A, C - A) = 12
area               = 6
orientation        = counterclockwise
```

It also fixes an affine map:

```text
A = [[2, 1],
     [1, 3]]
b = [1, -1]
det(A) = 5
```

and checks one finite area-scaling row:

```text
source signed double area = 12
image signed double area  = 60
```

The barycentric row checks a single nonnegative rational combination of the
same triangle vertices. These are exact coordinate calculations. They do not
prove general oriented-geometry, affine-volume, differential, or
change-of-variables theorems.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `triangle-orientation-witness` | `sat` | replay-only | The fixed triangle's signed double area and orientation are recomputed. |
| `affine-area-scaling` | `sat` | replay-only | The fixed determinant-5 affine map scales the fixed signed double area from `12` to `60`. |
| `barycentric-point-inside` | `sat` | replay-only | The point `(9/4,3/4)` is replayed as a nonnegative barycentric combination. |
| `bad-affine-area-scaling-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false claim that the determinant-5 map preserves signed double area. |
| `bad-orientation-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false claim that a clockwise triangle is counterclockwise, after replay computes signed double area `-1`. |
| `general-oriented-geometry-lean-horizon` | `not-run` | lean-horizon | General orientation, area, affine-volume, and higher-dimensional orientation theorems remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
signed area or orientation inequality. They are not proofs of general oriented
geometry.

## What Is Not Proved Yet

The current pack does not prove:

- affine maps scale oriented area or volume in arbitrary dimensions;
- determinant sign, orientation, and basis-change theorems in general;
- general barycentric-coordinate or simplex-interior theorems;
- projective or synthetic orientation theorems;
- differential orientation, orientability, or manifold integration facts;
- Jacobian change-of-variables or Stokes/Green theorem statements;
- higher-dimensional volume and mixed-volume theorems;
- robust floating-point orientation predicates, exact geometric kernels, or
  tolerance policies.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
orientation/area rows are exact coordinate examples and regression seeds, not
theorem evidence for general geometry.

## Query The Boundary

Find oriented-geometry theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text oriented \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack orientation-area-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack orientation-area-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked area-scaling and orientation contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack orientation-area-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text area \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack orientation-area-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text orientation \
  --require-any
```

## Graduation Criteria

General orientation/area resources graduate only when they add:

1. precise Lean theorem statements for oriented area, affine volume scaling,
   determinant sign, barycentric coordinates, or change of variables;
2. explicit hypotheses for fields, dimensions, nondegenerate bases,
   simplices, affine maps, determinant signs, and coordinate translations;
3. no-`sorry` proofs with an axiom audit;
4. links from finite orientation/area packs to theorem statements as examples,
   not as proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, orientation/area rows remain bounded/computable resources:

```text
untrusted fast search -> proposed triangle, affine map, barycentric point, or malformed claim
trusted small checking -> exact signed-area/orientation replay and Farkas evidence
theorem horizon       -> oriented geometry, affine volume, change of variables, and manifold orientation
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/orientation-area-geometry-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text oriented --require-any
python3 scripts/query-foundational-resources.py checks --pack orientation-area-geometry-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack orientation-area-geometry-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-oriented-geometry row remains `lean-horizon`.
