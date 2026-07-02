# Rigid Configuration Geometry Theorem Boundary

This page separates Axeyum's finite rigid-configuration resource from general
graph rigidity, rigid-motion classification, synthetic Euclidean rigidity,
higher-dimensional rigidity, manifold rigidity, and numerical-geometry claims.

Primary pack:

- [rigid-configuration-geometry-v0](../../../artifacts/examples/math/rigid-configuration-geometry-v0/)

Companion lessons and maps:

- [Rigid Configuration Geometry](rigid-configuration-geometry-end-to-end.md)
- [End To End: Coordinate And Affine Geometry](coordinate-affine-geometry-end-to-end.md)
- [Incidence Geometry Theorem Boundary](incidence-geometry-theorem-boundary.md)
- [Affine Geometry Theorem Boundary](affine-geometry-theorem-boundary.md)
- [Circle Geometry Theorem Boundary](circle-geometry-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md)

## Current Finite Resource

The pack fixes one exact rational triangle:

```text
A = (0,0)
B = (3,0)
C = (0,4)
```

The validator recomputes the squared distance table:

```text
AB^2 = 9
AC^2 = 16
BC^2 = 25
```

It also checks one finite isometry shadow: translation by `(1,-2)` sends the
triangle to `(1,-2)`, `(4,-2)`, and `(1,2)` while preserving the same squared
distance table. A second replay row compares two fixed congruent triangles by
their distance tables.

Those rows are exact coordinate calculations. They do not prove graph
rigidity, generic rigidity, rigid-motion classification, or synthetic
Euclidean geometry.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `triangle-distance-table` | `sat` | replay-only | The fixed `3-4-5` triangle distance table is recomputed over exact rationals. |
| `translation-isometry-witness` | `sat` | replay-only | The fixed translation is replayed and the source/target distance tables match. |
| `congruent-triangle-distance-witness` | `sat` | replay-only | Two fixed triangles are replayed as having the same squared-distance table. |
| `bad-translation-image-x-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false translated x-coordinate `5`, after replay computes `4`. |
| `bad-rigid-distance-table-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false squared distance `10`, after replay computes `9`. |
| `general-rigidity-geometry-lean-horizon` | `not-run` | lean-horizon | General graph rigidity, rigid-motion classification, and synthetic rigidity theorems remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes a
coordinate or squared distance. They are not proofs of general rigidity
theory.

## What Is Not Proved Yet

The current pack does not prove:

- generic rigidity or global rigidity of arbitrary graphs;
- Laman-style rigidity criteria or rigidity matroid theorems;
- complete rigid-motion classification in the Euclidean plane;
- congruence theorems for arbitrary point configurations;
- synthetic triangle congruence or construction soundness;
- higher-dimensional, manifold, or non-Euclidean rigidity;
- algebraic-geometric rigidity varieties or rank conditions in general;
- robust floating-point distance predicates, degeneracy handling, or
  tolerance policies.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
rigid-configuration rows are exact coordinate examples and regression seeds,
not theorem evidence for general rigidity.

## Query The Boundary

Find rigidity theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text rigidity \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack rigid-configuration-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack rigid-configuration-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked translation-image and distance-table contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack rigid-configuration-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text translation \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack rigid-configuration-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text distance \
  --require-any
```

## Graduation Criteria

General rigidity resources graduate only when they add:

1. precise Lean theorem statements for graph rigidity, global rigidity,
   rigid-motion classification, congruence, or synthetic rigidity;
2. explicit hypotheses for fields, dimensions, point configurations,
   nondegeneracy, graph edges, and coordinate/synthetic translations;
3. no-`sorry` proofs with an axiom audit;
4. links from finite rigid-configuration packs to theorem statements as
   examples, not as proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, rigid-configuration rows remain bounded/computable resources:

```text
untrusted fast search -> proposed coordinates, translation, distance table, or malformed claim
trusted small checking -> exact coordinate/distance replay and Farkas evidence
theorem horizon       -> graph rigidity, rigid-motion classification, and synthetic rigidity
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rigid-configuration-geometry-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text rigidity --require-any
python3 scripts/query-foundational-resources.py checks --pack rigid-configuration-geometry-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack rigid-configuration-geometry-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-rigidity-geometry row remains `lean-horizon`.
