# Incidence Geometry Theorem Boundary

This page separates Axeyum's finite incidence-geometry resource from general
synthetic incidence theorems, projective-geometry theorems, configuration
theorems, duality principles, algebraic-geometry incidence claims, and
numerical-geometry claims.

Primary pack:

- [incidence-geometry-v0](../../../artifacts/examples/math/incidence-geometry-v0/)

Companion lessons and maps:

- [Incidence Geometry](incidence-geometry-end-to-end.md)
- [End To End: Coordinate And Affine Geometry](coordinate-affine-geometry-end-to-end.md)
- [Affine Geometry Theorem Boundary](affine-geometry-theorem-boundary.md)
- [Rigid Configuration Geometry](rigid-configuration-geometry-end-to-end.md)
- [Circle Geometry Theorem Boundary](circle-geometry-theorem-boundary.md)
- [Rational And Real Algebra](rational-real-algebra.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)
- [Matrix Corpus And Benchmark Boundary](matrix-corpus-benchmark-boundary.md)

## Current Finite Resource

The pack fixes exact rational line equations and points. One row commits the
line:

```text
2x - y + 1 = 0
```

and checks that `(0,1)` and `(2,5)` lie on it by direct substitution.

The intersection row fixes two non-parallel lines:

```text
x + y - 3 = 0
x - y - 1 = 0
```

The validator checks the determinant:

```text
1*(-1) - 1*1 = -2
```

and then replays the listed intersection point `(2,1)` against both line
equations. The point-on-line row checks that `(3,7)` lies on `2x - y + 1 = 0`.

Those rows are exact coordinate calculations. They do not prove projective,
synthetic, or arbitrary-plane incidence theorems.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `line-equation-through-two-points` | `sat` | replay-only | The fixed line is replayed through two fixed rational points. |
| `line-intersection-witness` | `sat` | replay-only | The two fixed non-parallel lines are replayed as intersecting at `(2,1)`. |
| `point-on-line-witness` | `sat` | replay-only | The fixed point `(3,7)` is replayed on the fixed line. |
| `bad-intersection-x-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false intersection x-coordinate `3`, after replay computes `2`. |
| `bad-incidence-rejected` | `unsat` | checked | A QF_LRA/Farkas row rejects the false claim that `(2,2)` lies on `2x - y + 1 = 0`, after replay computes line value `3`. |
| `general-incidence-geometry-lean-horizon` | `not-run` | lean-horizon | General synthetic incidence, projective duality, and configuration theorems remain future proof-assistant work. |

The checked rows are exact-linear contradictions after replay computes an
intersection coordinate or a line value. They are not proofs of general
incidence geometry.

## What Is Not Proved Yet

The current pack does not prove:

- incidence axioms for arbitrary affine or projective planes;
- projective duality between points and lines;
- Desargues, Pappus, Pascal, Brianchon, or complete-quadrangle theorems;
- arbitrary non-parallel-line intersection theorems over every field;
- synthetic diagram reasoning independent of coordinates;
- algebraic-geometry incidence bounds or polynomial-method theorems;
- degeneracy handling for coincident, parallel, or undefined line families;
- robust floating-point predicates or tolerance policies.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite
incidence-geometry rows are exact coordinate examples and regression seeds,
not theorem evidence for general geometry.

## Query The Boundary

Find incidence-geometry theorem-horizon rows and their finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "incidence geometry" \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack incidence-geometry-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite Farkas shadows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack incidence-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Drill into the checked intersection-coordinate and point-incidence
contradictions:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack incidence-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text intersection \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack incidence-geometry-v0 \
  --route Farkas \
  --proof-status checked \
  --text incidence \
  --require-any
```

## Graduation Criteria

General incidence-geometry resources graduate only when they add:

1. precise Lean theorem statements for affine-plane incidence, projective-plane
   incidence, projective duality, or named configuration theorems;
2. explicit hypotheses for fields, planes, points, lines, nondegeneracy,
   parallelism, and coordinate/synthetic translations;
3. no-`sorry` proofs with an axiom audit;
4. links from finite incidence packs to theorem statements as examples, not as
   proof evidence for the theorem;
5. display labels that keep finite replay, checked QF_LRA/Farkas evidence, and
   theorem rows separate.

Until then, incidence-geometry rows remain bounded/computable resources:

```text
untrusted fast search -> proposed line, point, intersection, or malformed incidence claim
trusted small checking -> exact line-value/intersection replay and Farkas evidence
theorem horizon       -> synthetic incidence, projective duality, and configuration theorems
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/incidence-geometry-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text "incidence geometry" --require-any
python3 scripts/query-foundational-resources.py checks --pack incidence-geometry-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack incidence-geometry-v0 --route Farkas --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
general-incidence-geometry row remains `lean-horizon`.
