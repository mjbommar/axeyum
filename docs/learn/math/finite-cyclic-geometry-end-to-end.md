# Finite Cyclic Geometry Checks

This lesson follows
[finite-cyclic-geometry-v0](../../../artifacts/examples/math/finite-cyclic-geometry-v0/)
from exact coordinate replay through checked Farkas contradictions. It is a
finite rational coordinate certificate, not a proof of general cyclic
quadrilateral geometry.

## Concept

A cyclic quadrilateral has all vertices on one circle. This resource uses a
fixed square on the unit circle for diagonal and angle rows:

```text
A = (1,0)
B = (0,1)
C = (-1,0)
D = (0,-1)
```

It also uses a rational `4 x 3` rectangle for a finite Ptolemy shadow. Because
all values are rational, the checker can replay the circle membership,
diagonal, angle, and product-sum claims without diagrams or floating-point
tolerances.

## What Gets Checked

| Row | Result | Evidence |
|---|---|---|
| `cyclic-quadrilateral-witness` | `sat` | replay-only |
| `cyclic-diagonal-intersection-witness` | `sat` | replay-only |
| `cyclic-opposite-right-angles-witness` | `sat` | replay-only |
| `cyclic-ptolemy-rectangle-witness` | `sat` | replay-only |
| `bad-cyclic-diagonal-intersection-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-cyclic-opposite-angle-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-cyclic-ptolemy-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-cyclic-geometry-lean-horizon` | `not-run` | Lean horizon |

## Cyclic Witness

The validator checks that every point is on the unit circle:

```text
|A|^2 = 1^2 + 0^2 = 1
|B|^2 = 0^2 + 1^2 = 1
|C|^2 = (-1)^2 + 0^2 = 1
|D|^2 = 0^2 + (-1)^2 = 1
```

This is the finite cyclic-configuration part. It proves only this listed
configuration is cyclic.

## Diagonal Intersection

The diagonals are `AC` and `BD`. Their midpoints are:

```text
midpoint(A,C) = (0,0)
midpoint(B,D) = (0,0)
```

So the pack records the diagonal intersection as `(0,0)`. It also checks the
diagonal directions:

```text
C - A = (-2,0)
D - B = (0,-2)
(-2,0) . (0,-2) = 0
```

The fixed diagonals are perpendicular.

## Opposite Right Angles

At `B`, the two vectors are:

```text
A - B = (1,-1)
C - B = (-1,-1)
```

Their dot product is zero. At `D`, the vectors are:

```text
A - D = (1,1)
C - D = (-1,1)
```

Their dot product is also zero. The pack checks these exact angle witnesses for
the fixed square; it does not prove the general inscribed-angle theorem.

The checked bad opposite-angle row keeps the replayed angle at `B` but claims:

```text
(A - B) . (C - B) = 1
```

Exact replay computes the dot product as `0`, and the promoted source row
checks the final exact-rational conflict with `UnsatFarkas` evidence.

## Ptolemy Rectangle

The finite Ptolemy row uses a `4 x 3` rectangle centered at the origin:

```text
A = (-2,-3/2)
B = ( 2,-3/2)
C = ( 2, 3/2)
D = (-2, 3/2)
```

All four vertices lie on the circle with squared radius `25/4`. The side
lengths are `4,3,4,3`, and both diagonals have length `5`, so the replayed
Ptolemy arithmetic is:

```text
AC * BD = 5 * 5 = 25
AB * CD + BC * DA = 4 * 4 + 3 * 3 = 25
```

The checked bad Ptolemy row keeps the replayed rectangle but claims the
right-hand side is `24`. The source artifact checks only the final exact
linear conflict:

```smt2
(set-logic QF_LRA)
(declare-const ptolemy_rhs Real)
(assert (= ptolemy_rhs 25))
(assert (= ptolemy_rhs 24))
(check-sat)
```

## Bad Diagonal Row

The malformed row claims that the diagonal intersection has x-coordinate
`1/2`. Exact replay computes:

```text
intersection_x = 0
```

The source SMT-LIB artifact fixes the replayed value and the malformed value:

```smt2
(set-logic QF_LRA)
(declare-const diagonal_intersection_x Real)
(assert (= diagonal_intersection_x 0))
(assert (= diagonal_intersection_x (/ 1 2)))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

## What This Does Not Prove

The pack does not prove general cyclic quadrilateral theorems. It does not
prove the general Ptolemy theorem, general angle chasing, the inscribed-angle
theorem, or circle-line correspondences.

Those remain named in the Lean-horizon row:

```text
finite cyclic replay: checked now
general cyclic geometry: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cyclic-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_diagonal_intersection_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_opposite_angle_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_ptolemy_artifact_emits_checked_farkas
```
