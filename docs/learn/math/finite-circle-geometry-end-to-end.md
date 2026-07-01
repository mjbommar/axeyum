# Finite Circle Geometry Checks

This lesson follows
[finite-circle-geometry-v0](../../../artifacts/examples/math/finite-circle-geometry-v0/)
from exact coordinate replay through tangent-line, chord, circle-line, and
checked Farkas evidence. It is a finite rational coordinate certificate, not a
proof of general Euclidean circle geometry.

## Concept

Coordinate circle geometry reduces selected claims to exact arithmetic:

```text
point on circle:      (x - a)^2 + (y - b)^2 = r^2
tangent at point:     (p - c) . (z - p) = 0
perpendicular chord:  radius_to_midpoint . chord_direction = 0
circle-line replay:   line_value(point) = 0 and point lies on circle
```

The resource fixes rational points so the checker can replay every value
without diagrams, floating-point tolerances, or synthetic geometry assumptions.

## What Gets Checked

| Row | Result | Evidence |
|---|---|---|
| `point-on-circle-witness` | `sat` | replay-only |
| `tangent-line-witness` | `sat` | replay-only |
| `chord-midpoint-perpendicular-witness` | `sat` | replay-only |
| `circle-line-intersection-witness` | `sat` | replay-only |
| `bad-circle-radius-rejected` | `unsat` | checked QF_LRA/Farkas |
| `bad-circle-line-intersection-rejected` | `unsat` | checked QF_LRA/Farkas |
| `general-circle-geometry-lean-horizon` | `not-run` | Lean horizon |

## Point On Circle

The point-on-circle row uses:

```text
C = (0,0)
P = (3/5,4/5)
r^2 = 1
```

The validator recomputes:

```text
|P - C|^2 = (3/5)^2 + (4/5)^2 = 9/25 + 16/25 = 1
```

## Tangent Line

The tangent line at `P` is:

```text
(3/5)x + (4/5)y - 1 = 0
```

The validator checks that `P` lies on the line:

```text
(3/5)(3/5) + (4/5)(4/5) - 1 = 0
```

It also checks that the tangent direction is perpendicular to the radius:

```text
radius = (3/5,4/5)
tangent_direction = (-4/5,3/5)
radius . tangent_direction = -12/25 + 12/25 = 0
```

## Chord Midpoint

The chord row uses the circle `x^2 + y^2 = 25`:

```text
A = (3,4)
B = (3,-4)
M = (3,0)
```

Both endpoints lie on the circle. The midpoint is:

```text
((3 + 3)/2, (4 + -4)/2) = (3,0)
```

The chord direction and radius-to-midpoint vector are:

```text
B - A = (0,-8)
M - C = (3,0)
```

Their dot product is zero, so the fixed rational chord is perpendicular to the
radius through its midpoint.

## Circle-Line Intersection

The circle-line row uses the horizontal diameter of the unit circle:

```text
y = 0
A = (-1,0)
B = (1,0)
```

The validator checks both endpoints lie on the line and on the circle:

```text
0*x + 1*y + 0 = 0
x^2 + y^2 = 1
```

It also recomputes the midpoint `(0,0)` and records the right intersection as
`(1,0)`.

## Bad Circle Row

The malformed row claims `(1,1)` lies on the unit circle centered at the
origin. Exact replay computes:

```text
|(1,1)|^2 = 1^2 + 1^2 = 2
```

The source SMT-LIB artifact fixes the replayed value as `2` and also asserts
that it equals `1`:

```smt2
(set-logic QF_LRA)
(declare-const radius_squared Real)
(assert (= radius_squared 2))
(assert (= radius_squared 1))
(check-sat)
```

Axeyum parses that source row, emits `UnsatFarkas` evidence, and independently
checks the certificate.

The second checked bad row keeps the replayed horizontal diameter but claims
the right intersection has x-coordinate `2`:

```smt2
(set-logic QF_LRA)
(declare-const right_intersection_x Real)
(assert (= right_intersection_x 1))
(assert (= right_intersection_x 2))
(check-sat)
```

That row is still a finite coordinate certificate. It checks the exact
post-replay conflict, not arbitrary circle-line intersection theory.

## What This Does Not Prove

The pack does not prove general Euclidean circle theorems. It does not prove
power-of-a-point, cyclic quadrilateral theorems, inversion, angle theorems, or
coordinate-free tangent theorems.

Those remain named in the Lean-horizon row:

```text
finite coordinate replay: checked now
general circle geometry: future Lean reconstruction
```

## Run It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-circle-geometry-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_circle_geometry_bad_radius_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_circle_geometry_bad_line_intersection_artifact_emits_checked_farkas
```
