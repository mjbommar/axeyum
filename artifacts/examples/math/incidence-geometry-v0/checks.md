# Checks

## `line-equation-through-two-points`

Expected result: `sat`.

The validator checks that the line `2x - y + 1 = 0` contains both `(0,1)` and
`(2,5)`.

## `line-intersection-witness`

Expected result: `sat`.

The validator checks that `x + y - 3 = 0` and `x - y - 1 = 0` are non-parallel
and intersect at `(2,1)`.

## `point-on-line-witness`

Expected result: `sat`.

The validator checks that `(3,7)` satisfies `2x - y + 1 = 0`.

## `bad-incidence-rejected`

Expected result: `unsat`.

For the same line `2x - y + 1 = 0`, the point `(2,2)` gives:

```text
2*2 - 2 + 1 = 3
```

The malformed row claims the point lies on the line, i.e. the line value is
`0`. The source SMT-LIB artifact isolates the final exact-linear conflict:

```text
line_value = 3
line_value = 0
```

The QF_LRA route must emit checked `UnsatFarkas` evidence.

## `general-incidence-geometry-lean-horizon`

Expected result: `not-run`.

This row records the proof-assistant target: general incidence, projective, and
synthetic-geometry theorems are not finite coordinate replay.
