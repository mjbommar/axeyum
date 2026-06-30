# Checks

## `riemann-sums-linear-partition`

Expected result: `sat`.

The validator replays the partition `0, 1/4, 1/2, 3/4, 1` for `f(x) = x` and
checks the listed left sum, right sum, trapezoid sum, and exact integral.

## `midpoint-rule-affine-exact`

Expected result: `sat`.

The validator checks the listed midpoints for a uniform partition of `[0, 2]`
and recomputes the midpoint sum for `f(x) = 1 + 2x`. For this affine function,
the midpoint sum equals the exact integral.

## `antiderivative-endpoint-replay`

Expected result: `sat`.

The validator differentiates the listed antiderivative `x^2`, checks that it is
`2x`, and replays the endpoint difference on `[1, 3]`.

## `monotone-quadratic-lower-upper-bounds`

Expected result: `sat`.

The validator checks the lower and upper sums for `x^2` on the partition
`0, 1/2, 1`, using left endpoints for the lower sum and right endpoints for the
upper sum. It also checks that the exact integral lies between them.

## `false-integral-claim-rejected`

Expected result: `unsat`.

The validator computes the exact integral of `x` on `[0, 1]` as `1/2` and
rejects the listed claim `3/4`.

The source SMT-LIB artifact records the same final contradiction:

```text
integral_value = 1/2
integral_value = 3/4
```

The `math_resource_lra_routes` regression parses
`smt2/false-integral-farkas-conflict.smt2`, emits `UnsatFarkas` evidence, and
independently checks the certificate.

## `fundamental-theorem-lean-horizon`

Expected result: `not-run`.

This row records the future theorem-prover target for Riemann integrability,
convergence of arbitrary tagged partitions, and the fundamental theorem of
calculus.
