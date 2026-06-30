# Checks

## `coboundary-replay`

Expected result: `sat`.

The validator recomputes the F2 coboundary of the listed 0-cochain on each
edge.

## `coboundary-squared-zero`

Expected result: `sat`.

The validator computes the first coboundary on edges and then the second
coboundary on the filled two-simplex, checking that the final value is zero.

## `cohomology-rank-replay`

Expected result: `sat`.

The validator builds finite coboundary matrices over `F2`, computes their
ranks, checks the listed cohomology dimensions, and confirms that the all-ones
edge cochain is a cocycle but not a coboundary.

## `bad-coboundary-rejected`

Expected result: `unsat`.

The bad row claims the coboundary value on `[a,c]` is `1`. Exact finite replay
computes `0`, so the row is rejected.

## `qf-uf-bad-coboundary-value`

Expected result: `unsat`.

The solver artifact isolates the final mismatch as an equality conflict: the
same finite replay value is asserted equal to both `zero` and `one`, while
`zero != one`. Axeyum emits and checks an Alethe proof for that fixed conflict.

## `general-cohomology-lean-horizon`

Expected result: `not-run`.

General cohomology functoriality, cup products, universal coefficients, de Rham
comparison, sheaf cohomology, duality, and invariance remain Lean-horizon.
