# Checks

## `quadratic-midpoint-jensen-witness`

Replays a midpoint Jensen inequality for `f(x) = x^2` using exact rational
polynomial evaluation.

## `finite-convex-grid-second-differences`

Checks an equally spaced finite grid by recomputing all second differences.
This is a finite convexity signal, not a theorem about every real point.

## `affine-monotone-threshold-witness`

Checks a finite monotonicity/threshold implication for `g(x) = 3x - 2` on
listed rational samples.

## `bad-midpoint-convexity-rejected`

Rejects a false midpoint-convexity claim with a checked finite counterexample.
The resource-backed Axeyum regression reduces the same fixed row to the linear
inequality `2*f(midpoint) <= f(left)+f(right)`, parses the matching source
SMT-LIB artifact, and requires rechecked `UnsatFarkas` evidence.

## `bad-affine-threshold-rejected`

Rejects a false affine-threshold sample with a checked exact-rational
counterexample. The resource-backed Axeyum regression parses the matching
SMT-LIB artifact for `threshold_shortfall = 3/2` and requires rechecked
`UnsatFarkas` evidence for the contradictory claim
`threshold_shortfall <= 0`.

## `general-convex-analysis-lean-horizon`

Records that general convex analysis, duality, separation, SDP, and algorithm
convergence theorems need future proof-assistant resources.
