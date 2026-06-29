# Checks

## `lp-feasible-point`

Expected result: `sat`.

The validator replays `x = 1`, `y = 2` against the base LP inequalities.

## `objective-threshold-witness`

Expected result: `sat`.

The validator replays `x = 3`, `y = 1` against the base LP inequalities and
checks the objective threshold `x + y >= 4`.

## `objective-threshold-farkas-infeasible`

Expected result: `unsat`.

The validator checks a Farkas-style certificate for the infeasible threshold
`x + y >= 5`. The nonnegative multipliers combine two inequalities into
`0 <= -1`, so no assignment can satisfy the threshold and the base region.

The resource-backed Axeyum regression builds the same threshold conflict as a
conjunctive `QF_LRA` system and requires rechecked `UnsatFarkas` evidence.
