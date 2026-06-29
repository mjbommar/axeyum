# Checks

## `linear-recurrence-trace`

Expected result: `sat`.

The validator replays the trace for `x(t+1) = x(t) + 2`, starting from `0` for
four steps, and checks the states are exactly `0, 2, 4, 6, 8`.

## `bounded-invariant-witness`

Expected result: `sat`.

The validator replays the same recurrence trace and checks the invariant
`0 <= x(t) <= 8` at every listed time step.

## `unsafe-threshold-reachable`

Expected result: `sat`.

The validator replays the trace for `x(t+1) = x(t) + 3`, starting from `0` for
three steps, and checks that threshold `x(t) >= 7` first becomes true at step
`3`.
