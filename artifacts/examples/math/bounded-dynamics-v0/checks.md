# Checks

## `linear-recurrence-trace`

Expected result: `sat`.

The validator replays the trace for `x(t+1) = x(t) + 2`, starting from `0` for
four steps, and checks the states are exactly `0, 2, 4, 6, 8`.

## `bad-transition-step-rejected`

Expected result: `unsat`.

The validator replays the plus-two trace and recomputes the transition after
state `2` as `4`. The malformed claim says the same next state is `5`; the
source QF_LRA artifact isolates the contradiction `next_state = 2 + 2` and
`next_state = 5` for Farkas checking.

## `bounded-invariant-witness`

Expected result: `sat`.

The validator replays the same recurrence trace and checks the invariant
`0 <= x(t) <= 8` at every listed time step.

## `unsafe-threshold-reachable`

Expected result: `sat`.

The validator replays the trace for `x(t+1) = x(t) + 3`, starting from `0` for
three steps, and checks that threshold `x(t) >= 7` first becomes true at step
`3`.

## `bad-invariant-bound-rejected`

Expected result: `unsat`.

The validator replays the plus-two trace and recomputes the maximum state as
`8`. The malformed claim says every state stays below `6`; the source QF_LRA
artifact isolates the contradiction `terminal_state = 8` and
`terminal_state <= 6` for Farkas checking.
