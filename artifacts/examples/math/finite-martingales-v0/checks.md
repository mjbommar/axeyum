# Checks

## `finite-martingale-witness`

Expected result: `sat`.

The validator checks adaptedness and recomputes each finite conditional
expectation `E[M_{t+1} | F_t]` exactly.

## `square-submartingale-witness`

Expected result: `sat`.

The validator recomputes conditional expectations of `M_{t+1}^2` and checks
they are pointwise at least `M_t^2`.

## `bounded-stopping-replay`

Expected result: `sat`.

The validator checks that the listed `tau` is a bounded stopping time for the
finite filtration, recomputes the stopped values, and checks
`E[M_tau] = E[M0]`.

## `bad-stopped-expectation-rejected`

Expected result: `unsat`.

The validator replays the bounded stopping time, recomputes stopped values
`1, 1, 0, -2`, and checks that the stopped expectation is `0`, not `1/2`.
This row is replay-only; the separate `qf-lra-bad-stopped-expectation` row owns
the proof-object refutation.

## `qf-lra-bad-stopped-expectation`

Expected result: `unsat`.

The source-linked QF_LRA artifact records the exact-linear contradiction
between `stopped_expectation = 0` and `stopped_expectation = 1/2`, and is
checked by the shared Farkas route regression.

## `bad-martingale-rejected`

Expected result: `unsat`.

The validator rejects the malformed terminal table because the conditional
expectation on the up block is `3/2`, not `1`. This row is replay-only; the
separate `qf-lra-bad-martingale` row owns the proof-object refutation.

## `qf-lra-bad-martingale`

Expected result: `unsat`.

The source-linked QF_LRA artifact records the exact-linear contradiction
between `up_block_conditional_expectation = 3/2` and
`up_block_conditional_expectation = 1`, and is checked by the shared Farkas
route regression.

## `general-martingale-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general martingale convergence, optional
stopping, Doob inequalities, stochastic integration, or continuous-time
process theory. Those require future Lean artifacts with no `sorryAx`
dependencies.
