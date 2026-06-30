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

## `bad-martingale-rejected`

Expected result: `unsat`.

The validator rejects the malformed terminal table because the conditional
expectation on the up block is `3/2`, not `1`. The source-linked QF_LRA
artifact records the resulting exact-linear contradiction and is checked by
the shared Farkas route regression.

## `general-martingale-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general martingale convergence, optional
stopping, Doob inequalities, stochastic integration, or continuous-time
process theory. Those require future Lean artifacts with no `sorryAx`
dependencies.
