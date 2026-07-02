# Checks

## `kernel-normalization-witness`

Expected result: `sat`.

The validator checks that every source row is a normalized probability
distribution over the target set.

## `kernel-pushforward-witness`

Expected result: `sat`.

The validator recomputes the pushed-forward target distribution
`nu(y) = sum_x mu(x) K(x,y)` exactly.

## `joint-disintegration-witness`

Expected result: `sat`.

The validator recomputes the joint table, target marginal, and recovered kernel
rows by exact finite marginalization and division.

## `kernel-composition-witness`

Expected result: `sat`.

The validator recomputes the composed finite kernel
`M(x,z) = sum_y K(x,y) L(y,z)`.

## `bad-kernel-row-rejected`

Expected result: `unsat`.

The validator rejects the malformed row because one source row sums to `6/5`.
This row is replay-only; the separate `qf-lra-bad-kernel-row` row owns the
proof-object refutation.

## `qf-lra-bad-kernel-row`

Expected result: `unsat`.

The source-linked QF_LRA artifact isolates the exact-rational contradiction and
the `math_resource_lra_routes` regression checks Axeyum's emitted Farkas
evidence independently.

## `bad-kernel-composition-rejected`

Expected result: `unsat`.

The validator recomputes the composed transition
`(K;L)(rainy, early) = 22/75`, so the claimed value `1/3` is false.
This row is replay-only; the separate `qf-lra-bad-kernel-composition` row owns
the proof-object refutation.

## `qf-lra-bad-kernel-composition`

Expected result: `unsat`.

The source-linked QF_LRA artifact isolates the final exact-rational
contradiction `75 * rainy_early = 22` and `rainy_early = 1/3`, and the
`math_resource_lra_routes` regression checks Axeyum's emitted Farkas evidence
independently.

## `general-kernel-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove regular conditional probabilities,
disintegration theorems, Markov kernels on arbitrary measurable spaces, or
stochastic-process convergence. Those require future Lean artifacts with no
`sorryAx` dependencies.
