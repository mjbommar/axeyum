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

## `general-kernel-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove regular conditional probabilities,
disintegration theorems, Markov kernels on arbitrary measurable spaces, or
stochastic-process convergence. Those require future Lean artifacts with no
`sorryAx` dependencies.
