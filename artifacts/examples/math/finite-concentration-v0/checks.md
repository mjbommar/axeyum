# Checks

## `markov-inequality-witness`

Expected result: `sat`.

The validator checks nonnegativity, recomputes the expectation, recomputes the
tail event, and verifies `P(X >= a) <= E[X] / a`.

## `chebyshev-inequality-witness`

Expected result: `sat`.

The validator recomputes the mean, variance, centered tail event, and verifies
`P(|X - mu| >= r) <= Var(X) / r^2`.

## `union-bound-witness`

Expected result: `sat`.

The validator recomputes event probabilities and the finite union probability,
then checks the union bound.

## `bad-concentration-bound-rejected`

Expected result: `unsat`.

The validator rejects the claimed tail bound because the actual finite tail
probability is `1/4`, which is greater than the claimed `1/8`.

The resource-backed Axeyum regression checks the final bound obligation as
`QF_LRA`: `tail_probability = 1/4` and `tail_probability <= 1/8`, requiring
rechecked `UnsatFarkas` evidence.

## `general-concentration-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove Chernoff bounds, Hoeffding bounds, laws of large
numbers, central limit theorems, martingale concentration, or asymptotic
statistical inference. Those require future Lean artifacts with no `sorryAx`
dependencies.
