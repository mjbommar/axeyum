# Checks

## `partial-order-witness`

Expected result: `sat`.

The witness lists the divisibility relation on `{1, 2, 4}`. The validator checks
that the listed relation is reflexive, antisymmetric, and transitive.

## `bijection-table-witness`

Expected result: `sat`.

The witness lists a finite function from `{x0, x1, x2}` to `{y0, y1, y2}`. The
validator checks that the graph is total, single-valued, injective, and
surjective.

## `non-function-rejected`

Expected result: `unsat`.

The checked query is the fixed false claim that a graph with both
`x0 -> y0` and `x0 -> y1` is a function. The validator confirms the graph
violates single-valuedness.
