# Checks

## `product-measure-table-witness`

Expected result: `sat`.

The validator checks normalized factor distributions and verifies every listed
product atom has probability `P(x) * Q(y)`. It also recomputes the rectangle
measure for `{heads} x {two, three}`.

## `marginalization-witness`

Expected result: `sat`.

The validator recomputes left and right marginals from the product probability
table and checks that they recover the factor distributions.

## `finite-fubini-witness`

Expected result: `sat`.

The validator recomputes the direct finite integral, then recomputes both
iterated finite sums. All three values must equal `3`.

## `bad-product-measure-rejected`

Expected result: `unsat`.

The validator rejects the claimed product probability `1/5` because the exact
factor product for `(heads, one)` is `1/6`.

## `fubini-tonelli-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general product-measure construction,
Fubini/Tonelli, kernels, or almost-everywhere theorems. Those require future
Lean artifacts with no `sorryAx` dependencies.
