# Checks

## `vandermonde-unisolvence-witness`

Expected result: `sat`.

The validator recomputes the polynomial-basis evaluation matrix and checks that
its determinant is nonzero.

## `interpolation-polynomial-witness`

Expected result: `sat`.

The validator recomputes the same evaluation matrix and checks that multiplying
it by the listed coefficient vector yields the listed sample values.

## `alternating-residual-witness`

Expected result: `sat`.

The validator evaluates the residual polynomial at each point, recomputes the
sign vector, and checks that adjacent nonzero signs alternate with common
absolute magnitude.

## `bad-duplicate-node-grid-rejected`

Expected result: `unsat`.

The validator rejects the claimed unisolvence because the duplicate-node
evaluation matrix has determinant zero and a listed nonzero coefficient vector
vanishes on every listed sample point.

## `general-chebyshev-system-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general Chebyshev systems, Haar spaces, minimax
approximation, alternation theorems, compactness arguments, or
infinite-dimensional functional analysis. Those require future Lean artifacts
with no `sorryAx` dependencies.
