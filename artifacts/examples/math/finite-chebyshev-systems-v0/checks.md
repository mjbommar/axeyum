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

The promoted QF_LRA route isolates the determinant conflict:

```text
determinant = 0
determinant = 1
```

The solver regression emits checked `UnsatFarkas` evidence for that final
linear contradiction after pack-local replay computes the determinant.

## `bad-interpolation-sample-rejected`

Expected result: `unsat`.

The validator recomputes the interpolation row:

```text
p(x) = 2 - x + 3*x^2
p(1) = 4
```

The malformed row claims:

```text
p(1) = 5
```

The promoted QF_LRA route takes the replayed sample value and checks the final
exact-rational conflict with `UnsatFarkas` evidence.

## `bad-alternating-residual-rejected`

Expected result: `unsat`.

The validator recomputes the alternating residual table:

```text
r(x) = x^2 - 1/2
r(-1), r(0), r(1) = 1/2, -1/2, 1/2
uniform_error = 1/2
```

The malformed row claims:

```text
uniform_error = 2/3
```

The promoted QF_LRA route takes the replayed common magnitude and checks the
final exact-rational conflict with `UnsatFarkas` evidence.

## `general-chebyshev-system-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general Chebyshev systems, Haar spaces, minimax
approximation, alternation theorems, compactness arguments, or
infinite-dimensional functional analysis. Those require future Lean artifacts
with no `sorryAx` dependencies.
