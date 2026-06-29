# Checks

## `complex-arithmetic-replay`

Expected result: `sat`.

The validator recomputes the sum and product of `1 + 2i` and `3 - i` using the
real-pair operations.

## `conjugate-norm-replay`

Expected result: `sat`.

The validator recomputes the conjugate of `3 + 4i`, multiplies `z * conjugate(z)`,
and checks the result is the real pair `(25, 0)`.

## `quadratic-root-witness`

Expected result: `sat`.

The validator evaluates `z^2 + 1` at `z = i` and checks the result is exactly
`0 + 0i`.
