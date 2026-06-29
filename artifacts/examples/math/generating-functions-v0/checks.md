# Checks

## `coefficient-extraction-witness`

Expected result: `sat`.

The validator checks that the listed sequence prefix is exactly the coefficient
list of the ordinary generating polynomial and that the requested coefficient
indices replay to the listed extracted values.

## `cauchy-product-convolution`

Expected result: `sat`.

The validator recomputes the Cauchy product of two finite generating
polynomials and checks the listed convolution coefficients exactly.

## `fibonacci-generating-prefix`

Expected result: `sat`.

The validator checks the Fibonacci recurrence over the listed finite prefix and
then verifies that `(1 - x - x^2) F(x)` has prefix `x` through degree `6`.

## `bad-cauchy-product-rejected`

Expected result: `unsat`.

The validator rejects an incorrect convolution row where the claimed
coefficient of `x^2` is `12` but the exact Cauchy product coefficient is `13`.

## `general-generating-functions-lean-horizon`

Expected result: `not-run`.

General generating-function transformations, closed forms, convergence, and
asymptotic extraction belong in future Lean-backed resources. The finite rows
above are exact coefficient replay checks only.
