# Checks

## `l1-triangle-witness`

Expected result: `sat`.

The validator recomputes `u + v`, the three `l1` norms, and checks
`||u + v||_1 <= ||u||_1 + ||v||_1`.

## `bad-l1-sum-norm-rejected`

Expected result: `unsat`.

The validator reuses the same exact vectors, recomputes `u + v = (4, 1)` and
`||u + v||_1 = 5`, then checks the source QF_LRA artifact for the malformed
claim `||u + v||_1 <= 4` through checked Farkas evidence.

## `matrix-operator-bound`

Expected result: `sat`.

The validator recomputes `A*x`, the infinity norm of `x` and `A*x`, the matrix
row-sum norm, and checks `||A*x||_infty <= ||A||_row-sum * ||x||_infty`.

## `chebyshev-recurrence-witness`

Expected result: `sat`.

The validator checks the exact values `T0(1/2)`, `T1(1/2)`, `T2(1/2)`, and
`T3(1/2)` against the recurrence `T(n+1) = 2*x*T(n) - T(n-1)`.

## `bad-operator-bound-rejected`

Expected result: `unsat`.

The validator recomputes `A*x = (3, 3)`, `||A*x||_infty = 3`, `||A||_row-sum =
3`, and `||x||_infty = 2`. The malformed row claims the image norm is at most
`2`, so the source QF_LRA artifact closes the final contradiction with checked
Farkas evidence.
