# Checks

## `l1-triangle-witness`

Expected result: `sat`.

The validator recomputes `u + v`, the three `l1` norms, and checks
`||u + v||_1 <= ||u||_1 + ||v||_1`.

## `matrix-operator-bound`

Expected result: `sat`.

The validator recomputes `A*x`, the infinity norm of `x` and `A*x`, the matrix
row-sum norm, and checks `||A*x||_infty <= ||A||_row-sum * ||x||_infty`.

## `chebyshev-recurrence-witness`

Expected result: `sat`.

The validator checks the exact values `T0(1/2)`, `T1(1/2)`, `T2(1/2)`, and
`T3(1/2)` against the recurrence `T(n+1) = 2*x*T(n) - T(n-1)`.
