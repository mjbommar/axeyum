# Checks

## `l1-triangle-witness`

Expected result: `sat`.

The validator recomputes `u + v`, the three `l1` norms, and checks
`||u + v||_1 <= ||u||_1 + ||v||_1`.

## `bad-l1-sum-norm-rejected`

Expected result: `unsat`.

The validator reuses the same exact vectors, recomputes `u + v = (4, 1)` and
`||u + v||_1 = 5`, then rejects the malformed fixed row that claims
`||u + v||_1 <= 4`.

This row is replay-only; the separate `qf-lra-bad-l1-sum-norm` row owns the
proof-object refutation.

## `qf-lra-bad-l1-sum-norm`

Expected result: `unsat`.

The resource-backed Axeyum regression checks the final linear obligation as
`QF_LRA`: `sum_norm = 5` and `sum_norm <= 4`, requiring rechecked
`UnsatFarkas` evidence.

## `matrix-operator-bound`

Expected result: `sat`.

The validator recomputes `A*x`, the infinity norm of `x` and `A*x`, the matrix
row-sum norm, and checks `||A*x||_infty <= ||A||_row-sum * ||x||_infty`.

## `chebyshev-recurrence-witness`

Expected result: `sat`.

The validator checks the exact values `T0(1/2)`, `T1(1/2)`, `T2(1/2)`, and
`T3(1/2)` against the recurrence `T(n+1) = 2*x*T(n) - T(n-1)`.

## `bad-chebyshev-t3-rejected`

Expected result: `unsat`.

The validator reuses the same finite Chebyshev prefix, recomputes
`T3(1/2) = -1`, and rejects the malformed fixed row that claims
`T3(1/2) = -1/2`.

This row is replay-only; the separate `qf-lra-bad-chebyshev-t3` row owns the
proof-object refutation.

## `qf-lra-bad-chebyshev-t3`

Expected result: `unsat`.

The resource-backed Axeyum regression checks the shifted Chebyshev value
conflict as `QF_LRA`, requiring rechecked `UnsatFarkas` evidence.

## `bad-operator-bound-rejected`

Expected result: `unsat`.

The validator recomputes `A*x = (3, 3)`, `||A*x||_infty = 3`, `||A||_row-sum =
3`, and `||x||_infty = 2`. The malformed row claims the image norm is at most
`2`, so exact replay rejects the fixed data row.

This row is replay-only; the separate `qf-lra-bad-operator-bound` row owns the
proof-object refutation.

## `qf-lra-bad-operator-bound`

Expected result: `unsat`.

The resource-backed Axeyum regression checks the final linear obligation as
`QF_LRA`: `image_norm = 3` and `image_norm <= 2`, requiring rechecked
`UnsatFarkas` evidence.
