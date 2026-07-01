# Checks

## `residual-norm-bound-witness`

Expected result: `sat`.

The candidate vector `[1, 1]` has residual `[-1, -1]`, so its exact residual
infinity norm is `1`, matching the claimed bound.

## `solution-box-replay`

Expected result: `sat`.

The vector `[6/5, 6/5]` solves the fixed `2x2` system exactly and lies inside
the rational interval box `[1, 3/2] x [1, 3/2]`.

## `jacobi-contraction-witness`

Expected result: `sat`.

The validator recomputes the first Jacobi step from `x0 = [0, 0]`, checks the
exact solution, recomputes both error norms, and confirms the row-sum
contraction inequality.

## `bad-residual-bound-rejected`

Expected result: `unsat`.

The same candidate vector has exact residual infinity norm `1`, so the claimed
bound `1/2` is false.

The resource-backed Axeyum regression checks the final residual-bound
contradiction as `QF_LRA`: `residual_inf_norm = 1` and
`residual_inf_norm <= 1/2`, requiring rechecked `UnsatFarkas` evidence.

## `bad-jacobi-error-bound-rejected`

Expected result: `unsat`.

The Jacobi witness has exact first-step error infinity norm `7/44`, so the
claimed bound `1/8` is false.

The resource-backed Axeyum regression checks the final iteration-error
contradiction as `QF_LRA`: `44 * jacobi_error1_inf_norm = 7` and
`jacobi_error1_inf_norm <= 1/8`, requiring rechecked `UnsatFarkas` evidence.
