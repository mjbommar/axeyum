# Checks

## `residual-norm-bound-witness`

Expected result: `sat`.

The candidate vector `[1, 1]` has residual `[-1, -1]`, so its exact residual
infinity norm is `1`, matching the claimed bound.

## `solution-box-replay`

Expected result: `sat`.

The vector `[6/5, 6/5]` solves the fixed `2x2` system exactly and lies inside
the rational interval box `[1, 3/2] x [1, 3/2]`.

## `bad-solution-box-upper-bound-rejected`

Expected result: `unsat`.

The exact solution has first component `6/5`, so the claimed upper bound
`x0 <= 1` is false.

The resource-backed Axeyum regression checks the final solution-box
contradiction as `QF_LRA`: `5 * solution_x0 = 6` and `solution_x0 <= 1`,
requiring rechecked `UnsatFarkas` evidence.

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
