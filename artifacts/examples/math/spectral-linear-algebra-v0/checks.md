# Checks

## `symmetric-eigenpair-witness`

Expected result: `sat`.

The validator recomputes `A*v` and checks it equals `lambda*v` exactly for
`lambda = 3` and `v = [1,1]`.

## `orthogonal-eigenbasis-witness`

Expected result: `sat`.

The validator checks both listed eigenpairs, squared norms, and the pairwise
dot product.

## `rayleigh-quotient-witness`

Expected result: `sat`.

The validator recomputes `v^T A v`, `v^T v`, and their quotient exactly.

## `bad-rayleigh-quotient-rejected`

Expected result: `unsat`.

The vector `[1,1]` has Rayleigh quotient `6/2 = 3`, not `4`. The final
quotient equality conflict is checked by a linked `QF_LRA` artifact and a
resource-backed `UnsatFarkas` regression.

## `spectral-decomposition-witness`

Expected result: `sat`.

The validator checks `P*D*P^-1 = A` and `P*P^-1 = I` exactly.

## `bad-eigenpair-rejected`

Expected result: `unsat`.

The vector `[1,1]` maps to `[3,3]`, not `[2,2]`, so eigenvalue `2` is rejected
for that vector. The first-component equality conflict is also checked by a
linked `QF_LRA` artifact and a resource-backed `UnsatFarkas` regression.
