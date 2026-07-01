# Checks

## `trace-determinant-characteristic-polynomial`

Expected result: `sat`.

The validator recomputes `trace(A)`, `det(A)`, and the `2x2` characteristic
polynomial exactly.

## `characteristic-roots-witness`

Expected result: `sat`.

The validator evaluates the characteristic polynomial at each listed
eigenvalue and checks that every value is zero.

## `cayley-hamilton-replay`

Expected result: `sat`.

The validator recomputes `A^2` and checks `A^2 - trace(A)*A + det(A)*I = 0`
exactly for the fixed matrix.

## `gershgorin-interval-witness`

Expected result: `sat`.

The validator recomputes row centers, row radii, exact intervals, and confirms
that each listed eigenvalue lies inside at least one interval.

## `bad-trace-invariant-rejected`

Expected result: `unsat`.

The validator recomputes `trace([[2,1],[1,2]]) = 4`, so the malformed claim
that the fixed matrix has trace `5` is rejected by exact arithmetic. The trace
value conflict is also checked by a linked `QF_LRA` artifact and a
resource-backed `UnsatFarkas` regression.

## `bad-characteristic-polynomial-rejected`

Expected result: `unsat`.

The claimed polynomial `lambda^2 - 5*lambda + 6` differs from the recomputed
characteristic polynomial `lambda^2 - 4*lambda + 3`. The validator also checks
that the claimed polynomial evaluates to `2` at the actual root `1`, so the
claim is rejected by exact arithmetic. The witness-root value conflict is also
checked by a linked `QF_LRA` artifact and a resource-backed `UnsatFarkas`
regression.
