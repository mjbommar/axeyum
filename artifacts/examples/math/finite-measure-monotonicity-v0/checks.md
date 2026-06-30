# Checks

## `finite-measure-table`

Expected result: `sat`.

The validator checks that the listed powerset family is a sigma-algebra and
that the exact-rational table is a normalized finite measure.

## `subset-monotonicity-witness`

Expected result: `sat`.

The validator checks `A subset B`, recomputes `B \ A`, and verifies
`mu(B) = mu(A) + mu(B \ A)` and `mu(A) <= mu(B)`.

## `finite-union-subadditivity-witness`

Expected result: `sat`.

The validator recomputes `A union B`, `A intersect B`, and checks
`mu(A union B) = mu(A) + mu(B) - mu(A intersect B)`, hence
`mu(A union B) <= mu(A) + mu(B)`.

## `bad-subset-measure-rejected`

Expected result: `unsat`.

Finite replay computes `mu({a}) = 1/6`. The malformed row claims
`mu({a}) = 2/3`, which would also make the subset larger than its superset
`{a,b}` with measure `1/2`. The committed SMT-LIB artifact isolates the final
exact-rational contradiction and checks it through QF_LRA/Farkas evidence.

## `general-measure-monotonicity-lean-horizon`

Expected result: `not-run`.

General monotonicity over arbitrary measure spaces follows from measure
axioms, and convergence/countable-subadditivity results need future Lean
resources rather than finite-table replay alone.
