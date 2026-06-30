# Checks

## `simplicial-complex-closure`

Expected result: `sat`.

The validator checks that every non-empty face of every listed simplex is also
listed in the complex and verifies the stated dimension counts.

## `oriented-boundary-replay`

Expected result: `sat`.

The validator recomputes the alternating face sum for `[a,b,c]` and checks the
listed boundary chain.

## `boundary-squared-zero`

Expected result: `sat`.

The validator applies the boundary operator twice and checks that all vertex
coefficients cancel to the zero chain.

## `betti-rank-replay`

Expected result: `sat`.

The validator builds the boundary matrices for the three-edge circle over
exact rationals, computes ranks by Gaussian elimination, checks `b0 = 1` and
`b1 = 1`, and verifies the listed one-cycle.

## `bad-boundary-rejected`

Expected result: `unsat`.

The validator rejects the false boundary because the coefficient of `[a,c]`
must be `-1`, not `1`.

## `qf-lia-bad-boundary-coefficient`

Expected result: `unsat`.

The SMT-LIB artifact isolates the same sign error as an integer equality
contradiction: the coefficient of `[a,c]` is forced to be both `-1` and `1`.
Axeyum emits and checks an `UnsatDiophantine` certificate for those
inconsistent equalities.

## `general-homology-lean-horizon`

Expected result: `not-run`.

Homology invariance, exact sequences, homotopy equivalence, cohomology
operations, and higher-dimensional algebraic topology belong in future Lean
resources. The finite rows above are exact replay checks only.
