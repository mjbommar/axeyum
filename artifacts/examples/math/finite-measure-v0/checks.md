# Checks

## `finite-sigma-algebra-axioms`

Expected result: `sat`.

The validator checks that the listed subsets form a sigma-algebra on the finite
universe.

## `finite-measure-additivity`

Expected result: `sat`.

The validator checks exact finite measure normalization and finite additivity
over disjoint measurable sets.

## `event-complement-measure`

Expected result: `sat`.

The validator checks the event, complement, and total measure identities
exactly.

## `bad-complement-measure-rejected`

Expected result: `unsat`.

Finite replay computes `mu({a,b}) = 1/3` and `mu(U) = 1`. The malformed row
claims `mu({a,b}^c) = 1/2` while still requiring
`mu({a,b}) + mu({a,b}^c) = mu(U)`. This row is exact finite replay.

## `qf-lra-bad-complement-measure`

Expected result: `unsat`.

The source SMT-LIB artifact fixes `mu({a,b}) = 1/3`, `mu(U) = 1`,
`mu({a,b}^c) = 1/2`, and complement additivity. The final contradiction is
checked through QF_LRA/Farkas evidence.
