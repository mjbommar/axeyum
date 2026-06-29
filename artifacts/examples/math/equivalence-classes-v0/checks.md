# Checks

## `equivalence-relation-classes-witness`

Expected result: `sat`.

The witness lists the same-parity relation on `{0, 1, 2, 3}`. The validator
checks reflexivity, symmetry, transitivity, and the resulting classes.

## `quotient-map-fiber-witness`

Expected result: `sat`.

The witness lists a quotient map to `even` and `odd`. The validator checks the
finite function table, recomputes fibers, and verifies that two elements are
related exactly when they have the same quotient label.

## `partition-relation-roundtrip`

Expected result: `sat`.

The witness lists a partition of `{a, b, c, d, e}`. The validator checks that
the blocks are disjoint and covering, then recomputes the induced equivalence
relation.

## `bad-equivalence-rejected`

Expected result: `unsat`.

The checked query is the fixed false claim that a relation containing `a ~ b`
and `b ~ c`, but missing `a ~ c`, is an equivalence relation. The validator
confirms the relation is reflexive and symmetric, then rejects transitivity.

## `qf-uf-quotient-congruence-alethe`

Expected result: `unsat`.

The SMT-LIB artifact asserts `a = c` while also asserting `q(a) != q(c)` for a
quotient-map-style uninterpreted function `q`. The solver regression requires
`Evidence::UnsatAletheProof`, rechecks it with `Evidence::check`, and confirms
there are no trusted reduction steps.
