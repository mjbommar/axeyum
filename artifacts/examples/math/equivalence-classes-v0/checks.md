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

## `qf-uf-congruence-proof-gap`

Expected result: `not-run`.

This row records the future proof-object route: a QF_UF/Alethe congruence
certificate for quotient-style equality reasoning.
