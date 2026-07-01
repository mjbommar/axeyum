# Checks

## `boolean-lattice-poset`

Expected result: `sat`.

The validator checks the listed relation is reflexive, antisymmetric, and
transitive, with `0` as bottom and `AB` as top.

## `meet-join-table-replay`

Expected result: `sat`.

The validator recomputes lower and upper bound sets for every pair and checks
the listed meet/join tables.

## `distributive-lattice-replay`

Expected result: `sat`.

The validator checks both finite distributive lattice laws over all triples.

## `monotone-map-fixed-points`

Expected result: `sat`.

The validator checks monotonicity, recomputes fixed points, and verifies the
least fixed point.

## `bad-partial-order-rejected`

Expected result: `unsat`.

The validator rejects the relation with `x <= y` and `y <= x` for distinct
`x` and `y`, because antisymmetry fails. The linked `QF_UF` artifact turns the
fixed antisymmetry equality claim into a checked Alethe refutation.

## `bad-top-element-rejected`

Expected result: `unsat`.

The validator rejects the claim that `A` is top in the four-element Boolean
lattice. The relation has `B <= AB`, but not `B <= A`; a top-element claim for
`A` would require `B <= A`. The linked CNF artifact records the fixed false
comparison and the false top claim as a one-variable contradiction checked by
DRAT and LRAT.

## `general-order-lattice-theory-lean-horizon`

Expected result: `not-run`.

Complete-lattice fixed-point theorems, order-theoretic induction, domain
theory, Galois connections, Boolean-algebra representation, and infinite posets
belong in future Lean resources. The finite rows above are exact table replay
checks only.
