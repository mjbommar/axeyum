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
`x` and `y`, because antisymmetry fails.

## `general-order-lattice-theory-lean-horizon`

Expected result: `not-run`.

Complete-lattice fixed-point theorems, order-theoretic induction, domain
theory, Galois connections, Boolean-algebra representation, and infinite posets
belong in future Lean resources. The finite rows above are exact table replay
checks only.
