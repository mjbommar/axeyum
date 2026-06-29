# Checks

## `finite-bijection-cardinality-witness`

Expected: `sat`.

The witness maps three domain elements to three codomain elements with a total,
single-valued, injective, and surjective graph. This replays the finite meaning
of equal cardinality.

## `proper-subset-injection-witness`

Expected: `sat`.

The witness maps a two-element proper subset into a three-element set. The graph
is injective but not surjective, so it witnesses `|A| < |B|` for the fixed
finite sets.

## `no-injection-four-to-three`

Expected: `unsat`.

The validator enumerates all functions from a four-element domain to a
three-element codomain and confirms none is injective.

## `no-surjection-two-to-three`

Expected: `unsat`.

The validator enumerates all functions from a two-element domain to a
three-element codomain and confirms none is surjective.

## `cantor-diagonal-lean-horizon`

Expected: `not-run`.

This row names the infinite theorem boundary: no surjection from the natural
numbers onto their powerset. It remains a Lean-horizon target until a concrete
Lean artifact and checker command exist.
