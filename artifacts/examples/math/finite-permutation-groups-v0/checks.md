# Checks

## `s3-permutation-group-laws`

Expected result: `sat`.

The witness lists the six permutations of a three-point set and the Cayley table
for composition. The validator checks bijectivity, closure, identity, inverses,
and associativity.

## `permutation-composition-table-replay`

Expected result: `sat`.

The validator recomputes `left after right` for every pair of listed
permutations and checks that the resulting map has the table label shown in the
Cayley table.

## `cycle-type-and-sign-replay`

Expected result: `sat`.

The validator recomputes cycle lengths and parity from the point maps, then
checks that the sign map is a homomorphism from `S3` to the two-element parity
group.

## `natural-action-orbit-stabilizer`

Expected result: `sat`.

The validator checks that the natural action table equals the underlying
permutation maps, satisfies the group-action laws, and recomputes the orbit and
stabilizer of point `1`.

## `bad-nonbijection-rejected`

Expected result: `unsat`.

The fixed false claim is that a total map with duplicated image `1` and missing
image `2` is a permutation. The validator confirms the map is not bijective.

## `general-permutation-group-theory-lean-horizon`

Expected result: `not-run`.

General permutation-group theory remains a Lean/mathlib target. The finite rows
only validate fixed table and finite-function artifacts.
