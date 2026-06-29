# Checks

## `finite-connected-space-witness`

Expected result: `sat`.

The validator checks the two-point Sierpinski topology and enumerates all
subsets to confirm that only the empty set and universe are clopen.

## `finite-disconnected-separation-witness`

Expected result: `sat`.

The validator checks that `{a}` and `{b}` are non-empty, disjoint, open sets
whose union is the universe.

## `clopen-subset-disconnection-witness`

Expected result: `sat`.

The validator checks that `{a}` is open, that its complement `{b}` is open, and
that the pair forms an open separation.

## `bad-connected-claim-rejected`

Expected result: `unsat`.

The validator recomputes the non-trivial clopen subset `{a}` in the discrete
topology and rejects the connectedness claim.

## `general-connectedness-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove general connectedness theorems. Connected-image
theorems, interval connectedness, path-connectedness, and similar results need
a future Lean artifact with no `sorryAx` dependencies.
