# Checks

## `finite-open-cover-subcover`

Expected result: `sat`.

The validator checks that the listed cover and subcover contain only open sets,
that the subcover is drawn from the cover, and that both unions cover the
finite universe.

## `minimal-subcover-size-witness`

Expected result: `sat`.

The validator checks the listed two-set subcover and enumerates all smaller
subfamilies to confirm none cover the universe.

## `finite-intersection-family-witness`

Expected result: `sat`.

The validator checks that each listed set is closed and that every non-empty
finite subfamily has non-empty intersection. It also checks the total
intersection is `{b}`.

## `bad-open-cover-rejected`

Expected result: `unsat`.

The validator recomputes the union of `{a}` and `{b}` and rejects the open-cover
claim because `c` is missing.

## `general-compactness-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove compactness for arbitrary topological spaces.
That requires a future Lean artifact with no `sorryAx` dependencies.
