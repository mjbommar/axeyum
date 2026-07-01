# Checks

## `monotone-upper-bound-prefix`

Expected result: `sat`.

The validator checks that the listed prefix equals `a_n = n/(n+1)`, is
strictly increasing, and is pointwise below the displayed upper bound.

## `finite-prefix-supremum`

Expected result: `sat`.

The validator recomputes the maximum of the listed finite prefix and checks the
displayed argmax index and prefix supremum.

## `tail-gap-below-epsilon`

Expected result: `sat`.

The validator checks one finite tail against one epsilon by recomputing
`1 - a_n` for every listed tail index.

## `bad-upper-bound-rejected`

Expected result: `unsat`.

Finite replay computes `a_6 = 6/7`. The malformed row claims `5/6` is an upper
bound for the prefix. Since `6/7 <= 5/6` is false, the committed SMT-LIB
artifact checks the final exact-rational contradiction through QF_LRA/Farkas
evidence.

## `bad-tail-gap-rejected`

Expected result: `unsat`.

Finite replay computes `a_2 = 2/3`, so the gap to the proposed limit `1` is
`1/3`. The malformed row claims the finite tail starting at `n = 2` is within
`epsilon = 1/4`. Since the gap exceeds epsilon by `1/12`, the committed SMT-LIB
artifact checks the final exact-rational contradiction through QF_LRA/Farkas
evidence.

## `monotone-convergence-lean-horizon`

Expected result: `not-run`.

The actual monotone convergence theorem needs completeness and quantified
reasoning over all indices. It remains a Lean-horizon target.
