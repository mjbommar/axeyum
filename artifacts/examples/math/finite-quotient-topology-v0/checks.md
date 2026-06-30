# Checks

## `quotient-map-fiber-witness`

Expected result: `sat`.

The validator recomputes quotient-map fibers from the total function table,
checks surjectivity, and rebuilds the listed same-fiber equivalence relation.

## `quotient-topology-witness`

Expected result: `sat`.

The validator enumerates every subset of the quotient universe and accepts
exactly those whose preimages are open in the source topology.

## `saturated-open-image-witness`

Expected result: `sat`.

The validator checks that `{a,b}` is a union of fibers, is open in `X`, maps to
`{p}`, and is the full preimage of `{p}`.

## `bad-quotient-open-rejected`

Expected result: `unsat`.

The row claims `{r}` is quotient-open. Replay computes
`q^{-1}({r}) = {c}`, and `{c}` is not open in the source topology. The source
SMT-LIB artifact isolates the fixed open-status contradiction and Axeyum emits
and checks an Alethe proof for it.

## `general-quotient-topology-lean-horizon`

Expected result: `not-run`.

General quotient topology, quotient-map universal properties, preservation or
failure of topological properties under quotients, and quotient-space
invariance theorems remain Lean-horizon.
