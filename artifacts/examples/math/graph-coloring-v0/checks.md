# Checks

## `triangle-3-coloring-witness`

Expected result: `sat`.

The witness assigns three distinct colors to the vertices of `K3`, so every
edge has differently colored endpoints.

## `bad-edge-coloring-rejected`

Expected result: `unsat`.

The checked query is the claim that assigning both endpoints of a one-edge
graph to `red` is a proper coloring. The validator rejects it by replaying the
edge constraint.

## `triangle-not-2-colorable`

Expected result: `unsat`.

The checked query is the existence of a 2-coloring of `K3`. The validator
exhaustively enumerates all `2^3` assignments and confirms none satisfy every
edge constraint. A future SAT/CNF route should replace this with a checked
LRAT/DRAT certificate for the generated CNF.
