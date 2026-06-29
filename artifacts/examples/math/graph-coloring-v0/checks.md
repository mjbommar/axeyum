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
edge constraint.

The pack also carries
[`cnf/triangle-not-2-colorable.cnf`](cnf/triangle-not-2-colorable.cnf), a
deterministic DIMACS encoding of the same refutation. The focused regression

```sh
cargo test -p axeyum-cnf --test math_resource_boolean_routes graph_coloring_triangle_not_2_colorable_emits_checked_drat_and_lrat
```

parses that CNF, emits a DRAT proof with untrusted search, checks the DRAT proof
independently, elaborates it to LRAT, and checks the LRAT proof independently.
