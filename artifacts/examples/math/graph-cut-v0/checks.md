# Checks

## `min-edge-cut-partition-witness`

Expected result: `sat`.

The witness uses partition:

```text
source_side = {s}
target_side = {a,b,t}
cut_edges = (s,a), (s,b)
```

The validator checks that these are exactly the crossing edges, removes them,
confirms `t` is unreachable from `s`, and enumerates all one-edge removals to
prove the cut size is minimal for this graph.

## `one-edge-cut-rejected`

Expected result: `unsat`.

Removing only `(s,a)` does not separate the graph because `s-b-t` remains.

The promoted solver artifact is:

```text
artifacts/examples/math/graph-cut-v0/cnf/one-edge-cut-rejected.cnf
```

It uses variables `r_i_v` for reachability from `s` within depth `i` after
removing the proposed cut edge `(s,a)`. The remaining edges are `(a,t)`,
`(s,b)`, and `(b,t)`. The clauses force the bounded reachability fixed point
through depth `3`, then assert `!r_3_t`. Since the remaining path `s-b-t` has
length `2`, the CNF is unsatisfiable.

The shared Boolean regression:

```text
crates/axeyum-cnf/tests/math_resource_boolean_routes.rs::graph_cut_one_edge_rejected_emits_checked_drat_and_lrat
```

parses the DIMACS artifact, emits a DRAT refutation, elaborates it to LRAT, and
checks both proof objects independently.

## `min-vertex-cut-witness`

Expected result: `sat`.

The witness removes internal vertices:

```text
cut_vertices = {a,b}
```

The validator checks that neither endpoint is removed, then confirms no
one-vertex internal cut separates `s` from `t`.

## `one-vertex-cut-rejected`

Expected result: `unsat`.

Removing only `a` does not separate the graph because `s-b-t` remains.
