# Checks

## `bfs-shortest-distance-witness`

Expected result: `sat`.

The witness lists a path `s -> t`, a claimed distance of `1`, and a full BFS
distance map. The validator checks that every path step is an edge and then
recomputes BFS distances from the graph.

## `dfs-long-tail-order-replay`

Expected result: `sat`.

The witness lists the deterministic DFS preorder:

```text
s, a, b, c, d, t
```

The validator recomputes DFS using the listed vertex order as neighbor order and
checks that `t` is discovered later than the BFS distance.

## `disconnected-no-path`

Expected result: `unsat`.

The claim says an `s -> t` path exists in a graph whose source and target are in
different connected components. The validator recomputes the reachable
component from `s` and confirms that `t` is absent.

The promoted solver artifact is:

```text
artifacts/examples/math/graph-reachability-v0/cnf/disconnected-no-path.cnf
```

It uses variables `r_i_v` for reachability from `s` within depth `i`, with
depths `0..3` over the vertex order `s, a, b, t`. The clauses force the
bounded reachability fixed point for the graph edges `(s,a)` and `(b,t)`, then
assert `r_3_t`. Because every simple path in a four-vertex graph has length at
most three, this is a complete finite no-path obstruction for the fixed row.

The shared Boolean regression:

```text
crates/axeyum-cnf/tests/math_resource_boolean_routes.rs::graph_reachability_disconnected_no_path_emits_checked_drat_and_lrat
```

parses the DIMACS artifact, emits a DRAT refutation, elaborates it to LRAT, and
checks both proof objects independently.

## `edge-cut-separates`

Expected result: `sat`.

The validator checks that `s` can reach `t` in the original graph, removes the
listed cut edge, and checks that `t` is no longer reachable.
