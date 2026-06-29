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

## `edge-cut-separates`

Expected result: `sat`.

The validator checks that `s` can reach `t` in the original graph, removes the
listed cut edge, and checks that `t` is no longer reachable.
