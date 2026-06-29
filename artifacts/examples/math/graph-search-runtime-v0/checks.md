# Checks

## `bfs-nearest-target-witness`

Expected result: `sat`.

The validator recomputes BFS pop order, the shortest-distance map, and the
visited-node count until the target is popped.

## `dfs-long-tail-target-witness`

Expected result: `sat`.

The validator recomputes deterministic DFS preorder and checks that the target
is reached only after the full tail has been visited.

## `shortcut-tail-family-costs`

Expected result: `sat`.

The validator generates each shortcut-tail graph from its tail length and
recomputes BFS and DFS visited counts.

## `bad-dfs-cost-bound-rejected`

Expected result: `unsat`.

The validator rejects the claimed DFS bound because the recomputed visited
count exceeds the claimed upper bound.

## `asymptotic-search-runtime-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove asymptotic BFS/DFS complexity, lower bounds,
average-case behavior, heuristic search guarantees, or parallel-search
properties. Those require future proof artifacts.
