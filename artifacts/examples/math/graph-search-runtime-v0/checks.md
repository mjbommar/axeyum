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

The promoted solver artifact is
`artifacts/examples/math/graph-search-runtime-v0/smt2/bad-dfs-cost-bound-lia-conflict.smt2`.
It fixes `tail_length = 4`, `actual_dfs_visited_until_target = 6`,
`actual_bfs_visited_until_target = 3`, and `claimed_upper_bound = 3`, then
checks that `crates/axeyum-solver/tests/math_resource_lia_routes.rs` emits and
independently verifies arithmetic-DPLL evidence for the resulting `QF_LIA`
contradiction.

## `asymptotic-search-runtime-lean-horizon`

Expected result: `not-run`.

The finite checks do not prove asymptotic BFS/DFS complexity, lower bounds,
average-case behavior, heuristic search guarantees, or parallel-search
properties. Those require future proof artifacts.
