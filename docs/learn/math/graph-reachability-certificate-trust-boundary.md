# Graph Reachability Certificate Trust Boundary

This page separates Axeyum's finite graph-reachability resource from general
reachability theory, BFS/DFS algorithm correctness, shortest-path theorems,
graph-family lower bounds, graph minors, and asymptotic runtime claims.

Primary pack:

- [graph-reachability-v0](../../../artifacts/examples/math/graph-reachability-v0/)

Companion lessons and maps:

- [End To End: Graph Reachability And Traversal](graph-reachability-end-to-end.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Graph Search Runtime Counters](graph-search-runtime-end-to-end.md)

## Current Finite Resource

The pack fixes small undirected graphs and checks reachability claims directly
against the listed vertex and edge sets. The checker does not trust a proposed
path, traversal order, distance, no-path claim, or edge cut. It recomputes the
finite graph fact from the source data:

```text
BFS distance map       -> recompute all distances from s
DFS preorder           -> replay deterministic neighbor order
no-path refutation     -> recompute the reachable component from s
edge-cut separation    -> replay reachability before and after edge removal
```

The checked resource covers:

```text
shortest path:    direct edge s-t has distance 1
DFS long tail:    ordered DFS visits s,a,b,c,d,t before discovering t
disconnected:     no s-to-t path exists in the listed disconnected graph
edge cut:         removing (a,b) separates s from t in a path graph
```

The `disconnected-no-path` row also pins a source DIMACS bounded-reachability
artifact and the Boolean CNF route that emits DRAT, elaborates to LRAT, and
checks both proof objects independently. The BFS witness, deterministic DFS
witness, and edge-cut row are checked by finite replay, not by separate
source-linked CNF artifacts.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `bfs-shortest-distance-witness` | `sat` | checked finite BFS replay | The listed path `s,t` is valid and the recomputed BFS distance from `s` to `t` is 1. |
| `dfs-long-tail-order-replay` | `sat` | checked deterministic DFS replay | With the listed vertex order, DFS discovers `t` only after visiting the long tail. |
| `disconnected-no-path` | `unsat` | checked CNF/DRAT/LRAT plus reachability replay | The disconnected graph has no `s`-to-`t` path; the bounded fixed-point CNF is unsatisfiable. |
| `edge-cut-separates` | `sat` | checked finite edge-cut replay | `s` reaches `t` before removing `(a,b)`, and cannot reach `t` after that edge is removed. |

These rows prove only facts about the listed finite graphs:

```text
untrusted fast search -> proposed path, distance, traversal order, or cut
trusted small checking -> BFS/DFS/reachability replay and checked CNF evidence
theorem horizon       -> BFS/DFS correctness, graph algorithms, graph families, and asymptotics
```

## What Is Not Proved Yet

The current pack does not prove:

- BFS shortest-path correctness for all finite unweighted graphs;
- DFS reachability or traversal-order properties as general algorithms;
- `O(|V| + |E|)` BFS/DFS runtime bounds;
- all-pairs reachability, transitive closure, dynamic reachability, or
  parallel reachability algorithms;
- graph-family lower bounds, extremal graph theory, graph minors, or
  structural graph theory claims;
- average-case, randomized, heuristic, or probabilistic search guarantees;
- shortest-path theorem coverage beyond the fixed unweighted examples here.

Those claims need explicit theorem statements, hypotheses, algorithms, and
no-`sorry` proof artifacts before they can graduate. The finite reachability
rows are teaching and regression resources, not general graph-search theorem
coverage.

## Query The Boundary

Find all checked finite reachability rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-reachability-v0 \
  --proof-status checked \
  --require-any
```

Separate accepted witnesses from the rejected no-path claim:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-reachability-v0 \
  --expected-result sat \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-reachability-v0 \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

Find the source-linked Boolean CNF no-path refutation:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-reachability-v0 \
  --route boolean \
  --proof-status checked \
  --require-any
```

Drill into the BFS distance, DFS order, disconnected no-path, and edge-cut
rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-reachability-v0 \
  --proof-status checked \
  --text "shortest path" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-reachability-v0 \
  --proof-status checked \
  --text DFS \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-reachability-v0 \
  --proof-status checked \
  --text disconnected \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-reachability-v0 \
  --proof-status checked \
  --text "edge cut" \
  --require-any
```

There is intentionally no `horizon-frontier --text reachability` command here:
the current pack has no committed Lean-horizon row for general reachability or
BFS/DFS correctness. Consumers should display the current rows as checked
finite graph evidence, not as theorem-boundary coverage.

## Graduation Criteria

Graph-reachability resources graduate only when they add:

1. theorem-horizon rows for BFS shortest-path correctness, DFS reachability
   correctness, transitive closure, and asymptotic graph-search bounds;
2. explicit graph hypotheses for directed/undirected, weighted/unweighted,
   simple/multigraph, source-target, all-pairs, and dynamic variants;
3. no-`sorry` proof artifacts for each theorem claim before the display label
   changes from finite replay to theorem coverage;
4. source artifacts and checked certificates before promoting additional
   BFS/DFS or edge-cut rows as solver regressions;
5. display labels that keep finite replay, Boolean CNF evidence, algorithm
   theorem horizons, and benchmark claims separate.

Until then, `graph-reachability-v0` remains a finite checked graph resource and
a compact bridge to future graph-search theorem resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --expected-result sat --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --expected-result unsat --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --route boolean --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the checked-row queries
return reachability witnesses and the disconnected no-path refutation, and
general graph-search theorem coverage remains outside the current checked
claim.
