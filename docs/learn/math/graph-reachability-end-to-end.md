# End To End: Graph Reachability And Traversal

This lesson follows one finite graph resource from raw edge lists to shortest
paths, deterministic traversal replay, no-path refutation, and edge-cut
separation. It uses
[graph-reachability-v0](../../../artifacts/examples/math/graph-reachability-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_graph_theory` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `bfs-shortest-distance-witness` | `sat` | checked |
| `dfs-long-tail-order-replay` | `sat` | checked |
| `disconnected-no-path` | `unsat` | checked |
| `edge-cut-separates` | `sat` | checked |

Every row is a finite graph replay. The pack does not prove asymptotic runtime,
extremal graph theory, graph minors, or general graph algorithm complexity.

## Replay A Shortest Path

The main graph has vertices:

```text
s, a, b, c, d, t
```

and undirected edges:

```text
(s,a), (a,b), (b,c), (c,d), (d,t), (s,t)
```

There are two visible ways to reach `t` from `s`: the long tail

```text
s, a, b, c, d, t
```

and the direct edge:

```text
s, t
```

The witness claims the shortest path is `s, t` with distance `1`. The validator
checks the path edge-by-edge and recomputes the full BFS distance map:

```text
dist(s) = 0
dist(a) = 1
dist(t) = 1
dist(b) = 2
dist(d) = 2
dist(c) = 3
```

The important point is that the checker does not trust the proposed path or
distance. It recomputes the finite graph search from the raw edge list.

## Replay Deterministic DFS

The DFS witness uses the same graph, source, and target. With deterministic
neighbor order induced by the listed vertex order, DFS visits:

```text
s, a, b, c, d, t
```

The target `t` is discovered at index `5`, after the long tail. This is not a
contradiction with the BFS result. BFS is checking shortest distance; DFS is
checking one deterministic traversal order.

The validator recomputes the DFS preorder and confirms the target discovery
index directly.

## Refute A No-Path Claim

The checked `unsat` row uses a disconnected graph:

```text
vertices = s, a, b, t
edges = (s,a), (b,t)
source = s
target = t
```

The claim says there is an `s`-to-`t` path. The checker computes the reachable
component from `s`:

```text
reachable(s) = {s, a}
```

Since `t` is absent, the path claim is rejected. The trusted artifact is just
finite reachability replay, not a separate theorem.

## Replay An Edge Cut

The edge-cut row starts with a path graph:

```text
vertices = s, a, b, t
edges = (s,a), (a,b), (b,t)
source = s
target = t
cut_edges = (a,b)
```

Before removing the cut, `s` reaches `t`:

```text
s, a, b, t
```

After removing `(a,b)`, the reachable component from `s` is:

```text
{s, a}
```

So `t` is no longer reachable. The validator checks both halves: reachability
before the cut and non-reachability after the listed edge is removed.

## Why This Matters

Reachability is the graph version of Axeyum's general trust pattern:

```text
untrusted search proposes a path, traversal, or cut
trusted checker recomputes the finite graph fact
```

The same pattern later supports search-runtime examples, matching witnesses,
cut certificates, d-separation paths, and program-analysis control-flow traces.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
```

## Trust Boundary

The validator recomputes BFS distances, DFS preorder, reachable components,
and edge-cut separation over explicit finite graphs. The pack does not rely on
floating-point arithmetic, randomized search, or asymptotic assumptions.
General graph-theory and algorithmic complexity claims remain proof-horizon
material.
