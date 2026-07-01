# End To End: Graph Search Runtime Counters

This lesson follows one finite graph resource from ordered edge lists to BFS
and DFS visited-node counters. It uses
[graph-search-runtime-v0](../../../artifacts/examples/math/graph-search-runtime-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_graph_theory`, `field_discrete_math`, and `field_logic_and_proof` in
  the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `bfs-nearest-target-witness` | `sat` | checked |
| `dfs-long-tail-target-witness` | `sat` | checked |
| `shortcut-tail-family-costs` | `sat` | checked |
| `bad-dfs-cost-bound-rejected` | `unsat` | checked |
| `asymptotic-search-runtime-lean-horizon` | `not-run` | lean-horizon |

Every checked row is a finite cost replay over ordered finite graphs. The pack
also promotes the bad DFS-bound row into a tiny `QF_LIA` artifact checked by
Axeyum's arithmetic-DPLL evidence route. It does not prove asymptotic BFS or
DFS runtime, average-case search behavior, heuristic-search guarantees,
parallel-search properties, or graph lower bounds.

## Replay BFS To The Nearest Target

The base graph has vertices:

```text
s, a1, a2, a3, a4, t
```

and undirected edges:

```text
(s,a1), (s,t), (a1,a2), (a2,a3), (a3,a4)
```

The source is `s`, the target is `t`, and the direct shortcut edge `(s,t)`
makes the shortest distance equal to `1`.

The BFS witness counts vertices popped until the target is popped:

```text
s, a1, t
```

So the checked BFS visited count is `3`. The validator recomputes the BFS
queue order and shortest-distance map from the raw graph instead of trusting
the listed counter.

## Replay DFS Down The Long Tail

The same graph has an explicit vertex order. At `s`, deterministic DFS tries
`a1` before `t`, so it walks the tail first:

```text
s, a1, a2, a3, a4
```

Only after exhausting that branch and backtracking to `s` does DFS visit `t`:

```text
s, a1, a2, a3, a4, t
```

The checked DFS visited count is therefore `6`. This is not a contradiction
with the shortest-distance result. The graph has a distance-`1` path, but this
particular deterministic DFS order does not choose it first.

## Replay The Shortcut-Tail Family

The family row generates graphs of the form:

```text
vertices = s, a1, ..., an, t
edges = (s,a1), (s,t), (a1,a2), ..., (a(n-1),an)
```

The validator regenerates each listed graph and checks the counters:

| Tail Length | Vertex Count | BFS Visits | DFS Visits |
|---|---:|---:|---:|
| 2 | 4 | 3 | 4 |
| 4 | 6 | 3 | 6 |
| 8 | 10 | 3 | 10 |

For these finite rows, BFS stays at `3` popped vertices while deterministic
DFS visits `n + 2` vertices before reaching the target.

## Refute A Bad DFS Bound

The checked `unsat` row claims:

```text
tail_length = 4
claimed DFS upper bound = 3
actual DFS visits = 6
```

The validator reconstructs the length-four shortcut-tail graph, reruns
deterministic DFS, and rejects the claimed upper bound because the target is
not reached within three visits.

The promoted SMT-LIB artifact keeps only the integer contradiction extracted
from that replay:

```text
dfs_visits = 6
claimed_upper_bound = 3
dfs_visits <= claimed_upper_bound
```

The `math_resource_lia_routes` regression requires Axeyum to emit checked
`UnsatArithDpll` evidence for this `QF_LIA` row and independently re-check the
proof object.

This is a small but useful trust pattern:

```text
untrusted search proposes traversal counters
trusted checker recomputes the traversal from graph data
trusted proof checker rejects the extracted integer cost contradiction
```

## Why This Matters

The lesson separates three statements that are easy to blur:

- reachability: whether `t` can be reached from `s`;
- shortest path: the minimum number of edges needed to reach `t`;
- traversal cost: how many vertices a concrete algorithm visits before it
  finds `t`.

Axeyum can check all three for explicit finite instances. General runtime
theorems and asymptotic lower bounds need proof-assistant artifacts, so the
pack keeps that row at Lean-horizon status.

For the cross-pack path from reachability to traversal counters, read
[Graph Traversal Runtime Index](graph-traversal-runtime-index.md).

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-search-runtime-v0
```

## Trust Boundary

The validator rebuilds the ordered graph, recomputes deterministic adjacency,
replays BFS pop order until the target is reached, replays DFS preorder until
the target is reached, and checks the visited-node counters. The solver
regression separately checks arithmetic-DPLL evidence for the extracted
integer contradiction. The finite rows are checked evidence. The asymptotic
runtime row is metadata for future Lean work.
