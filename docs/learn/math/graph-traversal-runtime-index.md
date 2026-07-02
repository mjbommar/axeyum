# Graph Traversal Runtime Index

This index keeps the BFS/DFS runtime resources honest. It connects finite
reachability, shortest-path replay, deterministic traversal traces,
topological-order replay, and visited-node counters without turning any finite
row into an asymptotic runtime theorem.

The trust pattern is:

```text
untrusted fast search -> candidate path, traversal trace, cost counter, potential, topological order, or bound
trusted small checking -> graph replay, queue/stack replay, potential replay, order/cycle replay, and checked LIA evidence
remaining horizon -> asymptotic BFS/DFS complexity, shortest-path/topological-sort algorithms, and graph-family lower bounds
```

## Concept Rows

- `bridge_finite_graph_replay_obstruction`
- `bridge_finite_counting_replay`
- `bridge_boolean_cnf_lrat_anatomy`
- `field_graph_theory`
- `field_discrete_math`
- `field_logic_and_proof`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`

These rows live in the
[Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json).

## Resource Map

| Question | Packs | Trusted Check | Horizon |
|---|---|---|---|
| Is a target reachable? | `graph-reachability-v0` | finite BFS distance and no-path replay; CNF for disconnected no-path rows | unbounded reachability theorems |
| What does deterministic DFS do? | `graph-reachability-v0`, `graph-search-runtime-v0` | ordered adjacency and DFS preorder replay | average-case or heuristic DFS behavior |
| How many vertices are visited before the target? | `graph-search-runtime-v0` | finite BFS queue pop count and DFS preorder count | asymptotic BFS/DFS runtime |
| Is a proposed traversal bound false? | `graph-search-runtime-v0` | exact counter replay plus checked QF_LIA arithmetic evidence | graph-family lower bounds |
| Is a weighted path shortest? | `finite-shortest-path-v0` | exact path-length replay plus potential lower-bound certificate | shortest-path algorithm correctness |
| Is a DAG order valid? | `finite-dag-topological-order-v0` | vertex-coverage, edge-position, cycle-obstruction replay, and the checked `2 < 1` QF_LIA edge-order contradiction | topological-sort algorithm correctness |
| Does another graph obstruction reuse the same shape? | `graph-coloring-v0`, `graph-matching-v0`, `graph-cut-v0`, `finite-flow-cut-v0`, `finite-shortest-path-v0`, `finite-dag-topological-order-v0`, `graph-d-separation-v0` | finite witness replay plus Boolean/CNF, BV, LIA, or exact-rational proof/replay rows | broad graph theory |

## Checkable Shapes

Reachability rows are finite graph facts:

```text
vertices = s, a, b, c, d, t
edges = (s,a), (a,b), (b,c), (c,d), (d,t), (s,t)
source = s
target = t
```

The checker recomputes BFS distances from the graph. A path or no-path result
is not trusted just because a resource row lists it.

Traversal-runtime rows add an ordered adjacency convention. In the
shortcut-tail graph, BFS sees the shortcut quickly while deterministic DFS
walks the ordered tail first:

```text
BFS pop order until target = s, a1, t
DFS visit order until target = s, a1, a2, a3, a4, t
```

The checker recomputes the queue or stack behavior and counts the visited
vertices. The promoted bad row extracts the final integer contradiction:

```text
dfs_visits = 6
claimed_upper_bound = 3
dfs_visits <= claimed_upper_bound
```

That contradiction is small enough for Axeyum's checked QF_LIA arithmetic
route.

## Use The Lessons

Start with
[Graph Reachability And Traversal](graph-reachability-end-to-end.md) for the
basic finite graph replay: BFS shortest distance, DFS traversal order,
disconnected no-path refutation, and edge-cut separation.

Use [Graph Reachability Certificate Trust Boundary](graph-reachability-certificate-trust-boundary.md)
when a consumer needs display wording that keeps those finite replay rows and
the disconnected no-path CNF refutation separate from BFS/DFS correctness,
all-pairs/dynamic reachability, graph-family, and asymptotic claims.

Then read
[Graph Search Runtime Counters](graph-search-runtime-end-to-end.md) for the
runtime-counter slice. It separates three statements that are often blurred:

- reachability: whether `t` can be reached from `s`;
- shortest path: the minimum edge distance to `t`;
- traversal cost: how many vertices a concrete traversal visits before `t`.

Use [Graph Search Runtime Theorem Boundary](graph-search-runtime-theorem-boundary.md)
when a consumer needs display wording that keeps finite visited-counter replay
and the QF_LIA bad-bound refutation separate from asymptotic BFS/DFS runtime,
graph-family lower bounds, average-case search, heuristic search, and parallel
search.

Use [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md) when you
want the surrounding graph-resource cluster: coloring, matching, cuts,
d-separation, counting, and proof-by-refutation.

Use [Graph Coloring Certificate Trust Boundary](graph-coloring-certificate-trust-boundary.md)
when the question is whether a fixed finite coloring claim is replay-only,
checked by edge replay, checked by Boolean CNF/LRAT, or checked by QF_BV/DRAT.
That page keeps finite coloring evidence separate from chromatic-number,
planar-coloring, algorithm, graph-minor, and asymptotic claims.

Use [Graph Matching Certificate Trust Boundary](graph-matching-certificate-trust-boundary.md)
when the question is whether proposed matching edges or an augmenting path are
valid on a fixed graph. That page keeps finite matching replay separate from
matching-theory and algorithm-correctness claims.

Use [Finite Shortest Path Certificates](finite-shortest-path-end-to-end.md)
when the question is path optimality rather than traversal order. That page
shows how exact path replay and potential inequalities certify one finite
shortest-path instance.

Use [Graph Cut Certificate Trust Boundary](graph-cut-certificate-trust-boundary.md)
when the question is whether a proposed edge or vertex removal separates a
fixed graph. That page keeps finite cut replay separate from graph-cut theorem
coverage and flow-duality claims.

Use [Finite DAG Topological Order Certificates](finite-dag-topological-order-end-to-end.md)
when the question is order feasibility on a directed acyclic graph. That page
shows how edge positions and a cycle witness are replayed without trusting a
topological-sort implementation, and how the malformed edge-order row reduces
to a checked `2 < 1` QF_LIA contradiction.

## Query It

From the repository root:

```sh
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text runtime --require-any
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_graph_replay_obstruction --route LIA --require-any
python3 scripts/query-foundational-resources.py checks --field graph_theory --route LIA --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_graph_replay_obstruction --route LIA --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --route boolean --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --route LIA --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --expected-result not-run --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --route LIA --proof-status checked --text qf-lia-bad-topological-edge-order --require-any
```

## Replay It

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-search-runtime-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-shortest-path-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dag-topological-order-v0
```

Expected shape:

```text
validated 1 foundational example pack(s)
```

for each command.

## Trust Boundary

The checked rows prove only facts about the listed finite graphs and listed
finite shortcut-tail family rows. They do not prove `O(|V| + |E|)` bounds,
shortest-path algorithm invariants, negative-cycle handling, lower bounds for
graph families, topological-sort algorithm correctness, average-case search
claims, or guarantees for heuristic and parallel search. Those remain
theorem-horizon work until there are
kernel-checked proof artifacts.
