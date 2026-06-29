# Graph And Discrete Reasoning

Concept rows:

- `field_graph_theory`, `field_discrete_math`, and `field_logic_and_proof` in
  the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting`, `curriculum_sets`, and
  `curriculum_relations_and_functions` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [counting-v0](../../../artifacts/examples/math/counting-v0/)
- [graph-coloring-v0](../../../artifacts/examples/math/graph-coloring-v0/)
- [graph-reachability-v0](../../../artifacts/examples/math/graph-reachability-v0/)
- [graph-search-runtime-v0](../../../artifacts/examples/math/graph-search-runtime-v0/)
- [graph-matching-v0](../../../artifacts/examples/math/graph-matching-v0/)
- [graph-d-separation-v0](../../../artifacts/examples/math/graph-d-separation-v0/)
- [graph-cut-v0](../../../artifacts/examples/math/graph-cut-v0/)
- [proof-methods-refutation-v0](../../../artifacts/examples/math/proof-methods-refutation-v0/)

## What Axeyum Checks

The discrete path starts with finite counting and graph coloring. The counting
pack checks fixed permutation and binomial counts, then exhaustively rejects an
injection from three pigeons into two holes. The graph coloring pack replays a
coloring witness against every edge, rejects an invalid coloring, and checks a
tiny `K3` two-colorability refutation by exhaustive finite search. The graph
reachability pack checks finite BFS distances, deterministic DFS traversal
order, disconnected no-path claims, and edge-cut separation. The graph search
runtime pack adds finite visited-node counters for BFS and DFS target discovery,
checks a shortcut-tail family, and rejects a false DFS cost bound. The graph
matching pack checks finite matching witnesses, invalid overlapping edges,
augmenting path flips, and a perfect-matching obstruction. The DAG
d-separation pack checks chains, forks, colliders, and descendant-opened
colliders by enumerating finite skeleton paths. The graph cut pack checks
minimum edge and vertex cut certificates by replaying separation and
enumerating smaller candidate cuts.

This gives a direct model of "untrusted fast search, trusted small checking":
the search can propose colors, but the checker only needs the graph and the
candidate assignment. For traversal, the search can propose a path or trace,
but the checker recomputes reachability from the raw finite graph. For
traversal cost, the search can propose visited-count counters, but the checker
recomputes BFS pop order and DFS preorder from deterministic adjacency. For
matching, the search can propose edges or an augmenting path; the checker
verifies disjoint endpoints and enumerates the small matching space when a
maximum or obstruction is claimed. For d-separation, the search can propose an
active path, but the checker recomputes every simple path and applies the
collider/non-collider blocking rules. For cuts, the search can propose a cut
set and a partition; the checker removes edges or vertices, recomputes
reachability, and enumerates smaller cuts.

## Encode / Check Walkthrough

For counting, encode fixed integers:

```text
n = 6
k = 3
C(6,3) = C(5,2) + C(5,3)
20 = 10 + 10
```

For pigeonhole, the validator enumerates every placement of three pigeons into
two holes and confirms every placement has a collision. For graph coloring,
encode a finite graph by listing vertices, undirected edges, allowed colors, and
one assignment:

```text
vertices = a,b,c
edges = (a,b), (b,c), (a,c)
colors = red, green, blue
assignment = a:red, b:green, c:blue
```

The validator replays the assignment by checking that every edge has different
endpoint colors. For the two-colorability refutation of `K3`, the pack fixes
the same triangle with two colors and the validator exhaustively enumerates the
finite assignment space.

For reachability and traversal, encode the graph once and replay both BFS and
DFS facts against it:

```text
vertices = s, a, b, c, d, t
edges = (s,a), (a,b), (b,c), (c,d), (d,t), (s,t)
BFS shortest path = s, t
DFS order = s, a, b, c, d, t
```

The direct edge makes the BFS distance from `s` to `t` equal to `1`, while the
deterministic DFS order walks the long tail first. The validator recomputes the
distance map and the traversal order instead of trusting either list.

For traversal runtime counters, use the shortcut-tail family. The checked slice
is finite cost replay, not a general complexity theorem:

```text
vertices = s, a1, a2, a3, a4, t
edges = (s,a1), (s,t), (a1,a2), (a2,a3), (a3,a4)
BFS pop order until t = s, a1, t
DFS preorder until t = s, a1, a2, a3, a4, t
BFS visited count = 3
DFS visited count = 6
```

The family rows for tail lengths `2`, `4`, and `8` keep the BFS visited count
at `3` while the deterministic DFS visited count grows to `4`, `6`, and `10`.
The validator generates each listed graph and rejects a false claim that DFS on
the length-four graph reaches `t` within three visits.

For matching, list graph edges and the chosen matching:

```text
vertices = a, b, c, d
edges = (a,b), (b,c), (c,d)
matching = (a,b), (c,d)
augmenting path from current matching (b,c) = a, b, c, d
```

The validator checks that matching edges are real graph edges with no shared
endpoints. For the augmenting path it checks unmatched endpoints, alternating
matched/unmatched edges, and the exact flip to `(a,b), (c,d)`.

For d-separation, encode a finite DAG and a conditioning set:

```text
chain: a -> b -> c
conditioning set = {b}
query = is a d-connected to c?
```

Conditioning on the middle non-collider blocks the chain. In contrast:

```text
collider: a -> b <- c, b -> d
conditioning set = {d}
```

opens the path through `b` because `d` is a descendant of the collider.

For cut certificates, encode a finite graph, a source/target pair, and the
proposed cut:

```text
vertices = s, a, b, t
edges = (s,a), (a,t), (s,b), (b,t)
edge cut = (s,a), (s,b)
source side = {s}
target side = {a,b,t}
```

The validator checks that the cut edges are exactly the partition crossing
edges, removes them, confirms `t` is unreachable from `s`, and enumerates all
one-edge removals to justify the minimum size.

Run the check from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/counting-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-search-runtime-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-matching-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-cut-v0
```

For a fuller trace from data row to replay result and evidence status, read
[End To End: Triangle Coloring](graph-coloring-end-to-end.md).

## Horizon

The current pigeonhole refutation is checked by finite enumeration; deterministic
CNF plus LRAT/DRAT remains the stronger certificate route. Reachability,
traversal traces, finite traversal-cost counters, matching, d-separation, and
cut certificates now have dedicated finite packs. Weighted max-flow/min-cut,
extremal graph theory, graph minors, asymptotic graph families, causal
identification, average-case search, parallel search, and runtime-pathology
proofs need theorem-proving support beyond the current finite examples.
