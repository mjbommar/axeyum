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
- [proof-methods-refutation-v0](../../../artifacts/examples/math/proof-methods-refutation-v0/)

## What Axeyum Checks

The discrete path starts with finite counting and graph coloring. The counting
pack checks fixed permutation and binomial counts, then exhaustively rejects an
injection from three pigeons into two holes. The graph coloring pack replays a
coloring witness against every edge, rejects an invalid coloring, and checks a
tiny `K3` two-colorability refutation by exhaustive finite search. The graph
reachability pack checks finite BFS distances, deterministic DFS traversal
order, disconnected no-path claims, and edge-cut separation.

This gives a direct model of "untrusted fast search, trusted small checking":
the search can propose colors, but the checker only needs the graph and the
candidate assignment. For traversal, the search can propose a path or trace,
but the checker recomputes reachability from the raw finite graph.

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

Run the check from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/counting-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
```

For a fuller trace from data row to replay result and evidence status, read
[End To End: Triangle Coloring](graph-coloring-end-to-end.md).

## Horizon

The current pigeonhole refutation is checked by finite enumeration; deterministic
CNF plus LRAT/DRAT remains the stronger certificate route. Reachability,
single-edge cut separation, and traversal traces now have a dedicated finite
pack. Matching, richer cut certificates, and d-separation still need dedicated
schemas. Extremal graph theory, graph minors, asymptotic graph families, and
runtime-pathology proofs need theorem-proving support beyond the current finite
examples.
