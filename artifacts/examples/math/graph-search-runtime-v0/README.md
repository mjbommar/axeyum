# Graph Search Runtime V0

This pack adds finite runtime-counter checks for deterministic BFS and DFS on
ordered finite graphs. It complements `graph-reachability-v0`: that pack checks
reachability and traversal correctness, while this pack records concrete
visited-node costs for a small worst-case-shaped family.

The examples are:

- a BFS nearest-target witness on a graph with a direct shortcut;
- a DFS long-tail witness on the same ordered graph;
- a finite family table showing DFS visited-count growth while BFS stays small;
- checked rejection of a false DFS cost bound;
- an asymptotic graph-search Lean-horizon row.

## Concepts

- `field_graph_theory`
- `field_discrete_math`
- `field_logic_and_proof`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`

## Trust Story

The validator rebuilds the ordered graph, recomputes deterministic adjacency,
replays BFS pop order until the target is reached, replays DFS preorder until
the target is reached, and checks every listed visited-count counter. The family
row is checked by generating the same shortcut-plus-tail graph for each listed
tail length.

The bad-bound row is also a solver-backed resource. Its SMT-LIB artifact is
[`smt2/bad-dfs-cost-bound-lia-conflict.smt2`](smt2/bad-dfs-cost-bound-lia-conflict.smt2):
it encodes `dfs_visits = 6`, `claimed_upper_bound = 3`, and
`dfs_visits <= claimed_upper_bound` as a tiny `QF_LIA` contradiction. The
`math_resource_lia_routes` regression requires Axeyum to emit checked
QF_LIA arithmetic evidence and independently re-check the proof object.

This pack is finite checked evidence. It is not a proof of asymptotic graph
search complexity, average-case behavior, heuristic search, parallel search, or
algorithmic lower bounds.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-search-runtime-v0
```
