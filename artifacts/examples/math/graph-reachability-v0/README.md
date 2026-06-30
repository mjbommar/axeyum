# Finite Graph Reachability And Traversal

This pack is the second graph-theory resource after graph coloring. It keeps the
examples finite and explicit:

- shortest-path distance by BFS replay;
- deterministic DFS traversal order replay;
- a CNF-backed no-path refutation in a disconnected graph;
- edge-cut separation replay.

The point is not to prove asymptotic graph theory. The point is to show how a
finite graph claim can be reduced to a small replayable artifact.

## Concepts

- `field_graph_theory`
- `field_discrete_math`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`

## Trust Story

- BFS and DFS witnesses are checked by recomputing the traversal from the raw
  graph.
- The disconnected no-path row is checked by finite reachability from the
  source component.
- The disconnected no-path row also has a source-linked bounded reachability
  fixed-point DIMACS artifact and a Boolean regression that emits and
  independently checks DRAT and LRAT proof objects.
- The edge-cut row is checked by confirming reachability before the cut and
  non-reachability after removing the cut edge.
- Asymptotic runtime and extremal graph claims remain theorem-prover horizons,
  not claims made by this pack.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
```
