# Finite Graph Matching And Augmenting Paths

This pack is the third graph-theory resource after coloring and reachability. It
keeps matching theory finite and explicit:

- matching witness replay;
- invalid matching rejection when two edges share a vertex;
- augmenting-path flip replay;
- a CNF-backed perfect-matching refutation for `K3`.

The examples are deliberately small. They teach how a graph-search result can be
checked by replaying a finite certificate and, where needed, enumerating the
finite matching space.

## Concepts

- `field_graph_theory`
- `field_discrete_math`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`

## Trust Story

- Matching witnesses are checked against the original graph edge list.
- Maximum-size and perfect-matching rows are checked by exhaustive enumeration
  over the small finite graph.
- The `K3` no-perfect-matching row also has a source-linked DIMACS exact-cover
  artifact and a Boolean regression that emits and independently checks DRAT and
  LRAT proof objects.
- The augmenting-path row checks unmatched endpoints, alternating path edges,
  and the exact symmetric-difference flip.
- General matching algorithms, min-cut/max-flow theory, and graph minor theory
  remain outside this pack.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-matching-v0
```
