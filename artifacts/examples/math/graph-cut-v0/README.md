# Finite Graph Cut Certificates

This pack completes the first graph-theory expansion loop after coloring,
reachability, matching, and d-separation. It keeps cut claims finite and
checkable:

- a minimum `s-t` edge cut with a partition certificate;
- rejection of a one-edge non-cut;
- a minimum internal vertex cut;
- rejection of a one-vertex non-cut.

The validator recomputes reachability after removals and enumerates all smaller
candidate cuts on the small graph.

## Concepts

- `field_graph_theory`
- `field_discrete_math`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`

## Trust Story

- Edge-cut witnesses are checked against the original graph, the listed
  partition, and exhaustive smaller-cut enumeration.
- Vertex-cut witnesses are checked by removing only non-source/non-target
  vertices and enumerating smaller internal cuts.
- The pack does not claim max-flow/min-cut theorem coverage; that remains a
  later proof-object or theorem-prover target.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-cut-v0
```
