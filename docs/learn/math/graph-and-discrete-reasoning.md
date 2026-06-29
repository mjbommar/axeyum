# Graph And Discrete Reasoning

Concept rows:

- `field_graph_theory`, `field_discrete_math`, and `field_logic_and_proof` in
  the [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_counting`, `curriculum_sets`, and
  `curriculum_relations_and_functions` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

Example packs:

- [graph-coloring-v0](../../../artifacts/examples/math/graph-coloring-v0/)
- [proof-methods-refutation-v0](../../../artifacts/examples/math/proof-methods-refutation-v0/)

## What Axeyum Checks

The graph path starts with finite coloring. A coloring witness is replayed
against every edge, an invalid coloring is rejected, and a tiny `K3`
two-colorability refutation is checked by exhaustive finite search.

This gives a direct model of "untrusted fast search, trusted small checking":
the search can propose colors, but the checker only needs the graph and the
candidate assignment.

## Encode / Check Walkthrough

Encode a finite graph by listing vertices, undirected edges, allowed colors, and
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

Run the check from the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
```

## Horizon

Reachability, matching, cuts, traversal traces, and d-separation need dedicated
pack schemas. Extremal graph theory, graph minors, asymptotic graph families,
and runtime-pathology proofs need theorem-proving support beyond the current
finite examples.
