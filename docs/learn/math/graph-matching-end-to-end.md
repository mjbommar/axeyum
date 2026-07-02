# End To End: Graph Matching And Augmenting Paths

This lesson follows one finite graph resource from raw edge lists to matching
witness replay, invalid-matching rejection, augmenting-path replay, and a
perfect-matching refutation. It uses
[graph-matching-v0](../../../artifacts/examples/math/graph-matching-v0/).
For the broader boundary between these finite matching checks and matching
theory or algorithm claims, read
[Graph Matching Certificate Trust Boundary](graph-matching-certificate-trust-boundary.md).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_graph_theory` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `matching-size-two-witness` | `sat` | checked |
| `overlapping-matching-rejected` | `unsat` | checked |
| `augmenting-path-improves` | `sat` | checked |
| `triangle-no-perfect-matching` | `unsat` | checked |

Every row is a finite graph check. The pack does not prove Edmonds matching,
weighted matching, bipartite matching duality, min-cut/max-flow, graph minors,
or general matching-algorithm complexity.

## Replay A Matching Witness

The first graph is a four-vertex path:

```text
vertices = a, b, c, d
edges = (a,b), (b,c), (c,d)
```

The witness proposes the matching:

```text
(a,b), (c,d)
```

The validator checks three things:

- each listed pair is a real graph edge;
- no vertex appears in two matching edges;
- no larger matching exists in this finite graph.

The maximum-size check is important. The checker does not merely count the
submitted edges; it enumerates the small matching space and confirms size `2`
is maximal.

## Reject Overlapping Edges

The invalid row uses a triangle graph:

```text
vertices = a, b, c
edges = (a,b), (b,c), (a,c)
```

and proposes:

```text
(a,b), (b,c)
```

Both pairs are real graph edges, but they share vertex `b`. The validator
therefore rejects the claim that they form a matching.

This is a semantic rejection, not a parsing or well-formedness rejection. The
edge list is valid; the matching predicate is false.

## Replay An Augmenting Path

The augmenting-path row returns to the path graph:

```text
a - b - c - d
```

The current matching is:

```text
(b,c)
```

The proposed augmenting path is:

```text
a, b, c, d
```

The validator checks that the endpoints `a` and `d` are unmatched, then checks
the alternating pattern:

```text
(a,b) is unmatched
(b,c) is matched
(c,d) is unmatched
```

Flipping along the path removes `(b,c)` and adds `(a,b)` plus `(c,d)`:

```text
old matching = (b,c)
new matching = (a,b), (c,d)
```

The checked result is a size-`1` matching improved to a size-`2` matching.

## Refute A Perfect Matching In K3

The final row asks whether the triangle `K3` has a perfect matching:

```text
vertices = a, b, c
edges = (a,b), (b,c), (a,c)
```

Any matching can use at most one edge, because every pair of edges in `K3`
shares a vertex. A one-edge matching covers only two of the three vertices.
The validator enumerates all matchings and confirms the maximum size is `1`,
so the perfect-matching claim is rejected.

## Why This Matters

Matching examples show the same trust split as the graph-search packs:

```text
untrusted search proposes edges or an augmenting path
trusted checker replays local constraints and finite enumeration
```

The useful pattern is not that the graph is large or the algorithm is clever.
The useful pattern is that a proposed matching certificate is small and
replayable against the original graph.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-matching-v0
```

## Trust Boundary

The validator checks graph-edge membership, endpoint disjointness, vertex
coverage, augmenting-path alternation, symmetric-difference flips, and
small-graph matching enumeration. General matching theorems and scalable
algorithm guarantees remain outside this finite pack.
