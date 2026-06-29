# End To End: Graph Cut Certificates

This lesson follows one finite graph resource from a raw edge list to edge-cut
certificates, vertex-cut certificates, rejected non-cuts, and minimum-size
replay. It uses
[graph-cut-v0](../../../artifacts/examples/math/graph-cut-v0/).

Concept rows:

- `curriculum_sets`, `curriculum_relations_and_functions`, and
  `curriculum_counting` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- `field_graph_theory` and `field_discrete_math` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `min-edge-cut-partition-witness` | `sat` | checked |
| `one-edge-cut-rejected` | `unsat` | checked |
| `min-vertex-cut-witness` | `sat` | checked |
| `one-vertex-cut-rejected` | `unsat` | checked |

Every row is a finite graph replay. The pack does not prove max-flow/min-cut,
weighted cut algorithms, spectral cuts, graph partitioning quality, or
asymptotic cut algorithms.

## The Diamond Graph

All rows use the same undirected diamond graph:

```text
vertices = s, a, b, t
edges = (s,a), (a,t), (s,b), (b,t)
source = s
target = t
```

There are two disjoint `s`-to-`t` paths:

```text
s, a, t
s, b, t
```

This makes the example useful for small certificates. Removing one edge or one
internal vertex should not separate `s` from `t`, but removing the right two
does.

## Replay A Minimum Edge Cut

The edge-cut witness gives a partition:

```text
source_side = {s}
target_side = {a, b, t}
cut_edges = (s,a), (s,b)
```

The validator checks that `(s,a)` and `(s,b)` are exactly the edges crossing
from the source side to the target side. It then removes those edges and
recomputes reachability from `s`.

After the removal, neither path can start from `s`, so `t` is unreachable.
For the minimum-size part, the validator enumerates all one-edge removals and
confirms none of them separates `s` from `t`.

## Reject A One-Edge Non-Cut

The rejected row removes only:

```text
(s,a)
```

That edge removal blocks the upper path, but the lower path remains:

```text
s, b, t
```

The validator recomputes reachability and rejects the claim that one listed
edge separates the graph.

## Replay A Minimum Vertex Cut

The vertex-cut witness removes the internal vertices:

```text
cut_vertices = {a, b}
```

The validator first checks that neither endpoint `s` nor `t` is removed.
It then removes `a` and `b` and recomputes reachability from `s` to `t`.

With both internal vertices gone, no `s`-to-`t` path remains. For the
minimum-size part, the validator enumerates every one-vertex internal removal
and confirms each still leaves a path.

## Reject A One-Vertex Non-Cut

The rejected vertex row removes only:

```text
a
```

The lower path survives:

```text
s, b, t
```

So the one-vertex cut claim is false. The checker proves the fixed row by
removing the listed vertex and replaying reachability on the remaining graph.

## Why This Matters

Cut certificates are another version of Axeyum's trust pattern:

```text
untrusted search proposes a cut set and optional partition
trusted checker removes the listed items and recomputes reachability
```

For minimum-size claims on these tiny graphs, the checker can also enumerate
all smaller candidate cuts. That is finite checked evidence, not a general
graph theorem.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-cut-v0
```

## Trust Boundary

The validator checks graph-edge membership, partition crossing edges,
non-endpoint vertex removals, reachability after removals, and exhaustive
smaller-cut enumeration for this fixed graph. General max-flow/min-cut theory
and scalable cut algorithms remain future proof or solver-resource work.
