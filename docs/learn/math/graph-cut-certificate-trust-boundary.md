# Graph Cut Certificate Trust Boundary

This page separates Axeyum's finite graph-cut resource from general cut
theorems, Menger-style duality, max-flow/min-cut, scalable cut algorithms,
spectral cuts, graph partitioning guarantees, and asymptotic claims.

Primary pack:

- [graph-cut-v0](../../../artifacts/examples/math/graph-cut-v0/)

Companion lessons and maps:

- [End To End: Graph Cut Certificates](graph-cut-end-to-end.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)
- [Max-Flow Min-Cut Theorem Boundary](max-flow-min-cut-theorem-boundary.md)

## Current Finite Resource

The pack fixes one undirected diamond graph:

```text
vertices = s, a, b, t
edges = (s,a), (a,t), (s,b), (b,t)
source = s
target = t
```

The checker does not trust a proposed cut. For edge cuts it verifies edge
membership, checks the source-side partition crossing edges, removes the listed
edges, recomputes reachability, and enumerates smaller edge removals. For
vertex cuts it refuses to remove endpoints, removes the listed internal
vertices, recomputes reachability, and enumerates smaller internal vertex
removals.

The checked resource covers:

```text
minimum edge cut:    remove (s,a), (s,b)
bad one-edge cut:    remove only (s,a), path s-b-t remains
minimum vertex cut:  remove a, b
bad one-vertex cut:  remove only a, path s-b-t remains
```

The `one-edge-cut-rejected` row also pins a source DIMACS artifact and the
Boolean CNF route that emits DRAT, elaborates to LRAT, and checks both proof
objects independently. The vertex-cut rejection and minimum-cut rows are
checked by finite replay/enumeration, not by separate source-linked CNF
artifacts.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `min-edge-cut-partition-witness` | `sat` | checked finite enumeration | The listed source-side partition yields a size-2 edge cut, and no one-edge cut separates this graph. |
| `one-edge-cut-rejected` | `unsat` | checked CNF/DRAT/LRAT | Removing only `(s,a)` leaves the path `s-b-t`, so the one-edge cut claim is false. |
| `min-vertex-cut-witness` | `sat` | checked finite enumeration | Removing internal vertices `a,b` separates this graph, and no one-internal-vertex cut does. |
| `one-vertex-cut-rejected` | `unsat` | checked finite replay | Removing only `a` leaves the path `s-b-t`, so the one-vertex cut claim is false. |

These rows prove only facts about the listed finite graph:

```text
untrusted fast search -> proposed edge cut, vertex cut, or partition
trusted small checking -> remove listed items, replay reachability, enumerate smaller cuts
theorem horizon       -> Menger, max-flow/min-cut, algorithms, and asymptotics
```

## What Is Not Proved Yet

The current pack does not prove:

- Menger's theorem or edge/vertex connectivity dualities;
- max-flow/min-cut or weighted-capacity cut optimality;
- all-pairs or global minimum-cut correctness;
- Stoer-Wagner, Karger, Ford-Fulkerson, Edmonds-Karp, Dinic, or other algorithm
  correctness;
- graph-partitioning approximation, sparsest-cut, spectral-cut, or separator
  guarantees;
- asymptotic runtime, data-structure, randomized, parallel, or dynamic-cut
  claims.

Those claims need explicit theorem statements, hypotheses, algorithms, and
no-`sorry` proof artifacts before they can graduate. The finite graph-cut rows
are teaching and regression resources, not graph-cut theorem coverage.

## Query The Boundary

Find all checked finite graph-cut rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-cut-v0 \
  --proof-status checked \
  --require-any
```

Separate accepted cut certificates from rejected non-cut claims:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-cut-v0 \
  --expected-result sat \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-cut-v0 \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

Find the source-linked Boolean CNF non-cut row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-cut-v0 \
  --route boolean \
  --proof-status checked \
  --require-any
```

Drill into the edge-cut, vertex-cut, one-edge, and one-vertex rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-cut-v0 \
  --proof-status checked \
  --text "minimum s-t edge cut" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-cut-v0 \
  --proof-status checked \
  --text "minimum internal" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-cut-v0 \
  --proof-status checked \
  --text "listed one edge" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-cut-v0 \
  --proof-status checked \
  --text "one internal vertex" \
  --require-any
```

There is intentionally no `horizon-frontier --text graph-cut` command here:
the current pack has no committed Lean-horizon row for graph-cut theorem
coverage. Use
[Max-Flow Min-Cut Theorem Boundary](max-flow-min-cut-theorem-boundary.md) for
the separate finite-flow pack that does carry a max-flow/min-cut Lean-horizon
row.

## Graduation Criteria

Graph-cut resources graduate only when they add:

1. theorem-horizon rows for Menger-style connectivity, global minimum cut,
   weighted capacities, and algorithm correctness;
2. explicit graph hypotheses for directed/undirected, weighted/unweighted,
   simple/multigraph, source-target, endpoint-removal, and global-cut variants;
3. no-`sorry` proof artifacts for each theorem claim before the display label
   changes from finite replay to theorem coverage;
4. source artifacts and checked certificates before promoting vertex-cut or
   minimum-cut rows as new solver regressions;
5. display labels that keep finite graph-cut replay, Boolean CNF evidence,
   flow/cut theorem horizons, and benchmark claims separate.

Until then, `graph-cut-v0` remains a finite checked graph resource and a compact
bridge to future cut-theory resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-cut-v0
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --expected-result sat --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --expected-result unsat --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --route boolean --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the checked-row queries
return cut certificates and rejected non-cuts, and general graph-cut theorem
coverage remains outside the current checked claim.
