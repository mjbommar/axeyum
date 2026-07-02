# Graph Matching Certificate Trust Boundary

This page separates Axeyum's finite graph-matching resource from general
matching theory, Edmonds-style blossom algorithms, bipartite matching duality,
Hall/Tutte theorem coverage, weighted matching, flow reductions, graph minors,
and asymptotic algorithm claims.

Primary pack:

- [graph-matching-v0](../../../artifacts/examples/math/graph-matching-v0/)

Companion lessons and maps:

- [End To End: Graph Matching And Augmenting Paths](graph-matching-end-to-end.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)
- [Graph Cut Certificate Trust Boundary](graph-cut-certificate-trust-boundary.md)

## Current Finite Resource

The pack fixes small unweighted graphs and checks matching claims directly
against the listed edge sets. The checker does not trust the submitted edge
list or augmenting path. It verifies edge membership, endpoint disjointness,
covered vertices, alternating-path structure, symmetric-difference flips, and
finite matching enumeration.

The checked resource covers:

```text
path P4 maximum matching:   (a,b), (c,d)
invalid matching:           (a,b), (b,c) share vertex b
augmenting path:            a-b-c-d flips (b,c) into (a,b),(c,d)
K3 no perfect matching:     no one-edge matching covers all three vertices
```

The `triangle-no-perfect-matching` row also pins a source DIMACS exact-cover
artifact and the Boolean CNF route that emits DRAT, elaborates to LRAT, and
checks both proof objects independently. The maximum-matching, overlap
rejection, and augmenting-path rows are checked by finite replay/enumeration,
not by separate source-linked CNF artifacts.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `matching-size-two-witness` | `sat` | checked finite enumeration | The listed `P4` matching is valid and no larger matching exists in that finite graph. |
| `overlapping-matching-rejected` | `unsat` | checked finite replay | The listed edges are real graph edges but share vertex `b`, so they are not a matching. |
| `augmenting-path-improves` | `sat` | checked finite replay | The listed alternating path has unmatched endpoints and flips a size-1 matching into size 2. |
| `triangle-no-perfect-matching` | `unsat` | checked CNF/DRAT/LRAT | The `K3` exact-cover encoding is unsatisfiable because one edge cannot cover all three vertices. |

These rows prove only facts about the listed finite graphs:

```text
untrusted fast search -> proposed matching, augmenting path, or perfect-matching claim
trusted small checking -> edge replay, disjointness replay, finite enumeration, and CNF evidence
theorem horizon       -> Hall, Tutte, Edmonds, weighted matching, and algorithm complexity
```

## What Is Not Proved Yet

The current pack does not prove:

- Hall's marriage theorem or bipartite matching duality;
- Tutte's theorem or perfect-matching characterizations;
- Berge's augmenting-path theorem as a general optimality criterion;
- Edmonds blossom, Hopcroft-Karp, Hungarian, or weighted-matching algorithm
  correctness;
- reductions between matching, flow, cut, matroid, or LP duality frameworks;
- approximation, randomized, parallel, dynamic, or asymptotic matching claims.

Those claims need explicit theorem statements, hypotheses, algorithms, and
no-`sorry` proof artifacts before they can graduate. The finite matching rows
are teaching and regression resources, not general matching theorem coverage.

## Query The Boundary

Find all checked finite matching rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-matching-v0 \
  --proof-status checked \
  --require-any
```

Separate witnesses from rejected matching claims:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-matching-v0 \
  --expected-result sat \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-matching-v0 \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

Find the source-linked Boolean CNF perfect-matching refutation:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-matching-v0 \
  --route boolean \
  --proof-status checked \
  --require-any
```

Drill into the maximum matching, overlap rejection, augmenting path, and `K3`
perfect-matching refutation:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-matching-v0 \
  --proof-status checked \
  --text "maximum matching" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-matching-v0 \
  --proof-status checked \
  --text "two edges" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-matching-v0 \
  --proof-status checked \
  --text augmenting \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-matching-v0 \
  --proof-status checked \
  --text "triangle K3" \
  --require-any
```

There is intentionally no `horizon-frontier --text matching` command here: the
current pack has no committed Lean-horizon row for matching theorem coverage.
Consumers should display the current rows as checked finite graph evidence, not
as theorem-boundary coverage.

## Graduation Criteria

Graph-matching resources graduate only when they add:

1. theorem-horizon rows for Hall, Tutte, Berge augmenting paths, weighted
   matching duality, and representative algorithm correctness;
2. explicit graph hypotheses for bipartite/non-bipartite, weighted/unweighted,
   simple/multigraph, perfect/maximum/cardinality/weighted variants;
3. no-`sorry` proof artifacts for each theorem claim before the display label
   changes from finite replay to theorem coverage;
4. source artifacts and checked certificates before promoting overlap,
   augmenting-path, or maximum-matching rows as additional solver regressions;
5. display labels that keep finite matching replay, Boolean CNF evidence,
   theorem horizons, flow/cut analogies, and benchmark claims separate.

Until then, `graph-matching-v0` remains a finite checked graph resource and a
compact bridge to future matching-theory resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-matching-v0
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --expected-result sat --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --expected-result unsat --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --route boolean --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the checked-row queries
return matching witnesses and rejected claims, and general matching theory
remains outside the current checked claim.
