# Graph Coloring Certificate Trust Boundary

This page separates Axeyum's finite graph-coloring resource from general
coloring theory, chromatic-number theorems, planar graph coloring, list/color
variants, coloring algorithms, graph minors, and asymptotic claims.

Primary pack:

- [graph-coloring-v0](../../../artifacts/examples/math/graph-coloring-v0/)

Companion lessons and maps:

- [End To End: Triangle Coloring](graph-coloring-end-to-end.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)
- [Proof Route Learner Snippets](proof-route-learner-snippets.md)

## Current Finite Resource

The pack fixes tiny explicit graphs and checks coloring claims against the
listed vertices, edges, colors, and assignments. The checker does not trust a
proposed coloring or non-colorability claim. It either replays the finite
assignment edge by edge, enumerates the small coloring space, or checks a
source-linked certificate route:

```text
proper coloring witness      -> edge-by-edge finite replay
bad same-color assignment    -> edge replay rejects a monochromatic edge
K3 not 2-colorable           -> exhaustive finite coloring plus CNF/DRAT/LRAT
K3 not 2-colorable, 1-bit BV -> QF_BV bit-blast plus checked DRAT
```

The checked resource covers:

```text
triangle 3-coloring:     replay-only witness over red, green, blue
bad one-edge coloring:   checked rejection of red-red on a single edge
triangle 2-coloring:     checked Boolean CNF/DRAT/LRAT non-colorability
triangle 1-bit BV route: checked QF_BV/DRAT bit-blasted non-colorability
```

The `triangle-not-2-colorable` row pins a source DIMACS artifact and the
Boolean CNF route that emits DRAT, elaborates to LRAT, and checks both proof
objects independently. The `triangle-not-2-colorable-qf-bv-drat` row pins a
source SMT-LIB artifact and checks the generated bit-blasted DRAT certificate.
The `triangle-3-coloring-witness` row is replay-only: it validates the listed
model, but it is not a proof that `K3` needs exactly three colors.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `triangle-3-coloring-witness` | `sat` | replay-only | The listed 3-color assignment satisfies every edge in this finite triangle. |
| `bad-edge-coloring-rejected` | `unsat` | checked finite replay | The one-edge graph has a monochromatic edge under the listed assignment. |
| `triangle-not-2-colorable` | `unsat` | checked CNF/DRAT/LRAT | The Boolean encoding of 2-coloring `K3` is unsatisfiable. |
| `triangle-not-2-colorable-qf-bv-drat` | `unsat` | checked QF_BV/DRAT | The 1-bit BV encoding of the same 2-coloring obstruction bit-blasts to a checked DRAT refutation. |

These rows prove only facts about the listed finite graphs and encodings:

```text
untrusted fast search -> candidate coloring, SAT proof, or BV proof
trusted small checking -> edge replay, exhaustive finite search, DRAT/LRAT, and BV DRAT checks
theorem horizon       -> chromatic-number theorems, planar coloring, algorithms, and graph minors
```

## What Is Not Proved Yet

The current pack does not prove:

- `chi(K3) = 3` as a general chromatic-number theorem;
- graph-colorability complexity or NP-completeness;
- two-colorability equivalence with bipartiteness for all finite graphs;
- Brooks, Perfect Graph, Four Color, Five Color, or list-coloring theorems;
- coloring algorithm correctness, branch-and-bound completeness, or heuristic
  guarantees;
- graph-minor, planar, random-graph, dynamic, parallel, or asymptotic coloring
  claims;
- Lean reconstruction of the original graph-coloring theorem from the Boolean
  or QF_BV lowering steps.

Those claims need explicit theorem statements, hypotheses, algorithms, and
no-`sorry` proof artifacts before they can graduate. The finite coloring rows
are teaching and regression resources, not graph-coloring theorem coverage.

## Query The Boundary

Find all graph-coloring rows, including the replay-only witness:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --require-any
```

Find the checked finite and certificate-backed rejections:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --proof-status checked \
  --require-any
```

Separate the replay-only model witness from checked refutations:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --expected-result sat \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --proof-status replay-only \
  --require-any
```

Find the Boolean CNF/LRAT and QF_BV/DRAT proof routes:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

Drill into the same-color rejection, triangle 2-coloring obstruction, and
1-bit BV route:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --text "same-color" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --text "proper 2-coloring" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --text "1-bit BV" \
  --require-any
```

There is intentionally no `horizon-frontier --text coloring` command here: the
current pack has no committed Lean-horizon row for graph-coloring theorem
coverage. Consumers should display the current rows as finite replay and
checked certificate evidence, not as chromatic-number theorem coverage.

## Graduation Criteria

Graph-coloring resources graduate only when they add:

1. theorem-horizon rows for chromatic number, bipartite two-coloring,
   planar/four-color-style boundaries, and representative algorithm
   correctness;
2. explicit graph hypotheses for simple/multigraph, directed/undirected,
   list/color variants, finite/infinite graphs, and fixed-width encodings;
3. no-`sorry` proof artifacts for each theorem claim before the display label
   changes from finite replay to theorem coverage;
4. Lean or other kernel-checked reconstruction that discharges the Boolean and
   QF_BV lowering steps before the certificate route is advertised as a proof
   of the original graph theorem;
5. display labels that keep replay-only witnesses, checked finite rejections,
   Boolean CNF evidence, QF_BV evidence, theorem horizons, and benchmark
   claims separate.

Until then, `graph-coloring-v0` remains a finite checked graph resource and a
compact bridge to future graph-coloring theorem resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --route boolean --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --route qf-bv --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the checked-row queries
return the same-color rejection plus Boolean and QF_BV non-colorability rows,
the 3-coloring witness remains replay-only, and general graph-coloring theorem
coverage remains outside the current checked claim.
