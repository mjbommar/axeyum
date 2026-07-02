# Graph Search Runtime Theorem Boundary

This page separates Axeyum's finite BFS/DFS runtime-counter resource from
general graph-search runtime theorems, graph-family lower bounds, average-case
search, heuristic search, parallel search, and algorithm-analysis claims.

Primary pack:

- [graph-search-runtime-v0](../../../artifacts/examples/math/graph-search-runtime-v0/)

Companion lessons and maps:

- [End To End: Graph Search Runtime Counters](graph-search-runtime-end-to-end.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)
- [Graph Reachability Certificate Trust Boundary](graph-reachability-certificate-trust-boundary.md)
- [Theorem Horizon Queries](../../foundational-resources/THEOREM-HORIZON-QUERIES.md)

## Current Finite Resource

The pack fixes an ordered shortcut-tail graph and checks concrete visited-node
counters for deterministic BFS and DFS. The checker does not trust the listed
counter. It reconstructs the ordered graph, recomputes deterministic adjacency,
replays the traversal until the target is reached, and then checks the listed
integer counter.

The checked resource covers:

```text
BFS nearest-target witness:   s, a1, t                      -> 3 popped vertices
DFS long-tail witness:        s, a1, a2, a3, a4, t          -> 6 visited vertices
shortcut-tail family:         tail lengths 2,4,8            -> DFS grows in listed rows
bad DFS bound:                actual 6 <= claimed bound 3   -> QF_LIA contradiction
runtime theorem horizon:      asymptotic BFS/DFS claims      -> Lean/theorem work
```

The `bad-dfs-cost-bound-rejected` row also pins a source SMT-LIB artifact for
the extracted integer contradiction:

```text
dfs_visits = 6
claimed_upper_bound = 3
dfs_visits <= claimed_upper_bound
```

The `math_resource_lia_routes` regression emits checked QF_LIA arithmetic
evidence and independently rechecks the proof object. That proves the
extracted finite arithmetic conflict, not a general runtime theorem.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `bfs-nearest-target-witness` | `sat` | checked finite replay | BFS reaches the target through the direct shortcut after three popped vertices on this ordered graph. |
| `dfs-long-tail-target-witness` | `sat` | checked finite replay | Deterministic DFS follows the ordered tail before reaching the target on this ordered graph. |
| `shortcut-tail-family-costs` | `sat` | checked finite replay | The listed finite tail lengths have the listed BFS and DFS visited counts. |
| `bad-dfs-cost-bound-rejected` | `unsat` | checked QF_LIA arithmetic evidence | The length-four row cannot satisfy `dfs_visits <= 3` because replay computes `dfs_visits = 6`. |
| `asymptotic-search-runtime-lean-horizon` | `not-run` | Lean horizon | General BFS/DFS runtime and graph-search lower-bound claims remain future proof work. |

These rows prove only facts about the listed finite graphs and the extracted
integer contradiction:

```text
untrusted fast search -> proposed traversal counter or cost bound
trusted small checking -> BFS/DFS replay and checked QF_LIA arithmetic evidence
theorem horizon       -> asymptotic complexity, lower bounds, average case, heuristics, parallelism
```

## What Is Not Proved Yet

The current pack does not prove:

- `O(|V| + |E|)` BFS or DFS runtime for all finite graphs;
- BFS shortest-path correctness or DFS reachability correctness as general
  algorithms;
- graph-family lower bounds or worst-case complexity theorems;
- average-case, randomized, heuristic, A*, bidirectional, incremental, or
  parallel search guarantees;
- data-structure-specific queue/stack implementation bounds;
- graph-minor, extremal, dynamic-graph, or structural graph-theory claims.

Those claims need explicit algorithms, cost models, graph hypotheses, theorem
statements, and no-`sorry` proof artifacts before they can graduate. The finite
runtime rows are teaching and regression resources, not algorithm-analysis
coverage.

## Query The Boundary

Find all rows in the runtime pack:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --require-any
```

Find the checked finite replay and checked arithmetic rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --expected-result sat \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

Find the source-linked QF_LIA cost-bound refutation:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --route LIA \
  --proof-status checked \
  --require-any
```

Find the explicit theorem horizon:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text BFS \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --expected-result not-run \
  --proof-status lean-horizon \
  --require-any
```

Drill into the BFS, DFS, shortcut-family, and false-bound rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --text BFS \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --text DFS \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --text shortcut \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --text "at most three" \
  --require-any
```

## Graduation Criteria

Graph-search runtime resources graduate only when they add:

1. theorem-horizon rows for BFS runtime, DFS runtime, graph-family lower
   bounds, average-case search, heuristic search, and parallel search;
2. explicit algorithm and cost-model definitions, including adjacency
   representation and queue/stack implementation assumptions;
3. no-`sorry` proof artifacts for each theorem claim before the display label
   changes from finite replay to theorem coverage;
4. Lean or other kernel-checked reconstruction that links finite cost-counter
   replay to a general theorem statement when such a theorem is claimed;
5. display labels that keep finite counter replay, QF_LIA cost contradictions,
   theorem horizons, and benchmark claims separate.

Until then, `graph-search-runtime-v0` remains a finite checked runtime-counter
resource and a compact bridge to future graph-search theorem resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-search-runtime-v0
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --route LIA --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --expected-result not-run --proof-status lean-horizon --require-any
```

Expected resource boundary: the finite runtime rows validate, the bad DFS
bound is checked as a QF_LIA arithmetic contradiction, and asymptotic graph
search runtime remains an explicit Lean/theorem horizon.
