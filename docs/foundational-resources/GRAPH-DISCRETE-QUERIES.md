# Graph And Discrete Resource Consumer Queries

This guide turns the finite graph rows in the foundational-resource JSON
contract into copyable downstream queries. It is a consumer-discovery layer,
not a new proof route and not an asymptotic graph-theory claim.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked graph packs match this finite graph family and proof route?
```

The current graph surface is finite and route-explicit: graph coloring,
reachability, traversal traces, BFS/DFS cost counters, matching, cuts, finite
flow/cut certificates, finite shortest-path certificates, finite DAG
topological-order certificates, and d-separation.
General graph theorems, graph minors, extremal graph theory, max-flow/min-cut,
shortest-path algorithm correctness, topological-sort algorithm correctness,
asymptotic algorithms, graph-family lower bounds, average-case traversal, and
parallel/heuristic search guarantees remain in the proof-horizon lane.

## Query Shape

Start with field summaries by route:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field graph_theory \
  --route boolean \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field graph_theory \
  --route qf-bv \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field graph_theory \
  --route LIA \
  --require-any
```

Then drill into the shared graph bridge:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_graph_replay_obstruction \
  --route <route-substring> \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_graph_replay_obstruction \
  --route <route-substring> \
  --proof-status checked \
  --require-any
```

Use `packs` for a catalog row or pack path. Use `checks` when the consumer
needs concrete checked rows to display.

## Graph Query Families

| Graph Family | Concept Filter | Route Filter | Start Query |
|---|---|---|---|
| Coloring, reachability, matching, cut, and d-separation refutations | `bridge_finite_graph_replay_obstruction` | `boolean` | `checks --concept bridge_finite_graph_replay_obstruction --route boolean --proof-status checked` |
| Fixed-width graph-coloring encodings | `bridge_finite_graph_replay_obstruction` | `qf-bv` | `checks --concept bridge_finite_graph_replay_obstruction --route qf-bv --proof-status checked` |
| BFS/DFS finite traversal cost counters | `bridge_finite_graph_replay_obstruction` | `LIA` | `checks --concept bridge_finite_graph_replay_obstruction --route LIA --proof-status checked` |
| Finite directed flow and cut certificates | `bridge_finite_graph_replay_obstruction` | `finite-model-replay`; exact rational | `checks --pack finite-flow-cut-v0 --proof-status checked` |
| Max-flow/min-cut theorem boundary | pack `finite-flow-cut-v0` | `lean-horizon` | `checks --pack finite-flow-cut-v0 --expected-result not-run --proof-status lean-horizon` |
| Finite shortest-path certificates | `bridge_finite_graph_replay_obstruction` | `finite-model-replay`; exact rational | `checks --pack finite-shortest-path-v0 --proof-status checked` |
| Shortest-path theorem boundary | pack `finite-shortest-path-v0` | `lean-horizon` | `checks --pack finite-shortest-path-v0 --expected-result not-run --proof-status lean-horizon` |
| Finite DAG topological-order certificates | `bridge_finite_graph_replay_obstruction` | `finite-model-replay` | `checks --pack finite-dag-topological-order-v0 --proof-status checked` |
| Topological-sort theorem boundary | pack `finite-dag-topological-order-v0` | `lean-horizon` | `checks --pack finite-dag-topological-order-v0 --expected-result not-run --proof-status lean-horizon` |
| Bounded family rows versus asymptotic theorem boundaries | `bridge_bounded_family_asymptotic_boundary` | `LIA`; `Farkas` | `checks --concept bridge_bounded_family_asymptotic_boundary --route LIA --proof-status checked`; `checks --concept bridge_bounded_family_asymptotic_boundary --route Farkas --proof-status checked` |
| All checked graph rows | field `graph_theory` | any route | `checks --field graph_theory --expected-result unsat --proof-status checked` |
| Runtime-specific rows | pack `graph-search-runtime-v0` | `LIA` | `checks --pack graph-search-runtime-v0 --route LIA --proof-status checked` |
| Coloring-specific rows | pack `graph-coloring-v0` | `boolean`; `qf-bv` | `checks --pack graph-coloring-v0 --route boolean --proof-status checked`; `checks --pack graph-coloring-v0 --route qf-bv --proof-status checked` |
| D-separation blocker rows | pack `graph-d-separation-v0` | `boolean` | `checks --pack graph-d-separation-v0 --route boolean --proof-status checked` |

## Copyable Examples

List all promoted finite graph packs:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field graph_theory \
  --route finite-model-replay \
  --require-any
```

Display checked Boolean graph rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_graph_replay_obstruction \
  --route boolean \
  --proof-status checked \
  --require-any
```

Display checked finite DAG d-separation blocker rows, including the
unconditioned-collider CNF route:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-d-separation-v0 \
  --route boolean \
  --proof-status checked \
  --text collider \
  --require-any
```

Display the fixed-width graph-coloring row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_graph_replay_obstruction \
  --route qf-bv \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-coloring-v0 \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

Display checked finite traversal-cost rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_graph_replay_obstruction \
  --route LIA \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack graph-search-runtime-v0 \
  --route LIA \
  --proof-status checked \
  --require-any
```

Display finite network-flow and cut-certificate rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field graph_theory \
  --text flow \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-flow-cut-v0 \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-flow-cut-v0 \
  --expected-result not-run \
  --proof-status lean-horizon \
  --require-any
```

Display finite shortest-path and potential-certificate rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field graph_theory \
  --text shortest \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-shortest-path-v0 \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-shortest-path-v0 \
  --expected-result not-run \
  --proof-status lean-horizon \
  --require-any
```

Display finite DAG topological-order and cycle-obstruction rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field graph_theory \
  --text topological \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --expected-result not-run \
  --proof-status lean-horizon \
  --require-any
```

Display bounded-family rows that are useful finite checks but not asymptotic
theorems:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field graph_theory \
  --text asymptotic \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_bounded_family_asymptotic_boundary \
  --route LIA \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_bounded_family_asymptotic_boundary \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display all checked graph-theory negative examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked graph rows, not theorem
coverage. They can support a catalog, a learner page, a route-specific
regression search, or a sibling resource that wants graph examples by finite
object family.

They do not prove:

- general graph-coloring, matching, cut, minor, or extremal graph theorems;
- max-flow/min-cut, shortest-path, or topological-sort theorem families;
- asymptotic BFS/DFS/Dijkstra/A* runtime theorems or graph-family lower
  bounds;
- average-case traversal, randomized graph algorithms, or parallel search
  guarantees;
- causal validity beyond the finite d-separation table rows;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction, or
benchmark artifacts before they can graduate.
