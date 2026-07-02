# Topological Sort Theorem Boundary

This page separates Axeyum's finite DAG topological-order resource from
general topological-sort algorithm correctness, finite linear-extension
existence, cycle-obstruction completeness, partial-order theory, and
asymptotic runtime claims.

Primary pack:

- [finite-dag-topological-order-v0](../../../artifacts/examples/math/finite-dag-topological-order-v0/)

Companion lessons and maps:

- [End To End: Finite DAG Topological Order Certificates](finite-dag-topological-order-end-to-end.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)
- [Sets, Relations, And Finite Structures](sets-relations-and-finite-structures.md)

## Current Finite Resource

The pack fixes one tiny prerequisite DAG:

```text
intro -> algebra
intro -> analysis
algebra -> topology
analysis -> topology
topology -> thesis
```

The checker accepts an order only when:

```text
every vertex appears exactly once
every directed edge u -> v places u before v
```

Two concrete orders check:

```text
intro, algebra, analysis, topology, thesis
intro, analysis, algebra, topology, thesis
```

The second order is valid because `algebra` and `analysis` are incomparable in
the listed DAG.

The pack also fixes two rejected finite claims:

```text
bad order: intro, topology, algebra, analysis, thesis
violating edge: algebra -> topology

cycle obstruction: a -> b -> c -> a
```

Those rows certify only this listed finite DAG and listed finite cycle. They do
not prove the finite DAG linear-extension theorem or any topological-sort
algorithm.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `topological-order-witness` | `sat` | checked | The listed prerequisite order covers every vertex once and respects every edge. |
| `independent-swap-order-witness` | `sat` | checked | The swapped `algebra`/`analysis` order checks because those vertices are incomparable. |
| `bad-order-rejected` | `unsat` | checked | The malformed order puts `topology` before `algebra`, violating `algebra -> topology`. |
| `qf-lia-bad-topological-edge-order` | `unsat` | checked | The source-linked QF_LIA artifact fixes `algebra_position = 2`, `topology_position = 1`, and the required edge inequality, yielding `2 < 1`. |
| `cycle-obstruction-rejected` | `unsat` | checked | The directed cycle `a -> b -> c -> a` obstructs a topological order for that finite graph. |
| `topological-sort-theorem-lean-horizon` | `not-run` | lean-horizon | General topological-sort correctness and linear-extension existence remain future proof-assistant work. |

The checked finite rows are deterministic exact replay. The bad edge-order row
also has a committed QF_LIA artifact and route regression, so the pack is now a
promoted solver-reuse resource. That promotion is narrow: it covers the listed
`2 < 1` edge-order contradiction while the general theorem row remains
`lean-horizon`.

## What Is Not Proved Yet

The current pack does not prove:

- every finite DAG has a topological order;
- every directed cycle obstructs every topological order, in both directions
  as a complete characterization;
- Kahn's algorithm correctness;
- DFS finishing-time topological-sort correctness;
- cycle-detection completeness;
- partial-order dimension or linear-extension counting;
- asymptotic runtime or data-structure guarantees;
- incremental or dynamic topological-order maintenance.

Those claims need theorem statements with explicit finite-graph, acyclicity,
cycle, order, and algorithm hypotheses plus no-`sorry` Lean artifacts before
they can graduate from horizon rows. The finite topological-order rows are
exact checked examples and teaching resources, not proof evidence for the full
algorithm family.

## Query The Boundary

Find topological-sort theorem-horizon rows and finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "topological-sort" \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite replay rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --proof-status checked \
  --require-any
```

Find the source-linked QF_LIA edge-order contradiction:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --route LIA \
  --proof-status checked \
  --text qf-lia-bad-topological-edge-order \
  --require-any
```

Drill into the checked finite order, alternate order, bad-order, and cycle rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --proof-status checked \
  --text "every vertex appears once" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --proof-status checked \
  --text "no edge between algebra and analysis" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --proof-status checked \
  --text "algebra must precede" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-dag-topological-order-v0 \
  --proof-status checked \
  --text "directed cycle" \
  --require-any
```

## Graduation Criteria

General topological-sort resources graduate only when they add:

1. precise Lean theorem statements for finite DAG linear-extension existence,
   cycle obstruction, Kahn/DFS invariants, and optional counting or
   partial-order variants;
2. explicit hypotheses for finite directed graphs, vertex coverage,
   acyclicity, cycles, total orders, and algorithm state;
3. no-`sorry` proofs with an axiom audit;
4. source Boolean/LIA artifacts plus checked certificate routes before
   promoting additional malformed-order, cycle, or algorithm rows as solver
   regressions;
5. display labels that keep finite replay, route certificates, theorem rows,
   and benchmark claims separate.

Until then, topological-order rows remain bounded/computable resources:

```text
untrusted fast search -> proposed vertex order, cycle, or malformed order claim
trusted small checking -> exact vertex coverage, edge-position, and cycle replay
theorem horizon       -> finite DAG theorem and topological-sort correctness
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dag-topological-order-v0
cargo test -p axeyum-solver --test math_resource_lia_routes finite_dag_topological_bad_edge_order_emits_checked_lia_evidence
python3 scripts/query-foundational-resources.py horizon-frontier --text "topological-sort" --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --route LIA --proof-status checked --text qf-lia-bad-topological-edge-order --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
topological-sort theorem row remains `lean-horizon`; the promoted QF_LIA row is
only the checked finite edge-order contradiction.
