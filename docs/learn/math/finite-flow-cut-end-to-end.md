# End To End: Finite Flow And Cut Certificates

This lesson follows one capacitated directed graph from an explicit feasible
flow to a finite cut certificate and two rejected malformed claims. It uses
[finite-flow-cut-v0](../../../artifacts/examples/math/finite-flow-cut-v0/).

Concept rows:

- `field_graph_theory`, `field_discrete_math`,
  `field_optimization_and_convexity`, and `field_linear_algebra` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_finite_graph_replay_obstruction` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_sets`, `curriculum_relations_and_functions`,
  `curriculum_counting`, and `curriculum_linear_algebra` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `feasible-flow-witness` | `sat` | checked |
| `flow-cut-optimality-witness` | `sat` | checked |
| `bad-capacity-bound-rejected` | `unsat` | checked |
| `bad-flow-value-rejected` | `unsat` | checked |
| `qf-lra-bad-flow-value-cut-bound` | `unsat` | checked QF_LRA/Farkas |
| `max-flow-min-cut-theorem-lean-horizon` | `not-run` | lean-horizon |

The checked finite rows replay exact flow and cut arithmetic. The promoted
`qf-lra-*` row checks only the final scalar contradiction `4 <= 3` with
source-linked `UnsatFarkas` evidence. They do not prove the general
max-flow/min-cut theorem, algorithm correctness, integrality, min-cost flow, or
asymptotic runtime.

## The Network

The pack uses this directed network:

```text
s -> a  capacity 2  flow 2
s -> b  capacity 1  flow 1
a -> b  capacity 1  flow 1
a -> t  capacity 1  flow 1
b -> t  capacity 2  flow 2
```

The source is `s`, the sink is `t`, and the claimed flow value is `3`.

## Replay Feasibility

The validator checks every edge locally:

```text
0 <= flow(e) <= capacity(e)
```

It then checks conservation at the internal vertices:

```text
a: inflow 2, outflow 2
b: inflow 2, outflow 2
```

Finally it checks source and sink balance:

```text
s net outflow = 3
t net inflow = 3
```

## Replay The Cut Certificate

The cut witness chooses:

```text
source_side = {s}
target_side = {a, b, t}
```

The directed edges crossing from the source side to the target side are:

```text
s -> a  capacity 2
s -> b  capacity 1
```

So the cut capacity is `3`. Since the feasible flow value is also `3`, this
finite row certifies optimality for the listed network by exact cut replay.

## Reject Bad Claims

The capacity-bound rejection changes one edge:

```text
flow(s,a) = 3
capacity(s,a) = 2
```

The checker rejects the claim immediately because the edge flow exceeds the
edge capacity.

The flow-value rejection claims a feasible value `4`. The checker recomputes
the source-side cut capacity as `3`, so a value `4` violates this finite cut
upper bound.

The solver-facing row isolates that final contradiction as QF_LRA:

```smt2
(declare-const cut_capacity Real)
(declare-const claimed_flow_value Real)
(assert (= cut_capacity 3))
(assert (= claimed_flow_value 4))
(assert (<= claimed_flow_value cut_capacity))
```

Axeyum emits and independently checks `UnsatFarkas` evidence for this source
artifact. The finite replay computes the numbers; the Farkas proof checks the
last exact-rational conflict.

## Why This Matters

This is the graph-optimization version of Axeyum's trust pattern:

```text
untrusted search proposes a flow and a cut
trusted checker recomputes capacities, conservation, and cut bounds
```

The checker does not need to trust an algorithm trace for this row. It only
needs the finite network, the proposed flow, and the proposed cut.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-flow-cut-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_flow_cut_bad_flow_value_cut_bound_artifact_emits_checked_farkas
```

## Trust Boundary

The validator checks this fixed network over exact rationals. The general
max-flow/min-cut theorem and scalable algorithms remain theorem/proof-resource
work until a Lean route exists. The promoted Farkas row is only a checked
source artifact for the final finite cut-bound contradiction.
