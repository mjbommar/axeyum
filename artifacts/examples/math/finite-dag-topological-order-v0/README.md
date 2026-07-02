# Finite DAG Topological Order Certificates

Audience: graph-theory learners, discrete-math learners, solver contributors,
and resource consumers who need a small checked example of order constraints on
a finite directed graph plus a source-linked integer proof row.

This pack checks one finite prerequisite DAG and one finite directed cycle. It
does not prove a topological-sort algorithm correct. It shows how a proposed
order or cycle obstruction can be replayed by a small checker.

## Concept Rows

- `field_graph_theory`
- `field_discrete_math`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`
- `bridge_finite_graph_replay_obstruction`

## Checks

| Check | Expected | Evidence |
|---|---|---|
| `topological-order-witness` | `sat` | checked edge-position replay |
| `independent-swap-order-witness` | `sat` | checked alternate-order replay |
| `bad-order-rejected` | `unsat` | checked edge-position violation |
| `qf-lia-bad-topological-edge-order` | `unsat` | checked QF_LIA artifact for `2 < 1` |
| `cycle-obstruction-rejected` | `unsat` | checked directed-cycle obstruction |
| `topological-sort-theorem-lean-horizon` | `not-run` | theorem horizon |

## Trust Boundary

The untrusted side proposes a vertex order or a cycle. The trusted checker
verifies that the order covers every vertex exactly once, checks every directed
edge against the order, replays every edge of a cycle witness, and checks the
source-linked QF_LIA evidence for the promoted edge-order conflict. The checker
does not trust Kahn's algorithm, DFS finishing times, or any search trace for
this row.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dag-topological-order-v0
```

## Limitations

This is a fixed finite DAG and one fixed finite cycle. It does not prove
topological-sort algorithm correctness, the full finite linear-extension
theorem, cycle-detection completeness, partial-order dimension results, or
asymptotic runtime. Those stay in the Lean/theorem-horizon lane until proof
artifacts exist.
