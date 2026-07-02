# Finite Shortest Path Certificates

Audience: graph-theory learners, optimization learners, solver contributors,
and resource consumers who need a small checked example of path/certificate
duality plus a source-linked exact-rational proof row.

This pack checks one finite directed weighted graph over exact rationals. It
does not prove a shortest-path algorithm correct. It shows how a proposed path
and a proposed potential certificate can be replayed by a small checker.

## Concept Rows

- `field_graph_theory`
- `field_discrete_math`
- `field_optimization_and_convexity`
- `curriculum_sets`
- `curriculum_relations_and_functions`
- `curriculum_counting`
- `curriculum_rationals`
- `bridge_finite_graph_replay_obstruction`

## Checks

| Check | Expected | Evidence |
|---|---|---|
| `path-distance-witness` | `sat` | checked exact path-length replay |
| `potential-optimality-witness` | `sat` | checked edge-relaxation and path replay |
| `bad-path-distance-rejected` | `unsat` | checked path-length recomputation |
| `bad-shorter-distance-rejected` | `unsat` | checked potential lower-bound rejection |
| `qf-lra-bad-shorter-distance-potential-bound` | `unsat` | checked QF_LRA/Farkas artifact for `5 <= 4` |
| `shortest-path-theorem-lean-horizon` | `not-run` | theorem horizon |

## Trust Boundary

The untrusted side proposes a path, a distance value, or a potential assignment.
The trusted checker recomputes every used edge weight, every edge-relaxation
inequality, the resulting lower bound, and the source-linked Farkas certificate
for the promoted potential-bound conflict. The checker does not trust Dijkstra,
Bellman-Ford, or any search trace for this row.

## Run

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-shortest-path-v0
```

## Limitations

This is a fixed finite graph. It does not prove all-pairs shortest paths,
negative-cycle handling, algorithm invariants, heap/data-structure complexity,
or asymptotic runtime. Those stay in the Lean/theorem-horizon lane until proof
artifacts exist.
