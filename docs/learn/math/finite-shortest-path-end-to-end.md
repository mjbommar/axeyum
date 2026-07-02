# End To End: Finite Shortest Path Certificates

This lesson follows one directed weighted graph from a proposed path to a
potential certificate that proves the path is shortest. It uses
[finite-shortest-path-v0](../../../artifacts/examples/math/finite-shortest-path-v0/).

Concept rows:

- `field_graph_theory`, `field_discrete_math`, and
  `field_optimization_and_convexity` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `bridge_finite_graph_replay_obstruction` in the
  [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- `curriculum_sets`, `curriculum_relations_and_functions`,
  `curriculum_counting`, and `curriculum_rationals` in the
  [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)

## Claim Shape

| Check | Expected | Evidence Status |
|---|---|---|
| `path-distance-witness` | `sat` | checked |
| `potential-optimality-witness` | `sat` | checked |
| `bad-path-distance-rejected` | `unsat` | checked |
| `bad-shorter-distance-rejected` | `unsat` | checked |
| `qf-lra-bad-shorter-distance-potential-bound` | `unsat` | checked QF_LRA/Farkas |
| `shortest-path-theorem-lean-horizon` | `not-run` | lean-horizon |

The checked rows are exact finite replay. They do not prove Dijkstra,
Bellman-Ford, all-pairs shortest paths, negative-cycle theory, or asymptotic
runtime.

## The Graph

The pack uses this directed weighted graph:

```text
s -> a  weight 2
s -> b  weight 5
s -> t  weight 9
a -> b  weight 1
a -> t  weight 6
b -> t  weight 2
```

The source is `s` and the target is `t`.

## Replay The Path

The path witness is:

```text
s -> a -> b -> t
```

The checker verifies each consecutive pair is an edge and then sums:

```text
2 + 1 + 2 = 5
```

So the listed path has exact length `5`.

## Replay The Potential Certificate

The potential witness is:

```text
p(s) = 0
p(a) = 2
p(b) = 3
p(t) = 5
```

For every directed edge `u -> v`, the checker verifies:

```text
p(v) <= p(u) + weight(u,v)
```

Summing those inequalities along any `s`-to-`t` path gives:

```text
path_length >= p(t) - p(s) = 5
```

The proposed path has length `5`, so the finite optimality certificate checks.

## Reject Bad Claims

The bad path-distance row claims the same path has length `4`. The checker
recomputes length `5`, so the row is rejected.

The bad shorter-distance row claims there is an `s`-to-`t` path of length at
most `4`. The checker verifies the potential certificate lower-bounds every
path by `5`, so the row is rejected.

The source-linked QF_LRA row isolates that final scalar contradiction as
`potential_lower_bound = 5`, `claimed_upper_bound = 4`, and
`potential_lower_bound <= claimed_upper_bound`; Axeyum emits checked
`UnsatFarkas` evidence for this exact `5 <= 4` conflict.

## Why This Matters

This is the shortest-path version of Axeyum's trust pattern:

```text
untrusted search proposes a path and dual potentials
trusted checker recomputes path length and edge relaxations
```

The checker does not need to trust the search algorithm. It only needs the
finite graph, the proposed path, and the proposed potentials.

## Run It

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-shortest-path-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_shortest_path_bad_shorter_distance_potential_bound_artifact_emits_checked_farkas
```

## Trust Boundary

The validator checks this fixed graph over exact rationals. General
shortest-path algorithm correctness, negative-cycle handling, all-pairs
variants, data-structure costs, and asymptotic runtime remain theorem/proof
resource work. The promoted solver-reuse row covers only the source-linked
potential-bound contradiction, not the general shortest-path theorem.
