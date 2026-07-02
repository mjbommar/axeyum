# Shortest Path Theorem Boundary

This page separates Axeyum's finite shortest-path resource from general
shortest-path algorithm correctness, negative-cycle theory, all-pairs
shortest paths, data-structure complexity, and asymptotic runtime claims.

Primary pack:

- [finite-shortest-path-v0](../../../artifacts/examples/math/finite-shortest-path-v0/)

Companion lessons and maps:

- [End To End: Finite Shortest Path Certificates](finite-shortest-path-end-to-end.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)

## Current Finite Resource

The pack fixes one four-node directed weighted graph:

```text
vertices = s, a, b, t
source   = s
target   = t

s -> a  weight 2
s -> b  weight 5
s -> t  weight 9
a -> b  weight 1
a -> t  weight 6
b -> t  weight 2
```

The path witness is:

```text
s -> a -> b -> t
```

The checker replays the path exactly:

```text
2 + 1 + 2 = 5
```

It also checks one potential certificate:

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

That finite potential lower-bounds every `s`-to-`t` path by
`p(t) - p(s) = 5`. Since the listed path also has length `5`, this proves
optimality for this listed finite graph by exact replay.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `path-distance-witness` | `sat` | checked | The listed path uses real directed edges and has exact length `5`. |
| `potential-optimality-witness` | `sat` | checked | The listed potentials satisfy every edge relaxation and match the path length, certifying this finite instance. |
| `bad-path-distance-rejected` | `unsat` | checked | The malformed row claims the same path has length `4`, but exact replay computes `5`. |
| `bad-shorter-distance-rejected` | `unsat` | checked | The malformed row claims an `s`-to-`t` path of length at most `4`, but the potential lower bound is `5`. |
| `qf-lra-bad-shorter-distance-potential-bound` | `unsat` | checked QF_LRA/Farkas | The source SMT-LIB artifact isolates `5 <= 4` after replay checks the potential lower bound. |
| `shortest-path-theorem-lean-horizon` | `not-run` | lean-horizon | General shortest-path theorem and algorithm-correctness claims remain future proof-assistant work. |

The checked rows are deterministic exact finite replay, plus one promoted
source-linked QF_LRA/Farkas row for the final potential-bound contradiction.
That promoted row is a solver-regression seed for `5 <= 4`; it does not promote
the arbitrary-graph theorem, negative-cycle theory, or algorithm correctness.

## What Is Not Proved Yet

The current pack does not prove:

- Dijkstra, Bellman-Ford, Floyd-Warshall, Johnson, A*, or BFS-shortest-path
  algorithm correctness;
- shortest-path correctness for arbitrary finite weighted directed graphs;
- negative-cycle detection, infeasibility, or shortest-walk theory;
- all-pairs shortest paths;
- data-structure or heap complexity;
- asymptotic runtime;
- floating-point, approximate, heuristic, or dynamically updated shortest-path
  soundness.

Those claims need theorem statements with explicit graph, weight, path,
potential, cycle, and algorithm hypotheses plus no-`sorry` Lean artifacts
before they can graduate from horizon rows. The finite shortest-path rows are
exact checked examples and teaching resources, not proof evidence for the full
algorithm family.

## Query The Boundary

Find shortest-path theorem-horizon rows and finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text shortest \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-shortest-path-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite replay rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-shortest-path-v0 \
  --proof-status checked \
  --require-any
```

Drill into the checked finite path, potential, and malformed-distance rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-shortest-path-v0 \
  --proof-status checked \
  --text "exact length" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-shortest-path-v0 \
  --proof-status checked \
  --text potentials \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-shortest-path-v0 \
  --proof-status checked \
  --text "at most 4" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-shortest-path-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-shorter-distance-potential-bound \
  --require-any
```

## Graduation Criteria

General shortest-path resources graduate only when they add:

1. precise Lean theorem statements for path optimality, feasible potentials,
   edge relaxations, Bellman-Ford/Dijkstra-style invariants, negative-cycle
   handling, and optional all-pairs variants;
2. explicit hypotheses for finite directed graphs, exact weights, allowed
   negative weights, source/target reachability, paths, cycles, and algorithms;
3. no-`sorry` proofs with an axiom audit;
4. source exact-arithmetic artifacts plus checked certificate routes before
   promoting additional malformed distance, edge-relaxation, or
   potential-bound rows as solver regressions;
5. display labels that keep finite replay, route certificates, theorem rows,
   and benchmark claims separate.

Until then, shortest-path rows remain bounded/computable resources:

```text
untrusted fast search -> proposed path, distance, potential, or malformed bound
trusted small checking -> exact edge, path-length, relaxation, and lower-bound replay
theorem horizon       -> arbitrary-graph shortest-path and algorithm correctness
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-shortest-path-v0
cargo test -p axeyum-solver --test math_resource_lra_routes finite_shortest_path_bad_shorter_distance_potential_bound_artifact_emits_checked_farkas
python3 scripts/query-foundational-resources.py horizon-frontier --text shortest --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --route Farkas --proof-status checked --text qf-lra-bad-shorter-distance-potential-bound --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the shortest-path
theorem row remains `lean-horizon`.
