# Max-Flow Min-Cut Theorem Boundary

This page separates Axeyum's finite flow/cut resource from the general
max-flow/min-cut theorem, algorithm correctness, integrality theorems,
min-cost flow, multi-commodity flow, and asymptotic graph-algorithm claims.

Primary pack:

- [finite-flow-cut-v0](../../../artifacts/examples/math/finite-flow-cut-v0/)

Companion lessons and maps:

- [End To End: Finite Flow And Cut Certificates](finite-flow-cut-end-to-end.md)
- [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md)
- [Graph Traversal Runtime Index](graph-traversal-runtime-index.md)
- [Linear Algebra And Optimization](linear-algebra-and-optimization.md)

## Current Finite Resource

The pack fixes one four-node directed network:

```text
vertices = s, a, b, t
source   = s
sink     = t

s -> a  capacity 2  flow 2
s -> b  capacity 1  flow 1
a -> b  capacity 1  flow 1
a -> t  capacity 1  flow 1
b -> t  capacity 2  flow 2
```

The validator checks exact finite feasibility:

```text
0 <= flow(e) <= capacity(e)
a: inflow 2, outflow 2
b: inflow 2, outflow 2
s net outflow = 3
t net inflow  = 3
```

It also checks one cut certificate:

```text
source side = {s}
target side = {a, b, t}
cut edges   = s->a, s->b
cut capacity = 2 + 1 = 3
flow value   = 3
```

Those rows certify optimality for this listed finite network by exact replay.
They do not prove the general max-flow/min-cut theorem.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `feasible-flow-witness` | `sat` | checked | The listed edge flows respect capacities and conservation, with value `3`. |
| `flow-cut-optimality-witness` | `sat` | checked | The listed feasible flow saturates the `{s}` cut of capacity `3`, certifying this finite instance. |
| `bad-capacity-bound-rejected` | `unsat` | checked | The malformed row sends `3` units across edge `s -> a`, whose capacity is `2`. |
| `bad-flow-value-rejected` | `unsat` | checked | The malformed row claims feasible value `4`, but the listed cut has capacity `3`. |
| `max-flow-min-cut-theorem-lean-horizon` | `not-run` | lean-horizon | The general theorem for arbitrary finite networks remains future proof-assistant work. |

The checked rows are deterministic exact finite replay. The pack is currently a
`non-benchmark-horizon` resource, not a promoted solver-regression route: no
source SMT/CNF artifact or route-specific certificate has been committed for
the malformed rows.

## What Is Not Proved Yet

The current pack does not prove:

- max-flow/min-cut for every finite capacitated network;
- Ford-Fulkerson, Edmonds-Karp, Dinic, push-relabel, or augmenting-path
  algorithm correctness;
- integral-flow theorems from integral capacities;
- min-cost flow, circulation with demands, lower bounds, or multi-commodity
  flow;
- LP duality for the full flow/cut formulation;
- asymptotic runtime, complexity, or data-structure guarantees;
- floating-point or approximate-flow soundness.

Those claims need theorem statements with explicit hypotheses and no-`sorry`
Lean artifacts before they can graduate from horizon rows. The finite flow/cut
rows are exact checked examples and teaching resources, not proof evidence for
the theorem family.

## Query The Boundary

Find max-flow/min-cut theorem-horizon rows and finite shadows:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "max-flow" \
  --require-any
```

Find the explicit Lean-horizon row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-flow-cut-v0 \
  --proof-status lean-horizon \
  --require-any
```

Find the checked finite replay rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-flow-cut-v0 \
  --proof-status checked \
  --require-any
```

Drill into the checked finite capacity, cut, and value rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-flow-cut-v0 \
  --proof-status checked \
  --text "respects every edge" \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-flow-cut-v0 \
  --proof-status checked \
  --text saturates \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-flow-cut-v0 \
  --proof-status checked \
  --text "value 4" \
  --require-any
```

## Graduation Criteria

General flow/cut resources graduate only when they add:

1. precise Lean theorem statements for max-flow/min-cut, cut upper bounds,
   residual networks, augmenting paths, and optional integrality;
2. explicit hypotheses for finite directed graphs, nonnegative capacities,
   sources/sinks, feasible flows, cuts, and conservation;
3. no-`sorry` proofs with an axiom audit;
4. a source exact-arithmetic artifact plus checked certificate route before
   promoting malformed flow rows as solver regressions;
5. display labels that keep finite replay, route certificates, theorem rows,
   and benchmark claims separate.

Until then, flow/cut rows remain bounded/computable resources:

```text
untrusted fast search -> proposed flow, cut, or malformed capacity/value claim
trusted small checking -> exact capacity, conservation, cut-capacity, and value replay
theorem horizon       -> arbitrary-network max-flow/min-cut and algorithm correctness
```

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-flow-cut-v0
python3 scripts/query-foundational-resources.py horizon-frontier --text "max-flow" --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-flow-cut-v0 --proof-status lean-horizon --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-flow-cut-v0 --proof-status checked --require-any
```

Expected resource boundary: the finite pack validates, the
`horizon-frontier` query shows `checked-finite-shadow`, and the
max-flow/min-cut theorem row remains `lean-horizon`.
