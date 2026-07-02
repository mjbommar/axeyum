# Proof Route Query Matrix

This is the route-facing companion to
[FIELD-READINESS-QUERY-MATRIX.md](FIELD-READINESS-QUERY-MATRIX.md) and
[MATRIX-COMPUTATION-QUERIES.md](MATRIX-COMPUTATION-QUERIES.md). It answers:

```text
Which current proof/evidence routes have resource coverage, how should a
consumer query them, and what should the consumer avoid claiming?
```

The route rows come from proof-cookbook recipe links in committed pack
metadata. The query helper does not import validators, generators, or solver
crates.

For consumer queries focused specifically on theorem-boundary rows, see
[Theorem Horizon Queries](THEOREM-HORIZON-QUERIES.md).

## Query Pattern

Start with the route summary:

```sh
python3 scripts/query-foundational-resources.py routes --route <route-alias> --require-any
```

Then drill into source packs or checked rows:

```sh
python3 scripts/query-foundational-resources.py packs --route <canonical-route-name> --solver-reuse promoted --require-any
python3 scripts/query-foundational-resources.py checks --route <canonical-route-name> --proof-status checked --require-any
```

Route aliases are normalized for the `routes` summary command, so `Farkas`,
`qf-lra`, `Alethe`, `qf-uf`, `boolean`, `qf-bv`, `Diophantine`, `finite-replay`,
and `lean` are stable summary terms. Pack and check drilldowns keep the older
public substring filter, so use canonical recipe names such as
`lean-horizon-template` when ambiguity matters.

## Route Matrix

| Route | Current Pack Count | Start Query | Drilldown Query | Do Not Claim |
|---|---:|---|---|---|
| `finite-model-replay` | 117 | `routes --route finite-replay` | `packs --route finite-model-replay --solver-reuse promoted` | Certificate checking, theorem proof, performance, or solver parity. This route proves exact replay of finite source data. |
| `boolean-cnf-lrat` | 16 | `routes --route boolean` | `checks --route boolean --proof-status checked` | General graph/set/proof theorems or trust in the encoder. The trusted claim is the checked finite CNF proof object. |
| `qf-bv-bitblast` | 7 | `routes --route qf-bv` | `checks --route qf-bv --proof-status checked` | Unbounded arithmetic, arbitrary finite algebra, or width-independent claims. Width must be part of the source claim. |
| `qf-lia-diophantine` | 15 | `routes --route Diophantine` | `checks --route Diophantine --proof-status checked` | General number theory, arbitrary integer theorem schemas, universal coefficient theorems, or asymptotic combinatorics. The row is a concrete integer obstruction. |
| `qf-lra-farkas` | 65 | `routes --route Farkas` | `checks --route Farkas --proof-status checked` | Real completeness, calculus/optimization convergence, floating-point stability, duality theorems, or performance claims. |
| `qf-uf-congruence-alethe` | 19 | `routes --route Alethe` | `checks --route Alethe --proof-status checked` | Arbitrary algebraic/topological structure theorems or full first-order reasoning. This route checks equality/congruence conflicts after finite replay exposes them. |
| `lean-horizon-template` | 86 | `routes --route lean` | `packs --route lean-horizon-template --proof-status lean-horizon` | That the theorem is proved. A Lean-horizon row records theorem shape and missing reconstruction dependency. |

## Field-Scoped Route Queries

Route summaries can be scoped to a field when a consumer wants the route view
for one curriculum area:

```sh
python3 scripts/query-foundational-resources.py routes \
  --route Farkas \
  --field linear_algebra \
  --require-any
```

```sh
python3 scripts/query-foundational-resources.py routes \
  --route Alethe \
  --field abstract_algebra \
  --require-any
```

```sh
python3 scripts/query-foundational-resources.py routes \
  --route lean \
  --field topology \
  --require-any
```

```sh
python3 scripts/query-foundational-resources.py routes \
  --route LIA \
  --field graph_theory \
  --require-any
```

The counts in a field-scoped route row are pack/check counts for packs tagged
with that field. The `fields` cell can still list other fields because many
packs intentionally bridge topics, such as topology with set theory or linear
algebra with optimization.

## Boundary

This matrix is documentation over committed JSON and
`query-foundational-resources.py`. It does not add a proof route, route
checker, typed API, crate, or separate repository.

Use the route summary to find current resources. Use the route-specific
regressions and proof-cookbook recipes before upgrading evidence claims.
