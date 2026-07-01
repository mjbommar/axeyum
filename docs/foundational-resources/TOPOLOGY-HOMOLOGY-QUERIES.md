# Topology And Homology Resource Consumer Queries

This guide turns the topology, finite-topological-space, and finite
homology/cohomology rows in the foundational-resource JSON contract into
copyable downstream queries. It is a consumer-discovery layer, not a new proof
route and not a claim of general topology, algebraic topology, or analysis
theorem coverage.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked finite topology or homology packs match this concept and proof route?
```

The current topology surface is finite and route-explicit: metric balls,
bounded epsilon-delta shadows, finite topology axioms, compactness and
connectedness shadows, finite continuity/open-preimage checks, homeomorphism
operator replay, quotient topology, specialization order, finite boundary and
homology arithmetic, torsion shadows, cohomology/coboundary replay, universal
coefficient shadows, and F2 cup products. Arbitrary compactness,
connectedness, homeomorphism invariance, quotient universal properties,
homology/cohomology invariance, exact sequences, UCT naturality, cohomology
ring laws, and infinite-space topology remain in the proof-horizon lane.

## Query Shape

Start with field summaries by route:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field topology \
  --route boolean \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field topology \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field topology \
  --route Diophantine \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field topology \
  --route qf-bv \
  --require-any
```

Then drill into bridge concepts by finite topology family:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_compactness_shadow \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_quotient_topology_replay \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Use `packs` for catalog rows and pack paths. Use `checks` when the consumer
needs concrete checked rows to display.

## Topology Query Families

| Family | Concept Filter | Route Filter | Start Query |
|---|---|---|---|
| Metric balls and bounded epsilon-delta shadows | `bridge_metric_ball`; `bridge_bounded_epsilon_delta_shadow` | `Farkas` | `packs --concept bridge_metric_ball --route Farkas`; `checks --concept bridge_bounded_epsilon_delta_shadow --route Farkas --proof-status checked` |
| Finite topology axioms, compactness, and connectedness shadows | `bridge_compactness_shadow`; `bridge_connectedness_shadow` | `boolean` | `checks --concept bridge_compactness_shadow --route boolean --proof-status checked`; `checks --concept bridge_connectedness_shadow --route boolean --proof-status checked` |
| Continuity, topology operators, and finite homeomorphism replay | `bridge_finite_topology_operator_homeomorphism` | `Alethe` | `checks --concept bridge_finite_topology_operator_homeomorphism --route Alethe --proof-status checked` |
| Quotient topology and finite quotient maps | `bridge_finite_quotient_topology_replay`; `bridge_quotient_map` | `Alethe` | `checks --concept bridge_finite_quotient_topology_replay --route Alethe --proof-status checked` |
| Specialization preorder and finite T0 rows | `bridge_finite_specialization_order_replay` | `Alethe` | `checks --concept bridge_finite_specialization_order_replay --route Alethe --proof-status checked` |
| Boundary operators and finite homology arithmetic | `bridge_finite_boundary_operator_replay`; `bridge_finite_chain_homology_replay` | `Diophantine` | `checks --concept bridge_finite_boundary_operator_replay --route Diophantine --proof-status checked`; `checks --concept bridge_finite_chain_homology_replay --route Diophantine --proof-status checked` |
| Torsion homology shadows | `bridge_finite_torsion_homology_replay` | `Diophantine` | `checks --concept bridge_finite_torsion_homology_replay --route Diophantine --proof-status checked` |
| Cohomology, UCT shadows, and cup products | `bridge_finite_cohomology_replay`; `bridge_finite_universal_coefficient_shadow`; `bridge_finite_cup_product_replay` | `Alethe`; `qf-bv` | `checks --concept bridge_finite_cohomology_replay --route Alethe --proof-status checked`; `checks --concept bridge_finite_cup_product_replay --route qf-bv --proof-status checked` |

## Copyable Examples

Display checked topology rows by route:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

Display metric and bounded analysis/topology rows:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_metric_ball \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_bounded_epsilon_delta_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display finite topology, compactness, connectedness, quotient, and
specialization rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_compactness_shadow \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_connectedness_shadow \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_topology_operator_homeomorphism \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_quotient_topology_replay \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_specialization_order_replay \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Display finite homology, cohomology, UCT, and cup-product rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_boundary_operator_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_torsion_homology_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_cohomology_replay \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_universal_coefficient_shadow \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_cup_product_replay \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked topology and
homology/cohomology rows, not theorem coverage. They can support a catalog,
learner page, solver-regression search, or sibling resource that needs examples
by finite topological object family.

They do not prove:

- arbitrary compactness, connectedness, convergence, or continuity theorems;
- homeomorphism invariance or classification of topological spaces;
- quotient topology universal properties or quotient-map theorem schemas;
- homology/cohomology invariance, exact sequences, UCT naturality, or
  cohomology-ring laws;
- infinite-dimensional, manifold, sheaf, homotopy, or spectral-sequence
  claims;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction, or
benchmark evidence before they can graduate.
