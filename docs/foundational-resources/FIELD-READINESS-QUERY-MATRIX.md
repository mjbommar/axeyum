# Field Readiness Query Matrix

## Purpose

This is the compact consumer-facing map for the current math-resource query
surface. It complements [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md), which gives
copyable examples and explanatory prose. This file answers one narrower
question:

```text
For each university math field, which public query should a consumer start with,
which bridge concepts should it expose, which checked rows can it display, and
which theorem horizon must it avoid overclaiming?
```

The boundary remains JSON-first and in-repo. Every row below is backed by the
committed data contract:

- [`artifacts/ontology/foundational-concepts.json`](../../artifacts/ontology/foundational-concepts.json)
- [`artifacts/examples/math/*/metadata.json`](../../artifacts/examples/math/)
- [`artifacts/examples/math/*/expected.json`](../../artifacts/examples/math/)
- [`scripts/query-foundational-resources.py`](../../scripts/query-foundational-resources.py)

The smoke coverage lives in
[`scripts/check-foundational-resources.sh`](../../scripts/check-foundational-resources.sh).
At the time this matrix was written, the public summary reports 109 concept
rows, 106 non-template packs, 538 expected checks, 229 checked rows, 240
replay-only rows, 69 Lean-horizon rows, and 106 promoted solver-reuse packs.

## Query Pattern

Use the same three-step pattern for every field:

```sh
python3 scripts/query-foundational-resources.py fields --field <field> --route <route> --require-any
python3 scripts/query-foundational-resources.py concepts --field <field> --text <bridge-term> --require-any
python3 scripts/query-foundational-resources.py checks --field <field> --route <route> --proof-status checked --require-any
```

The first command is the field-readiness summary. The second command exposes
shared vocabulary that multiple packs reuse. The third command returns concrete
checked rows a learner page, catalog card, or downstream app can display.

## Matrix

| Field | Packs / Checks | Start Route | Bridge Lookup Terms | Checked Row Drilldown | Do Not Claim |
|---|---:|---|---|---|---|
| `logic_and_proof` | 11 / 55 | `fields --field logic_and_proof --route boolean` | `concepts --field logic_and_proof --text proof` | `checks --field logic_and_proof --route boolean --proof-status checked` | Full proof automation, quantified metatheory, or the general induction schema. |
| `set_theory_and_foundations` | 34 / 186 | `fields --field set_theory_and_foundations --route Alethe` | `concepts --field set_theory_and_foundations --text partition` | `checks --field set_theory_and_foundations --route Alethe --proof-status checked` | ZFC, ordinals, choice, infinite cardinality, or complete-lattice theorems. |
| `discrete_math` | 22 / 107 | `fields --field discrete_math --route Diophantine` | `concepts --field discrete_math --text finite`; `concepts --field discrete_math --text counting` | `checks --field discrete_math --route Diophantine --proof-status checked` | Asymptotic enumeration, recurrence closed forms, or broad combinatorial theorem families. |
| `graph_theory` | 6 / 26 | `fields --field graph_theory --route boolean` | `concepts --field graph_theory --text graph`; `concepts --field graph_theory --text reachability` | `checks --field graph_theory --route boolean --proof-status checked` | Extremal graph theory, graph minors, asymptotic algorithms, or general graph theorems. |
| `number_theory` | 9 / 50 | `fields --field number_theory --route Diophantine` | `concepts --field number_theory --text finite`; `concepts --field number_theory --text totality`; `concepts --field number_theory --text gcd`; `concepts --field number_theory --text CRT` | `checks --field number_theory --route Diophantine --proof-status checked` | Analytic/algebraic number theory or unbounded number-theory theorem coverage. |
| `linear_algebra` | 42 / 210 | `fields --field linear_algebra --route Farkas` and `fields --field linear_algebra --route Alethe` | `concepts --field linear_algebra --text rank`; `concepts --field linear_algebra --text projection` | `checks --field linear_algebra --route Farkas --proof-status checked`; `checks --field linear_algebra --route Alethe --proof-status checked` | Spectral theorems, conditioning/stability, general Smith normal form, or general vector-space/module theorem claims. |
| `abstract_algebra` | 23 / 124 | `fields --field abstract_algebra --route Alethe` | `concepts --field abstract_algebra --text homomorphism`; `concepts --field abstract_algebra --text ideal` | `checks --field abstract_algebra --route Alethe --proof-status checked`; `checks --field abstract_algebra --route qf-bv --proof-status checked` | Arbitrary group/ring/module/category theory, classification of finitely generated abelian groups, or infinite algebra. |
| `real_analysis` | 50 / 256 | `fields --field real_analysis --route Farkas` | `concepts --field real_analysis --text epsilon`; `concepts --field real_analysis --text gradient` | `checks --field real_analysis --route Farkas --proof-status checked` | Completeness, IVT/MVT/FTC, general convergence, compactness, or theorem-level calculus. |
| `complex_analysis` | 4 / 19 | `fields --field complex_analysis --route Farkas` | `concepts --field complex_analysis --text real-pair` | `checks --field complex_analysis --route Farkas --proof-status checked` | Holomorphicity, contour integration, residues, analytic continuation, or algebraic closure. |
| `topology` | 13 / 70 | `fields --field topology --route boolean`; `fields --field topology --route Diophantine`; `fields --field topology --route qf-bv` | `concepts --field topology --text compactness`; `concepts --field topology --text preimage`; `concepts --field topology --text closure`; `concepts --field topology --text homeomorphism`; `concepts --field topology --text specialization`; `concepts --field topology --text boundary`; `concepts --field topology --text homology`; `concepts --field topology --text torsion`; `concepts --field topology --text cohomology`; `concepts --field topology --text cup` | `checks --field topology --route boolean --proof-status checked`; `checks --field topology --route alethe --proof-status checked`; `checks --field topology --route Diophantine --proof-status checked`; `checks --field topology --route qf-bv --proof-status checked`; `packs --concept bridge_finite_topology_operator_homeomorphism --route alethe`; `checks --concept bridge_finite_topology_operator_homeomorphism --route alethe --proof-status checked`; `packs --concept bridge_finite_specialization_order_replay --route alethe`; `checks --concept bridge_finite_specialization_order_replay --route alethe --proof-status checked`; `packs --concept bridge_finite_boundary_operator_replay --route Diophantine`; `checks --concept bridge_finite_boundary_operator_replay --route Diophantine --proof-status checked`; `packs --concept bridge_finite_chain_homology_replay --route Diophantine`; `checks --concept bridge_finite_chain_homology_replay --route Diophantine --proof-status checked`; `packs --concept bridge_finite_torsion_homology_replay --route Diophantine`; `checks --concept bridge_finite_torsion_homology_replay --route Diophantine --proof-status checked`; `packs --concept bridge_finite_cohomology_replay --route alethe`; `checks --concept bridge_finite_cohomology_replay --route alethe --proof-status checked`; `packs --concept bridge_finite_cup_product_replay --route qf-bv`; `checks --concept bridge_finite_cup_product_replay --route qf-bv --proof-status checked` | Arbitrary compactness, connectedness, homeomorphism invariance, specialization-order theorems, homology/cohomology invariance, exact sequences, universal coefficient theorems, cohomology-ring laws, or cohomology-operation invariance. |
| `measure_theory` | 11 / 55 | `fields --field measure_theory --route Farkas` | `concepts --field measure_theory --text finite` | `checks --field measure_theory --route Farkas --proof-status checked` | Lebesgue measure, countable additivity beyond finite tables, convergence theorems, or almost-everywhere reasoning. |
| `probability_theory` | 18 / 85 | `fields --field probability_theory --route Farkas` | `concepts --field probability_theory --text probability` | `checks --field probability_theory --route Farkas --proof-status checked` | Continuous distributions, stochastic-process limit theorems, or asymptotic probability theory. |
| `statistics` | 14 / 68 | `fields --field statistics --route Farkas` | `concepts --field statistics --text tail`; `concepts --field statistics --text finite` | `checks --field statistics --route Farkas --proof-status checked`; `checks --field statistics --route Diophantine --proof-status checked` | Floating-point inference, asymptotic sampling, MCMC, VI, or model-calibration claims. |
| `optimization_and_convexity` | 19 / 99 | `fields --field optimization_and_convexity --route Farkas` | `concepts --field optimization_and_convexity --text objective`; `concepts --field optimization_and_convexity --text convexity` | `checks --field optimization_and_convexity --route Farkas --proof-status checked` | Duality, KKT sufficiency, SDP strong duality, or algorithm convergence theorems. |
| `numerical_analysis` | 21 / 108 | `fields --field numerical_analysis --route Farkas` | `concepts --field numerical_analysis --text residual`; `concepts --field numerical_analysis --text operator`; `concepts --field numerical_analysis --text floating` | `checks --field numerical_analysis --route Farkas --proof-status checked` | Floating-point roundoff, conditioning/stability, asymptotic error analysis, or convergence theorems. |
| `differential_equations_and_dynamical_systems` | 7 / 36 | `fields --field differential_equations_and_dynamical_systems --route Farkas` | `concepts --field differential_equations_and_dynamical_systems --text Euler`; `concepts --field differential_equations_and_dynamical_systems --text stochastic` | `checks --field differential_equations_and_dynamical_systems --route Farkas --proof-status checked` | Existence/uniqueness, continuous dynamics, chaos, PDE theory, or continuous-time stability. |
| `geometry` | 8 / 39 | `fields --field geometry --route Farkas` | `concepts --field geometry --text coordinate`; `concepts --field geometry --text circle` | `checks --field geometry --route Farkas --proof-status checked` | Synthetic, projective, differential, global, or higher-degree algebraic geometry theorems. |
| `functional_analysis_and_operator_theory` | 5 / 27 | `fields --field functional_analysis_and_operator_theory --route Farkas` | `concepts --field functional_analysis_and_operator_theory --text operator` | `checks --field functional_analysis_and_operator_theory --route Farkas --proof-status checked` | Banach/Hilbert-space theorems, topological duals, compact operators, minimax, or infinite-dimensional approximation theory. |

## Current Boundary Decision

This matrix is intentionally documentation over the existing script interface.
It does not create a typed API, a new crate, or a new repository. The split
trigger remains the one recorded in
[LIBRARY-BOUNDARY-DECISION.md](LIBRARY-BOUNDARY-DECISION.md): at least three
duplicated typed consumers or one external release-cadence need.

Until then, the practical contract is:

```text
committed JSON -> query helper -> generated dashboards -> small checked lessons
```

That keeps the resource ecosystem aligned with Axeyum's core identity:
untrusted fast search, trusted small checking.
