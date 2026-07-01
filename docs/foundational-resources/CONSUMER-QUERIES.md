# Foundational Resource Consumer Queries

This page shows how a downstream consumer can ask useful questions about the
foundational-resource data contract without importing Axeyum internals.

The query surface is intentionally boring:

- [`artifacts/ontology/foundational-concepts.json`](../../artifacts/ontology/foundational-concepts.json)
- [`artifacts/examples/math/*/metadata.json`](../../artifacts/examples/math/)
- [`artifacts/examples/math/*/expected.json`](../../artifacts/examples/math/)
- [`scripts/query-foundational-resources.py`](../../scripts/query-foundational-resources.py)

The script reads only committed JSON files. It does not import validators,
generators, solver crates, or dashboard code, so it acts like a small external
consumer would.

For a compact all-field map of the current smoke-checked readiness routes,
bridge lookups, checked-row drilldowns, and theorem boundaries, see
[FIELD-READINESS-QUERY-MATRIX.md](FIELD-READINESS-QUERY-MATRIX.md).
For proof-route summaries and route-specific boundaries, see
[PROOF-ROUTE-QUERY-MATRIX.md](PROOF-ROUTE-QUERY-MATRIX.md).
For concept-plus-route matrix discovery, see
[MATRIX-COMPUTATION-QUERIES.md](MATRIX-COMPUTATION-QUERIES.md).

## Contract Summary

```sh
python3 scripts/query-foundational-resources.py summary
```

Use this first when checking that a checkout exposes the expected public data
shape. It reports concept-row counts, non-template pack counts,
expected-result counts, proof-status counts, and solver-reuse status counts.

JSON output is available when another tool needs stable parsing:

```sh
python3 scripts/query-foundational-resources.py summary --format json
```

## Solver-Reuse Candidates

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse candidate
```

This answers: "Which validated education packs are ready to consider for
regression, fuzz, or benchmark reuse?"

Candidate status is not the same as R5 promotion. A candidate is still R4 until
a regression, fuzz seed, benchmark slice, or explicit non-benchmark-horizon
back-link exists. It is valid for this query to return no rows after a candidate
batch has been fully promoted.

To list rows that already have solver-regression back-links:

```sh
python3 scripts/query-foundational-resources.py packs \
  --solver-reuse promoted \
  --require-any
```

## Field-Focused Pack Discovery

```sh
python3 scripts/query-foundational-resources.py packs \
  --field graph_theory \
  --format table
```

This answers: "What packs should a graph-theory consumer display or mine first?"
The row includes the pack path, trust status, expected-result mix, proof-status
mix, and solver-reuse status.

For machine consumers:

```sh
python3 scripts/query-foundational-resources.py packs \
  --field graph_theory \
  --format json
```

## Field And Proof-Route Discovery

```sh
python3 scripts/query-foundational-resources.py packs \
  --field probability_theory \
  --route Farkas \
  --require-any
```

This answers: "Which probability packs use or point at the exact-rational
Farkas route?" The route filter is a case-insensitive substring over public
route-bearing fields: fragments, proof-cookbook source refs, validation labels,
proof statuses, solver-reuse metadata, evidence metadata, and route notes. Pack
rows include `route_checks` and `route_validations` when a specific check row
matches; `pack-metadata` means the pack advertises that route at the metadata
level even if no individual check label contains the substring.
Hyphen and underscore spellings are normalized for substring search, so
`qf-bv` and `QF_BV` match the same route text.

## Proof-Route Summary Discovery

```sh
python3 scripts/query-foundational-resources.py routes \
  --route Farkas \
  --field linear_algebra \
  --require-any
```

This answers: "How much resource coverage does this proof route currently have
for this field?" Route summaries are generated from proof-cookbook recipe links
in pack metadata and report pack counts, check counts, proof-status mix,
result mix, solver-reuse status, fields, and sample packs.

The route filter uses normalized route aliases for active recipes. For example,
`lean` matches `lean-horizon-template` but does not match
`boolean-cnf-lrat`.

## Concept And Proof-Route Discovery

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_lu_replay \
  --route Farkas \
  --require-any
```

This answers: "Which packs are attached to this atlas bridge concept and also
use or point at this proof route?" Concept filters use the committed
`example_packs` list in the foundational concept atlas. Route filters keep the
same case-insensitive public-text behavior as field-focused pack discovery.

For concrete checked rows under a concept:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_residual_bound \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For a narrower row-level view, query checks directly:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --route qf-bv \
  --expected-result unsat \
  --require-any
```

Use this when a consumer needs concrete rows to display as checked examples,
rather than a list of route-relevant packs.

## Curriculum Field Readiness

```sh
python3 scripts/query-foundational-resources.py fields \
  --field probability_theory \
  --require-any
```

This answers: "For one university-curriculum field, how many packs and checks
are ready, which proof routes do they exercise, and which packs still carry
Lean-horizon rows?" The table includes pack and check counts, proof-status
counts, proof-cookbook route counts, solver-reuse status counts, sample packs,
and horizon packs.

Route filtering works over the same public route text used by pack discovery:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field graph_theory \
  --route boolean \
  --format json \
  --require-any
```

Use this view for curriculum navigation, dashboards, or external sites that
need a field-level readiness summary before drilling into individual packs or
checks.

For logic and proof, query the Boolean route to keep propositional truth-table
checks, proof-pattern examples, finite predicate expansion, small CNF
refutations, and finite graph/coloring refutations grouped while leaving full
proof-assistant automation, quantified metatheory, and general induction
schemas in the Lean-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field logic_and_proof \
  --route boolean \
  --require-any
```

Use the atlas lookup for reusable proof-route vocabulary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field logic_and_proof \
  --text proof \
  --require-any
```

To display concrete checked logic/proof rows, drill into checked Boolean
examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field logic_and_proof \
  --route boolean \
  --proof-status checked \
  --require-any
```

For set theory and foundations, query both the Alethe and Boolean routes:
Alethe keeps finite relations, functions, quotient maps, lattices,
continuous-map preimages, finite algebra maps, modules, tensors, and
equality-heavy finite structure rows grouped, while Boolean exposes finite
set-family and lattice refutations. ZFC, ordinals, choice, infinite
cardinality, and complete-lattice theorems stay in the proof-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field set_theory_and_foundations \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field set_theory_and_foundations \
  --route boolean \
  --require-any
```

Use atlas lookups for reusable partition, quotient, and finite Boolean-algebra
vocabulary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field set_theory_and_foundations \
  --text partition \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field set_theory_and_foundations \
  --text Boolean \
  --require-any
```

To display concrete checked foundation rows, drill into checked Alethe and
finite Boolean-algebra examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field set_theory_and_foundations \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_boolean_algebra \
  --route boolean \
  --proof-status checked \
  --require-any
```

For discrete math, query the Diophantine route to keep finite counting,
overlap-additivity, coefficient-convolution, exact tail-count, and finite
runtime-counter rows grouped while leaving asymptotic enumeration, recurrence
closed forms, and broad combinatorial theorem families in the proof-horizon
lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field discrete_math \
  --route Diophantine \
  --require-any
```

Use the finite atlas lookup for recurring finite bijection/cardinality,
quantifier-expansion, Boolean CNF, and integer-obstruction families. Use the
counting lookup when a consumer wants permutation/Pascal rows, pigeonhole
proofs, double-counting tables, coefficient extraction, orbit counts, and
exact finite tail counts grouped as one curriculum theme:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field discrete_math \
  --text finite \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field discrete_math \
  --text counting \
  --require-any
```

Concept-plus-route queries can then drill into the shared finite-counting
bridge without hard-coding pack names:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_counting_replay \
  --route boolean \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_counting_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

To display concrete checked discrete-math rows, drill into checked
Diophantine examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field discrete_math \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

For probability theory, query the Farkas route to keep finite probability
mass tables, conditioning and Bayes tables, product measures, pushforwards, conditional
expectations, stochastic kernels, finite Markov chains, martingales, hitting
times, concentration rows, and exact random-matrix moments grouped while
leaving continuous distributions, stochastic-process limit theorems, and
asymptotic probability theory in proof-horizon or numerical-honesty lanes:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field probability_theory \
  --route Farkas \
  --require-any
```

Use the atlas lookup for reusable finite-probability and finite random-matrix
vocabulary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field probability_theory \
  --text probability \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field probability_theory \
  --text random \
  --require-any
```

Concept-plus-route queries can find finite random-matrix moment packs and
checked rows without hard-coding the pack id:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_random_matrix_finite_moment \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_random_matrix_finite_moment \
  --route Farkas \
  --proof-status checked \
  --require-any
```

To display concrete checked probability rows, drill into checked Farkas
examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field probability_theory \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-markov-chain-v0 \
  --route Farkas \
  --proof-status checked \
  --text stationary \
  --require-any
```

For a field where the useful finite slice crosses several recent learner pages,
query the exact-rational route directly:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field differential_equations_and_dynamical_systems \
  --route Farkas \
  --require-any
```

That gives a compact readiness row for recurrence traces, Euler-step examples,
stochastic-kernel/hitting-time equations, and invariant-bound conflicts without
requiring a consumer to know which pack owns each topic.

Use the atlas lookup for deterministic finite dynamics/Euler replay and
stochastic-kernel/process bridge vocabulary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field differential_equations_and_dynamical_systems \
  --text Euler \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field differential_equations_and_dynamical_systems \
  --text stochastic \
  --require-any
```

Concept-plus-route queries can find finite recurrence, invariant, and Euler
packs without hard-coding the owning pack:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_dynamics_euler_replay \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_dynamics_euler_replay \
  --route Farkas \
  --proof-status checked \
  --require-any
```

To display concrete checked rows for a lesson or catalog card, drill into the
check table:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field differential_equations_and_dynamical_systems \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For topology, query the Boolean route to keep finite topology axioms,
finite open-cover refutations, connectedness counterexamples, finite
continuous-map/preimage rows, closure/interior replay, finite homeomorphism
replay, metric-ball examples, and bounded epsilon-delta shadows grouped; use
the Alethe route for finite specialization-order, cohomology, and
homeomorphism/preimage conflicts, use the Diophantine route for finite
boundary-operator, homology boundary-coefficient, and torsion-generator rows,
and use the QF_BV route for fixed one-bit finite cup-product contradictions.
Arbitrary
compactness, connectedness, homeomorphism invariance, specialization-order
theorems, homology/cohomology invariance, exact sequences, universal
coefficient theorems, and general cohomology-ring or cohomology-operation laws
remain in the proof-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field topology \
  --route boolean \
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

Use atlas lookups for the reusable topology bridge concepts:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text metric \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text compactness \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text preimage \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text closure \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text homeomorphism \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text quotient \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text specialization \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text boundary \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text homology \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text torsion \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text cohomology \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text universal \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field topology \
  --text cup \
  --require-any
```

Concept-plus-route queries find finite metric-ball and bounded
epsilon-delta rows, finite topology-operator/homeomorphism rows,
finite quotient-topology rows, finite specialization-order rows, finite
boundary-operator rows, finite
chain-complex/homology rows, finite torsion-homology rows, finite cohomology
rows, finite universal-coefficient shadow rows, and finite cup-product rows
without hard-coding pack ids:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_metric_ball \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_bounded_epsilon_delta_shadow \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_bounded_epsilon_delta_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_topology_operator_homeomorphism \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_topology_operator_homeomorphism \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_quotient_topology_replay \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_quotient_topology_replay \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_specialization_order_replay \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_specialization_order_replay \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_boundary_operator_replay \
  --route Diophantine \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_boundary_operator_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_chain_homology_replay \
  --route Diophantine \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_chain_homology_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_torsion_homology_replay \
  --route Diophantine \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_torsion_homology_replay \
  --route Diophantine \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_cohomology_replay \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_cohomology_replay \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_universal_coefficient_shadow \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_universal_coefficient_shadow \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_cup_product_replay \
  --route qf-bv \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_cup_product_replay \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

To display concrete checked topology rows, drill into the Boolean, Alethe,
Diophantine, and QF_BV routes separately:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --route alethe \
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

For measure theory, use the same field-readiness query to keep finite
event-algebra, product-measure, integration, random-variable, conditioning, and
stochastic-process examples grouped without treating the finite rows as
Lebesgue or convergence theorem coverage:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field measure_theory \
  --route Farkas \
  --require-any
```

The random-variable lane now includes checked rows for both a malformed
pushforward mass and a malformed expectation-through-pushforward claim:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-random-variables-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

The bridge rows are visible through the atlas query surface:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field measure_theory \
  --text finite \
  --require-any
```

To display concrete checked finite-measure or finite-integration examples, drill
into checked Farkas rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field measure_theory \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For statistics, query the Farkas route to keep exact finite tests,
contingency tables, least-squares regression, random-matrix finite moments,
finite probability/process tables, concentration rows, and stochastic-kernel
checks grouped while leaving floating-point inference, asymptotic sampling,
MCMC, VI, and model-calibration claims in numerical-honesty or proof-horizon
lanes:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field statistics \
  --route Farkas \
  --require-any
```

Use atlas lookups for reusable finite-table and tail-count vocabulary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field statistics \
  --text tail \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field statistics \
  --text finite \
  --require-any
```

To display concrete checked statistics rows, drill into the exact-rational and
integer-count routes separately:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field statistics \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack descriptive-statistics-v0 \
  --route Farkas \
  --proof-status checked \
  --text variance \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack exact-statistical-tests-v0 \
  --route Farkas \
  --proof-status checked \
  --text Fisher \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack exact-statistical-tests-v0 \
  --route Farkas \
  --proof-status checked \
  --text two-sided \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack exact-statistical-tests-v0 \
  --route Farkas \
  --proof-status checked \
  --text multinomial \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-concentration-v0 \
  --route Farkas \
  --proof-status checked \
  --text union \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field statistics \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

For linear algebra, query the Farkas route to keep exact rational systems,
residual bounds, least-squares normal equations, Rayleigh/eigenpair checks,
matrix-invariant rows, geometry dot-product rows, finite SDP/KKT/active-set
rows, and finite dynamics/process matrix equations grouped while keeping
spectral theorems, conditioning/stability, and general vector-space/module
theorems in the proof-horizon or numerical-honesty lanes:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field linear_algebra \
  --route Farkas \
  --require-any
```

Use the Alethe route when the consumer wants finite vector-space, dual-space,
module, tensor, and equality-heavy finite algebra rows:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field linear_algebra \
  --route Alethe \
  --require-any
```

Use atlas lookups for reusable matrix and functional vocabulary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field linear_algebra \
  --text rank \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field linear_algebra \
  --text projection \
  --require-any
```

To display concrete checked linear-algebra rows, drill into the exact-rational
and equality-heavy routes separately:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field linear_algebra \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field linear_algebra \
  --route Alethe \
  --proof-status checked \
  --require-any
```

For abstract algebra, query the Alethe route to keep equality-heavy finite
groups, monoids, permutation groups, homomorphisms, ideals, modules, vector
spaces, dual spaces, and tensor products grouped while leaving arbitrary
algebraic structure theorems, isomorphism theorems, and infinite algebra in
the theorem-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field abstract_algebra \
  --route Alethe \
  --require-any
```

Use atlas lookups for reusable algebra-map vocabulary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field abstract_algebra \
  --text homomorphism \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field abstract_algebra \
  --text ideal \
  --require-any
```

To display concrete checked algebra rows, drill into equality-heavy and
fixed-width finite-algebra routes separately:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field abstract_algebra \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_homomorphism_preservation \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field abstract_algebra \
  --route qf-bv \
  --proof-status checked \
  --require-any
```

For number theory, query the Diophantine route to keep gcd/Bezout,
nonunit modular inverse, integer interval obstruction, bounded induction
parity, and bounded Diophantine witness rows grouped while leaving unbounded
number-theory theorem claims in the Lean-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field number_theory \
  --route Diophantine \
  --require-any
```

Use the finite vocabulary lookup to expose the shared Diophantine and
fixed-width residue families, the totality lookup to expose operation
conventions and side-condition boundaries, the gcd lookup to expose
divisibility witness and non-divisibility certificate vocabulary, and the CRT
lookup to expose concrete modular congruence and inverse witnesses:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field number_theory \
  --text finite \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field number_theory \
  --text totality \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field number_theory \
  --text gcd \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field number_theory \
  --text CRT \
  --require-any
```

To display concrete checked integer-arithmetic rows, drill into checked
Diophantine examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field number_theory \
  --route Diophantine \
  --proof-status checked \
  --require-any
```

For graph theory, query the Boolean route to keep finite coloring,
reachability, matching, cut, and d-separation refutations grouped. Query the
LIA route for finite BFS/DFS traversal-cost counters and bad DFS-bound rows.
Leave asymptotic algorithm analysis and unbounded graph-theorem coverage in
the proof-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field graph_theory \
  --route boolean \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field graph_theory \
  --route LIA \
  --require-any
```

Use the graph atlas lookup for the reusable Boolean CNF and fixed-width graph
families, plus reachability lookup for the shared finite graph replay bridge:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field graph_theory \
  --text graph \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field graph_theory \
  --text reachability \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field graph_theory \
  --text runtime \
  --require-any
```

Concept-plus-route queries can find graph packs and checked rows without
hard-coding whether the row came from coloring, reachability, runtime counters,
matching, cut, or d-separation:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_graph_replay_obstruction \
  --route boolean \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_graph_replay_obstruction \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_graph_replay_obstruction \
  --route LIA \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_graph_replay_obstruction \
  --route LIA \
  --proof-status checked \
  --require-any
```

To display concrete checked graph rows, drill into checked Boolean and LIA
examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --route boolean \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --route LIA \
  --proof-status checked \
  --require-any
```

For real analysis, query the Farkas route to keep bounded epsilon-delta
shadows, rational interval/ball rows, finite sequence-prefix rows, exact
derivative and integral shadows, root-finding iterations, geometry rows, and
optimization-step rows grouped while leaving completeness, IVT/MVT/FTC,
general convergence, compactness, and theorem-level calculus in the
Lean-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field real_analysis \
  --route Farkas \
  --require-any
```

Use atlas lookups for reusable bounded-analysis vocabulary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text epsilon \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text metric \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field real_analysis \
  --text gradient \
  --require-any
```

To display concrete checked real-analysis rows, drill into checked Farkas
examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field real_analysis \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For numerical analysis, query the Farkas route to keep exact residual bounds,
Euler-step rows, recurrence traces, root-finding iterations, finite operator
checks, and finite optimization-step rows grouped while leaving floating-point
roundoff, conditioning/stability, asymptotic error analysis, and convergence
theorems in numerical-honesty or proof-horizon lanes:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field numerical_analysis \
  --route Farkas \
  --require-any
```

Use atlas lookups for reusable numerical vocabulary and the exact-vs-floating
boundary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field numerical_analysis \
  --text residual \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field numerical_analysis \
  --text operator \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field numerical_analysis \
  --text floating \
  --require-any
```

To display concrete checked numerical-analysis rows, drill into checked
Farkas examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field numerical_analysis \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For the finite iterative-method slice, the current source-linked Jacobi
error-bound row can be queried directly:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack numerical-linear-algebra-v0 \
  --route Farkas \
  --proof-status checked \
  --text Jacobi \
  --require-any
```

For complex analysis, query the Farkas route to keep exact real-pair complex
arithmetic, norm, unit-circle transform, and polynomial-discriminant rows
grouped while leaving holomorphic, contour-integral, analytic-continuation,
and general complex-analysis theorems in the Lean-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field complex_analysis \
  --route Farkas \
  --require-any
```

Use the atlas lookup for the reusable real-pair encoding boundary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field complex_analysis \
  --text real-pair \
  --require-any
```

To display concrete checked complex-analysis rows, drill into checked Farkas
examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field complex_analysis \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For optimization and convexity, query the Farkas route to keep exact LP
thresholds, finite convexity shadows, regression normal equations, residual
bounds, gradient/Hessian replay, finite KKT stationarity, finite SDP
objective/slack replay, finite gradient-descent replay, and finite
line-search replay, finite Wolfe line-search replay, finite active-set QP
replay, finite projected-gradient replay, and finite proximal-gradient replay together while
leaving duality, KKT sufficiency, SDP strong duality, line-search convergence,
Wolfe line-search convergence, active-set convergence, projected-gradient convergence,
proximal-gradient convergence, and convergence
claims in the proof-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field optimization_and_convexity \
  --route Farkas \
  --require-any
```

Use atlas lookups for the two reusable bridge concepts:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field optimization_and_convexity \
  --text objective \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field optimization_and_convexity \
  --text convexity \
  --require-any
```

To display concrete checked optimization, convexity, finite SDP, finite
active-set QP, finite gradient-descent, finite line-search, finite Wolfe
line-search, finite projected-gradient, finite proximal-gradient, least-squares, gradient,
residual, Rayleigh, or eigenpair rows, drill
into checked Farkas examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field optimization_and_convexity \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For geometry, use the Farkas route to keep finite coordinate, incidence,
rigid-configuration, affine, oriented-area, circle-geometry, inversion, and
cyclic-configuration replay together while leaving synthetic, projective,
circle-theorem, inversion-theorem, cyclic-theorem, and differential geometry
claims in the proof-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field geometry \
  --route Farkas \
  --require-any
```

Use the atlas lookup for shared coordinate/orientation geometry vocabulary and
the narrower circle/inversion/cyclic replay bridge:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field geometry \
  --text coordinate \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field geometry \
  --text circle \
  --require-any
```

Concept-plus-route queries can find circle, inversion, and cyclic-configuration
packs without hard-coding each pack id:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_circle_inversion_cyclic_replay \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_circle_inversion_cyclic_replay \
  --route Farkas \
  --proof-status checked \
  --require-any
```

To display concrete checked geometry rows, drill into checked Farkas examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field geometry \
  --route Farkas \
  --proof-status checked \
  --require-any
```

For functional analysis and operator theory, query the same exact-rational
route to group finite-dimensional operator bounds, inner-product positivity,
projection-orthogonality, Chebyshev duplicate-node grids, spectral/eigenpair
and Rayleigh witnesses, and dual-space rows while keeping Banach, Hilbert,
compact-operator, minimax, and infinite-dimensional approximation claims in
the proof-horizon lane:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field functional_analysis_and_operator_theory \
  --route Farkas \
  --require-any
```

Use the atlas query to expose the shared operator and Chebyshev bridge
vocabulary:

```sh
python3 scripts/query-foundational-resources.py concepts \
  --field functional_analysis_and_operator_theory \
  --text operator \
  --require-any

python3 scripts/query-foundational-resources.py concepts \
  --field functional_analysis_and_operator_theory \
  --text Chebyshev \
  --require-any
```

Concept-plus-route queries can find the finite operator, Chebyshev,
spectral, characteristic-polynomial, and checked trace-invariant packs without
hard-coding pack ids:

```sh
python3 scripts/query-foundational-resources.py packs \
  --concept bridge_finite_operator_chebyshev \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_operator_chebyshev \
  --route Farkas \
  --proof-status checked \
  --require-any
```

To display concrete checked finite-operator norm/bound, inner-product
positivity/projection, Chebyshev, spectral, and matrix-invariant rows, drill
into checked Farkas examples:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field functional_analysis_and_operator_theory \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Proof And Check Mining

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --expected-result unsat \
  --proof-status checked \
  --require-any
```

This answers: "Which checked graph-theory negative examples can be shown as
trusted-small-checking examples?"

Other useful filters:

```sh
python3 scripts/query-foundational-resources.py checks --fragment QF_LRA --proof-status checked
python3 scripts/query-foundational-resources.py checks --validation farkas --expected-result unsat
python3 scripts/query-foundational-resources.py checks --pack logic-basics-v0
python3 scripts/query-foundational-resources.py checks --text counterexample
```

The table output truncates long claims for readability. Use `--format json` for
the full row text.

## Atlas Concept Queries

```sh
python3 scripts/query-foundational-resources.py concepts \
  --kind example-family \
  --format json \
  --require-any
```

This answers: "Which reusable cross-pack families already exist in the atlas?"

Other useful filters:

```sh
python3 scripts/query-foundational-resources.py concepts --field linear_algebra
python3 scripts/query-foundational-resources.py concepts --decidability proof-horizon
python3 scripts/query-foundational-resources.py concepts --pack finite-cardinality-v0
python3 scripts/query-foundational-resources.py concepts --text totality
python3 scripts/query-foundational-resources.py concepts --text floating
python3 scripts/query-foundational-resources.py concepts --text Lean
```

## What These Queries Prove

These queries prove the public JSON contract is readable and useful for common
consumer workflows:

- locating packs by field, curriculum node, fragment, or proof status;
- mining checked `sat` and `unsat` rows for learner or benchmark views;
- finding candidate and promoted solver-reuse rows without scanning prose;
- listing reusable concept families from the atlas.
- summarizing field-level curriculum readiness before drilling into packs.

They do not prove solver correctness, proof-certificate validity, or general
mathematical theorem coverage. Those remain the job of the example-pack
validators, route-specific cargo regressions, proof-cookbook checks, and future
Lean reconstruction work.

## CI Smoke Coverage

[`scripts/check-foundational-resources.sh`](../../scripts/check-foundational-resources.sh)
runs a small query smoke set after validating concepts and packs:

```sh
python3 scripts/query-foundational-resources.py summary >/dev/null
python3 scripts/query-foundational-resources.py routes --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route Diophantine --field number_theory --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route Farkas --field linear_algebra --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route Alethe --field abstract_algebra --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route lean --field topology --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse promoted --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field probability_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --kind example-family --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field probability_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field probability_theory --text probability --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field probability_theory --text random --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field probability_theory --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_random_matrix_finite_moment --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_random_matrix_finite_moment --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field logic_and_proof --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field logic_and_proof --text proof --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field logic_and_proof --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field set_theory_and_foundations --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field set_theory_and_foundations --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field set_theory_and_foundations --text partition --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field set_theory_and_foundations --text Boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field set_theory_and_foundations --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_boolean_algebra --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field discrete_math --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field discrete_math --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field discrete_math --text counting --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field discrete_math --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_counting_replay --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_counting_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field differential_equations_and_dynamical_systems --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text Euler --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text stochastic --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_dynamics_euler_replay --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field topology --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field topology --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field topology --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text compactness --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text metric --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text preimage --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text closure --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text homeomorphism --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text specialization --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text boundary --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text homology --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text torsion --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text cohomology --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text universal --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text cup --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_metric_ball --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_bounded_epsilon_delta_shadow --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_bounded_epsilon_delta_shadow --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_topology_operator_homeomorphism --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_topology_operator_homeomorphism --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_specialization_order_replay --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_specialization_order_replay --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_boundary_operator_replay --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_boundary_operator_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_chain_homology_replay --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_chain_homology_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_torsion_homology_replay --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_torsion_homology_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_cohomology_replay --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_cohomology_replay --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_universal_coefficient_shadow --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_universal_coefficient_shadow --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_cup_product_replay --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_cup_product_replay --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field measure_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field measure_theory --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field measure_theory --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field statistics --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text tail --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text random --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field statistics --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack descriptive-statistics-v0 --route Farkas --proof-status checked --text variance --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack exact-statistical-tests-v0 --route Farkas --proof-status checked --text Fisher --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack exact-statistical-tests-v0 --route Farkas --proof-status checked --text two-sided --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack exact-statistical-tests-v0 --route Farkas --proof-status checked --text multinomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field statistics --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field linear_algebra --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field linear_algebra --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field linear_algebra --text rank --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field linear_algebra --text projection --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field linear_algebra --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field linear_algebra --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_lu_replay --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_rank_nullity --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field abstract_algebra --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text homomorphism --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text ideal --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field abstract_algebra --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_homomorphism_preservation --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field abstract_algebra --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field number_theory --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field number_theory --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field number_theory --text totality --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field number_theory --text gcd --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field number_theory --text CRT --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field number_theory --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field graph_theory --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field graph_theory --route LIA --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text graph --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text reachability --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text runtime --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_graph_replay_obstruction --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_graph_replay_obstruction --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_graph_replay_obstruction --route LIA --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_graph_replay_obstruction --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field real_analysis --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text epsilon --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text metric --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text gradient --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field real_analysis --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field numerical_analysis --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text residual --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text operator --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text floating --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field numerical_analysis --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field complex_analysis --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field complex_analysis --text real-pair --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field complex_analysis --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field optimization_and_convexity --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field optimization_and_convexity --text objective --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field optimization_and_convexity --text convexity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field optimization_and_convexity --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field geometry --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field geometry --text coordinate --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field geometry --text circle --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field geometry --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_circle_inversion_cyclic_replay --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_circle_inversion_cyclic_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field functional_analysis_and_operator_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field functional_analysis_and_operator_theory --text operator --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field functional_analysis_and_operator_theory --text Chebyshev --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_operator_chebyshev --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_operator_chebyshev --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field functional_analysis_and_operator_theory --route Farkas --proof-status checked --require-any >/dev/null
```

That keeps the examples on this page aligned with the committed data boundary
without turning the query helper into a replacement validator.
