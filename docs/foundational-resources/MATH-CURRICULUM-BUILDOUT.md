# Math Curriculum Resource Buildout Plan

## Objective

Build the sibling-resource ecosystem outward from the existing
[formal mathematics curriculum](../curriculum/README.md). The curriculum DAG in
[`docs/curriculum/curriculum.toml`](../curriculum/curriculum.toml) is the seed:
every concept row, example pack, learner page, proof route, and dashboard entry
should trace back to either a curriculum node or an explicit extension field in
the [University Math Field Taxonomy](MATH-FIELDS.md).

The product is not a textbook and not a formal-library clone. It is a set of
small, checkable resources that make the same point over and over:

```text
untrusted fast search, trusted small checking
```

For this buildout, "done" means machine-readable rows validate, examples replay,
proof/evidence status is explicit, and generated views show coverage and gaps.

## Inputs And Outputs

### Inputs

| Input | Role |
|---|---|
| [curriculum.toml](../curriculum/curriculum.toml) | Authoritative 23-node prerequisite DAG, decidability labels, and current testability status. |
| [MATH-FIELDS.md](MATH-FIELDS.md) | Authoritative 18-field math taxonomy for undergraduate/graduate expansion. |
| [SMT Fragment Atlas](../atlas/README.md) | Canonical solver/theory/fragment names and support status. |
| [Proof Certificate Cookbook](../proof-cookbook/README.md) | Canonical evidence and proof-route vocabulary. |
| [Rules-as-Code Lab](../rules-as-code/README.md) | Existing example-pack structure and validation discipline. |
| [curriculum backlog](../curriculum/BACKLOG.md) | First high-yield decidable math examples. |
| [curriculum depth note](../curriculum/DEPTH.md) | Guardrails against overstating bounded examples as full textbook coverage. |

### Planned Outputs

```text
artifacts/ontology/
  foundational-concepts.schema.json
  foundational-concepts.json
  foundational-example-pack.schema.json

artifacts/examples/math/
  <example-pack-id>/
    README.md
    metadata.json
    model.md
    checks.md
    expected.json

docs/foundational-resources/
  MATH-CURRICULUM-BUILDOUT.md
  generated/
    math-coverage.md
    math-field-dashboard.md
    proof-gap-dashboard.md

docs/learn/math/
  README.md
  <lesson>.md

scripts/
  validate-foundational-concepts.py
  validate-foundational-example-pack.py
  gen-foundational-dashboards.py
```

Defer new crates until at least three example packs duplicate enough logic to
prove a library boundary.

## Resource Lanes

### Lane 1: Foundational Concept Atlas

The atlas is the root data product. It should start with the curriculum DAG,
then add field-extension rows.

Minimum row fields:

- `id`: stable snake-case identifier;
- `kind`: `curriculum-node`, `field`, `bridge-concept`, or `example-family`;
- `title`;
- `domain`: `mathematics`, `computer-science`, `logic`, or `statistics`;
- `field_ids`: one or more IDs from [MATH-FIELDS.md](MATH-FIELDS.md);
- `curriculum_node`: optional existing curriculum node id;
- `prerequisites` and `unlocks`;
- `decidability`: `decidable`, `computable`, `bounded`, `numerical`, or
  `proof-horizon`;
- `axeyum_fragments`: references to SMT Fragment Atlas rows or local theory
  labels;
- `example_packs`;
- `proof_routes`: replay, SAT proof, LRAT/DRAT, Farkas, Alethe, Lean, or gap;
- `source_refs`: local docs and upstream source notes;
- `graduation`: concrete criteria for promoting status.

Rules:

- No `covered` or `validated` claim without at least one validating command.
- No `unsat` claim without a named evidence route or an explicit proof gap.
- No general theorem claim when only fixed-size or finite-domain examples exist.
- Every `field_id` must validate against [MATH-FIELDS.md](MATH-FIELDS.md).
- Every `axeyum_fragments` entry should eventually cross-link to the SMT
  Fragment Atlas.

### Lane 2: Example Packs

Example packs are the executable counterpart to concept rows.

Minimum pack files:

- `README.md`: audience, concept rows, theorem/claim shape, limitations;
- `metadata.json`: stable id, concepts, fields, fragments, proof route,
  validator command;
- `model.md`: finite model, encoding sketch, symbols, assumptions;
- `checks.md`: list of SAT/UNSAT/UNKNOWN checks and expected trust story;
- `expected.json`: machine-readable expected results and witnesses;
- optional generated evidence artifacts only when small and stable.

Pack validation requirements:

- Replay every SAT witness against the original mathematical claim.
- For UNSAT, either check evidence or mark the proof route as missing.
- Treat `unknown` as an accepted result only when the pack says why.
- Keep all examples deterministic: explicit seeds, fixed sizes, fixed
  time/resource limits.

### Lane 3: Education Pages

Each learner-facing page should be generated from or linked to concept rows and
example packs. The page pattern is:

1. State the concept in plain language.
2. Show the finite or computable fragment Axeyum can check.
3. Encode one tiny instance.
4. Show a model, counterexample, or proof/evidence route.
5. State the proof horizon honestly.

Do not write generic textbook chapters. Write small "what can be checked and
why" lessons.

### Lane 4: Proof And Certificate Hooks

Every example pack should name a proof route even before the route exists.
The Proof Certificate Cookbook is the vocabulary source.

Near-term proof-route targets:

- SAT/CNF/LRAT for pigeonhole and graph-coloring refutations;
- Farkas/LRA for rationals, linear systems, and LP infeasibility;
- EUF/Alethe for finite functions and equality-heavy examples;
- replay-only for finite algebra tables and SAT witnesses;
- Lean-horizon for induction schemas, limits, topology, measure, and infinite
  cardinality.

### Lane 5: Dashboards

Generated dashboards turn the resources into a planning and measurement surface.

Required first views:

- coverage by curriculum node;
- coverage by math field;
- coverage by decidability class;
- coverage by proof/evidence route;
- list of example packs with validation commands;
- proof gaps grouped by solver fragment and field.

Dashboards should be regenerated, not edited by hand.

## Curriculum Node Mapping

This table is the first expansion contract. Every curriculum node gets an atlas
row and a pack target, even if the initial pack is only proof-horizon metadata.

| Curriculum Node | Field IDs | First Resource Target | First Checkable Slice |
|---|---|---|---|
| `propositional-logic` | `logic_and_proof` | `logic-basics-v0` | SAT/UNSAT Boolean formulas, truth tables, CNF refutations. |
| `predicate-logic` | `logic_and_proof`, `set_theory_and_foundations` | `finite-predicate-v0` | Finite-domain quantifier expansion and counterexamples. |
| `proof-methods` | `logic_and_proof` | `proof-methods-refutation-v0` | Negate-and-decide examples; proof by contradiction as UNSAT. |
| `induction` | `logic_and_proof`, `number_theory` | `induction-obligations-v0` | Bounded base/step obligations; general induction marked Lean-horizon. |
| `sets` | `set_theory_and_foundations` | `finite-sets-v0` | Membership, subset, union/intersection, finite identities. |
| `relations-and-functions` | `set_theory_and_foundations`, `discrete_math` | `relations-functions-v0` | Finite relation properties, injective/surjective checks, EUF slices. |
| `cardinality` | `set_theory_and_foundations`, `discrete_math` | `finite-cardinality-v0` | Finite bijections/counting; infinite cardinality marked Lean-horizon. |
| `naturals` | `number_theory`, `discrete_math` | `natural-arithmetic-v0` | Bounded Peano arithmetic and LIA/BV arithmetic identities. |
| `integers` | `number_theory` | `integer-lia-v0` | Linear integer equations/inequalities and witnesses. |
| `rationals` | `real_analysis`, `linear_algebra` | `rationals-lra-v0` | Exact rational order/field facts, density, trichotomy, Farkas links. |
| `reals` | `real_analysis`, `optimization_and_convexity` | `reals-rcf-shadow-v0` | Algebraic real constraints through LRA/NRA; completeness marked horizon. |
| `complex` | `complex_analysis`, `linear_algebra` | `complex-algebraic-v0` | Complex arithmetic as real-pair algebraic constraints. |
| `divisibility-and-euclid` | `number_theory` | `gcd-bezout-v0` | GCD, Bezout witness replay, divisibility checks. |
| `modular-arithmetic` | `number_theory`, `abstract_algebra` | `modular-arithmetic-v0` | Congruences, inverses, CRT, fixed-modulus enumeration. |
| `groups` | `abstract_algebra` | `finite-groups-v0` | Cayley-table closure, identity, inverse, associativity checks. |
| `rings` | `abstract_algebra` | `finite-rings-v0` | Two-operation table checks and distributivity. |
| `fields` | `abstract_algebra`, `number_theory` | `finite-fields-v0` | Field axioms over small prime fields; composite modulus counterexamples. |
| `polynomials` | `abstract_algebra`, `real_analysis`, `complex_analysis` | `polynomial-identities-v0` | Fixed-degree identities, factor theorem, root witness replay. |
| `sequences-and-limits` | `real_analysis`, `topology` | `sequence-limit-shadow-v0` | Bounded epsilon/N templates and algebraic sequence checks; general limits marked Lean-horizon. |
| `counting` | `discrete_math`, `probability_theory` | `counting-v0` | Permutations, combinations, pigeonhole finite instances. |
| `number-theory` | `number_theory` | `number-theory-v0` | CRT, quadratic residues, sum of squares, bounded Diophantine checks. |
| `linear-algebra` | `linear_algebra`, `numerical_analysis`, `optimization_and_convexity` | `linear-algebra-rational-v0` | Fixed rational matrices, LU replay, inverse checks, inconsistent systems. |
| `calculus` | `real_analysis`, `differential_equations_and_dynamical_systems`, `numerical_analysis` | `calculus-algebraic-shadow-v0` | Polynomial derivative identities and algebraic inequalities; epsilon-delta/integration marked Lean-horizon. |

## Field Extensions Beyond The Current Curriculum

These rows widen the existing DAG into the 18-field university taxonomy without
losing the curriculum anchor.

| Field | Curriculum Anchor | First New Resource |
|---|---|---|
| `graph_theory` | sets, relations, counting | `graph-coloring-v0`, then reachability, matching, cuts, and d-separation. |
| `topology` | sets, reals, sequences-and-limits | `finite-topology-v0`, then metric balls and closure/interior finite checks. |
| `measure_theory` | sets, rationals, probability | `finite-measure-v0` over finite universes; Lebesgue theory remains horizon. |
| `probability_theory` | counting, rationals, finite sets | `finite-probability-v0`, Bayes tables, exact discrete distributions. |
| `statistics` | probability, rationals, linear algebra | `descriptive-statistics-v0`, contingency tables, exact small tests. |
| `optimization_and_convexity` | rationals, reals, linear algebra | `linear-optimization-v0`, LP feasibility, dual/Farkas certificates, threshold checks. |
| `numerical_analysis` | linear algebra, real algebra | `numerical-linear-algebra-v0`, LU replay, interval bounds, error recurrences. |
| `differential_equations_and_dynamical_systems` | calculus, linear algebra | `bounded-dynamics-v0`, recurrence and invariant checks before continuous theory. |
| `geometry` | reals, polynomials, linear algebra | `coordinate-geometry-v0`, incidence, distance, midpoint, collinearity. |
| `functional_analysis_and_operator_theory` | linear algebra, real analysis | `finite-operator-v0`, norms, matrices as operators, Chebyshev polynomial slices. |

## Phased Build Plan

### Phase M0: Alignment

Status: this plan.

Exit criteria:

- The buildout plan is linked from resource navigation.
- `STATUS.md` records the plan.
- No new data format is introduced without a validator target.

### Phase M1: Atlas Schema And Seed Rows

Status: first seed landed for the mathematics lane. The repository now has a
schema, deterministic generator, validator, committed JSON atlas, and generated
dashboards covering all 23 curriculum nodes and all 18 math fields. Validated
example packs remain future phases.

Deliverables:

- `artifacts/ontology/foundational-concepts.schema.json`.
- `artifacts/ontology/foundational-concepts.json`.
- `scripts/validate-foundational-concepts.py`.

Implementation notes:

- Seed all 23 curriculum nodes from `curriculum.toml`.
- Add 18 field rows from [MATH-FIELDS.md](MATH-FIELDS.md).
- Add a `field_ids` validation table in the validator.
- Validate prerequisite IDs, local links, enum values, and duplicate IDs.
- Report coverage by `status`, `decidability`, `field_id`, and `axeyum_fragment`.

Exit criteria:

- Validator passes on a clean checkout.
- Every curriculum node appears exactly once.
- Every math field appears at least once.
- `covered` curriculum nodes either link an existing family or carry an explicit
  migration note explaining what still needs a pack.

### Phase M2: Example-Pack Schema And Scaffold

Status: scaffold landed. The repository now has an example-pack schema, a
validator, a validating template pack under `artifacts/examples/math/template-v0/`,
and the first substantive pack under
`artifacts/examples/math/proof-methods-refutation-v0/`; the first replay-checked
number-theory pack lives under `artifacts/examples/math/modular-arithmetic-v0/`;
the first exact-rational pack lives under `artifacts/examples/math/rationals-lra-v0/`;
the first exact rational linear-algebra pack lives under
`artifacts/examples/math/linear-algebra-rational-v0/`.

Deliverables:

- `artifacts/ontology/foundational-example-pack.schema.json`.
- `scripts/validate-foundational-example-pack.py`.
- `artifacts/examples/math/TEMPLATE/` or documented template.

Implementation notes:

- Model the pack structure after the rules-as-code pack.
- Require `concept_ids`, `field_ids`, `claim_status`, `trust_status`,
  `validator_command`, and `expected_results`.
- Allow packs to start as `planned`, but require explicit graduation criteria.

Exit criteria:

- One empty/template pack validates.
- The concept validator checks every referenced pack path.
- The docs link checker remains clean.

### Phase M3: Core Curriculum Packs

Build the existing DAG before adding too many adjacent fields.

Recommended order:

1. `proof-methods-refutation-v0`: negation-as-query, pigeonhole, CNF/LRAT gap
   or checked route.
2. `finite-sets-v0` and `relations-functions-v0`: finite set identities,
   relation properties, function properties.
3. `modular-arithmetic-v0`: CRT, modular inverse, residue witness checks.
4. `finite-fields-v0`: prime-field axioms and composite-modulus counterexample.
5. `rationals-lra-v0`: density/trichotomy and exact rational LRA certificates.
6. `linear-algebra-rational-v0`: fixed matrices, LU replay, inconsistent
   system with Farkas evidence where available.
7. `polynomial-identities-v0`: factor theorem and fixed-degree identities.
8. `counting-v0`: combinations, pigeonhole, finite counting witnesses.

Exit criteria:

- At least eight packs validate.
- At least three packs include checked UNSAT evidence, not only SAT witnesses.
- Curriculum rows for `planned` nodes are updated as packs land.
- Any missing proof route is explicitly listed in the proof-gap dashboard.

### Phase M4: Field Expansion Packs

Add the fields users naturally expect from an undergraduate/graduate math map.

Status: first field-extension packs landed.
`artifacts/examples/math/graph-coloring-v0/` now validates coloring witnesses
and a tiny exhaustive non-colorability check.
`artifacts/examples/math/finite-probability-v0/` now validates finite
probability mass tables, conditional probability, and Bayes posterior replay.
`artifacts/examples/math/descriptive-statistics-v0/` now validates exact
mean/variance identities, contingency-table margins, and a Simpson's paradox
count-table witness.
`artifacts/examples/math/linear-optimization-v0/` now validates LP feasibility
witnesses, objective-threshold replay, and a tiny checked Farkas certificate.
`artifacts/examples/math/coordinate-geometry-v0/` now validates exact midpoint,
collinearity, and squared-distance coordinate checks.
`artifacts/examples/math/finite-topology-v0/` now validates finite topology
axioms, closure/interior computation, and exact finite metric-ball replay.
`artifacts/examples/math/finite-measure-v0/` now validates finite
sigma-algebra axioms, exact finite additivity, and event/complement measure
replay.
`artifacts/examples/math/bounded-dynamics-v0/` now validates exact rational
recurrence traces, bounded invariant witnesses, and threshold reachability
replay.

Recommended order:

1. `graph-coloring-v0`: SAT colorings, non-colorability, certificate status.
2. `finite-probability-v0`: probability mass, conditioning, Bayes rule.
3. `descriptive-statistics-v0`: mean/variance identities, contingency tables,
   Simpson witness.
4. `linear-optimization-v0`: LP feasibility, threshold cliffs, Farkas links.
5. `coordinate-geometry-v0`: collinearity, midpoint, distance constraints.
6. `finite-topology-v0`: finite closure/interior and metric-ball examples.
7. `finite-measure-v0`: finite sigma-algebras and finite measure checks.
8. `bounded-dynamics-v0`: recurrence systems and invariant checks.
9. `finite-operator-v0`: finite-dimensional norms/operators and Chebyshev
   polynomial examples.
10. `complex-algebraic-v0`: complex arithmetic as real-pair algebra.

Exit criteria:

- Every Band A field from [MATH-FIELDS.md](MATH-FIELDS.md) has one validating
  pack.
- Every Band B field has either a validating pack or a concrete planned pack.
- Every Band C field has a proof-horizon row with a named first finite slice.

### Phase M5: Lessons And Learner Paths

Deliverables:

- `docs/learn/math/README.md`.
- One lesson path per major cluster:
  - logic and proof;
  - sets, relations, and finite structures;
  - number systems and arithmetic;
  - algebra and number theory;
  - rational/real algebra;
  - graph/discrete reasoning;
  - linear algebra and optimization;
  - probability and statistics;
  - analysis/topology proof horizons.

Exit criteria:

- Every lesson links at least one concept row and one example pack.
- Every lesson states "what Axeyum checks" and "what requires Lean or remains
  numerical/proof-horizon."
- No lesson duplicates source-of-truth metadata that should be generated from
  JSON.

### Phase M6: Proof Cookbook Integration

Deliverables:

- Proof recipe links from each example pack.
- New cookbook recipes where the resource plan exposes repeated gaps.

Priority recipes:

1. CNF/LRAT for pigeonhole and graph coloring.
2. LRA/Farkas for rational inequalities and inconsistent systems.
3. Finite-function/EUF congruence for relation/function packs.
4. Bounded arithmetic/Diophantine route for number-theory packs.
5. "Lean horizon" recipe template for induction, topology, measure, and limits.

Exit criteria:

- Every UNSAT example has either a checked route or a cookbook gap.
- The proof-gap dashboard is generated from pack metadata.
- At least one lesson shows the trusted-small-checking loop end to end.

### Phase M7: Generated Dashboards And CI Hook

Deliverables:

- `docs/foundational-resources/generated/math-coverage.md`.
- `docs/foundational-resources/generated/math-field-dashboard.md`.
- `docs/foundational-resources/generated/proof-gap-dashboard.md`.
- Optional `just check-foundational-resources` target once scripts stabilize.

Exit criteria:

- Dashboards are deterministic.
- Validators run in the normal docs/check workflow or have a documented command.
- Dashboard output names gaps without manual editing.

### Phase M8: Library Boundary Decision

Only after the data and examples reveal repeated logic, decide whether to add a
workspace crate or split a sibling repository.

Possible boundaries:

- `axeyum-foundational-data`: generated JSON and schema consumers.
- `axeyum-math-examples`: reusable encoders for graph, finite algebra, matrix,
  and finite probability examples.
- Separate repository only if the resources gain an independent release cycle,
  large corpora, or users who do not need the Axeyum source tree.

Exit criteria:

- At least 40 validated concept rows.
- At least 12 validated example packs.
- At least 6 packs with checked proof/evidence routes.
- At least one downstream consumer can read the data without repository-internal
  knowledge.

## First Ten Commits To Make

1. Add `foundational-concepts.schema.json` and a validator with no data.
2. Seed `foundational-concepts.json` with 23 curriculum nodes and 18 field rows.
3. Add generated coverage dashboard for those rows.
4. Add `foundational-example-pack.schema.json` and a template pack.
5. Add `proof-methods-refutation-v0` with pigeonhole metadata and proof gap.
6. Add `modular-arithmetic-v0` from the curriculum backlog.
7. Add `rationals-lra-v0` with density/trichotomy checks.
8. Add `linear-algebra-rational-v0` with LU and inconsistent-system examples.
9. Add `graph-coloring-v0` as the first pure field-extension pack.
10. Add `finite-probability-v0` and `descriptive-statistics-v0` as the
    probability/statistics bridge.

Each commit should update `STATUS.md`, run the relevant validator, and keep the
docs link checker clean.

Progress: items 1-10 and Phase M4 items 4-8 have landed for the math seed.
Continue Phase M4 with `finite-operator-v0`.

## Operating Rules

- The curriculum DAG stays authoritative for math prerequisites until a new ADR
  changes that.
- The field taxonomy classifies expansion; it does not replace prerequisites.
- Example packs are small by design. If a pack becomes a corpus, move the corpus
  out of docs and keep only metadata and regeneration instructions here.
- Treat approximate numerical and statistical material as reproducible
  experiments, not proof.
- Never promote a resource because the prose is good. Promote it because the
  row validates, the examples replay, and the proof/evidence status is explicit.
