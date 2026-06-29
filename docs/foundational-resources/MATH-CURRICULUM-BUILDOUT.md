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
propositional-logic pack lives under
`artifacts/examples/math/logic-basics-v0/`;
the first replay-checked
bounded induction pack lives under
`artifacts/examples/math/induction-obligations-v0/`;
the first finite predicate-logic pack lives under
`artifacts/examples/math/finite-predicate-v0/`;
the first replay-checked number-theory pack lives under
`artifacts/examples/math/modular-arithmetic-v0/`;
the first gcd/Bezout core arithmetic pack lives under
`artifacts/examples/math/gcd-bezout-v0/`;
the first bounded number-theory destination pack lives under
`artifacts/examples/math/number-theory-v0/`;
the first exact-integer LIA pack lives under
`artifacts/examples/math/integer-lia-v0/`;
the first bounded natural-arithmetic pack lives under
`artifacts/examples/math/natural-arithmetic-v0/`;
the first finite-set core curriculum pack lives under
`artifacts/examples/math/finite-sets-v0/`;
the first relation/function core curriculum pack lives under
`artifacts/examples/math/relations-functions-v0/`;
the first finite-cardinality foundations pack lives under
`artifacts/examples/math/finite-cardinality-v0/`;
the first finite-field core curriculum pack lives under
`artifacts/examples/math/finite-fields-v0/`;
the first fixed-degree polynomial core curriculum pack lives under
`artifacts/examples/math/polynomial-identities-v0/`;
the first finite-counting core curriculum pack lives under
`artifacts/examples/math/counting-v0/`;
the first finite-group core-structure pack lives under
`artifacts/examples/math/finite-groups-v0/`;
the first finite-ring core-structure pack lives under
`artifacts/examples/math/finite-rings-v0/`;
the first exact-rational pack lives under `artifacts/examples/math/rationals-lra-v0/`;
the first algebraic real/RCF-shadow pack lives under
`artifacts/examples/math/reals-rcf-shadow-v0/`;
the first bounded sequence/limit shadow pack lives under
`artifacts/examples/math/sequence-limit-shadow-v0/`;
the first calculus algebraic-shadow pack lives under
`artifacts/examples/math/calculus-algebraic-shadow-v0/`;
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

Status: core pack expansion is ongoing. `finite-sets-v0` validates the `sets`
curriculum node with finite universe membership, subset transitivity,
union/intersection identity replay, and a bounded rejection of a malformed fixed
set identity. `relations-functions-v0` now validates the next set-theory
dependency with finite relation properties, bijective function-table replay, and
a checked rejection of a multi-valued graph. `finite-fields-v0` now validates
prime-field inverse replay, exhaustive distributivity over a fixed prime field,
and a checked composite-modulus non-field contrast. `polynomial-identities-v0`
now validates exact coefficient identity replay, a factor-theorem root witness,
and a checked false rational-root rejection. `counting-v0` now validates fixed
permutation and binomial counts plus an exhaustive `3 -> 2` pigeonhole
refutation. The recommended Phase M3 pack list has landed. `finite-groups-v0`
now validates finite Cayley-table group axioms, inverse-table replay, and a
checked non-group operation. `finite-rings-v0` now validates finite ring tables,
zero-divisor replay, and a checked non-distributive table. `gcd-bezout-v0` now
validates gcd/common-divisor replay, Bezout coefficient replay, direct
divisibility witnesses, and a checked linear Diophantine gcd obstruction.
`number-theory-v0` now validates bounded CRT compatibility, quadratic-residue
replay, checked nonresidue enumeration, sum-of-two-squares replay, checked
mod-4 two-squares obstruction, and bounded Diophantine replay. `integer-lia-v0`
now validates signed trichotomy, order transitivity, integer ring-identity
replay, linear equation witnesses, checked interval infeasibility, and a fixed
GCD-test Diophantine obstruction. `natural-arithmetic-v0` now validates
bounded successor/addition replay, addition commutativity, multiplication
distributivity, successor injectivity by bounded enumeration, zero-not-successor,
and nonnegative-domain checks. `finite-cardinality-v0` now validates finite
bijection replay, proper-subset injection replay, exhaustive no-injection and
no-surjection rows, and a Cantor-diagonal theorem target that stays
Lean-horizon. `induction-obligations-v0` now validates exact prefix-sum
base-case replay, bounded step-obligation enumeration, bounded conclusion
checking, a bad-step counterexample witness, and a full-schema Lean-horizon
row. `logic-basics-v0` now validates SAT witness replay, tautology and
contradiction truth-table checks, De Morgan equivalence, and a tiny CNF
refutation by enumeration. `finite-predicate-v0` now validates finite-domain
universal/existential predicate replay, an exhaustive non-empty finite
`forall -> exists` row, an `exists`-not-`forall` counterexample, binary
relation asymmetry replay, and a general first-order Lean-horizon row.
`reals-rcf-shadow-v0` now validates exact ordered-field midpoint replay,
nonlinear real product replay, a quadratic real-root witness, checked
`x^2 < 0` infeasibility, checked negative-discriminant no-root infeasibility,
and a completeness/epsilon-delta Lean-horizon row. `sequence-limit-shadow-v0`
now validates finite epsilon-tail replay, finite limit-counterexample replay,
monotone bounded prefix replay, a fixed geometric partial-sum identity, a
bounded Cauchy-tail no-counterexample row, and a general convergence
Lean-horizon row. `calculus-algebraic-shadow-v0` now validates polynomial
derivative coefficient replay, a checked product-rule polynomial identity,
tangent-line replay, convex quadratic critical-point replay, false derivative
rejection, and a general calculus Lean-horizon row. `proof-methods-refutation-v0`
now validates the `PHP(2,2)` control witness and the `PHP(3,2)` refutation by
deterministic CNF truth-table enumeration; LRAT/DRAT proof objects remain its
graduation route, not a pack-level proof gap.

Recommended order:

1. `proof-methods-refutation-v0` (landed): negation-as-query, pigeonhole,
   checked finite CNF refutation; LRAT/DRAT remains the stronger proof-object
   graduation route.
2. `finite-sets-v0` (landed) and `relations-functions-v0` (landed): finite set
   identities, relation properties, function properties.
3. `gcd-bezout-v0` (landed): gcd, Bezout, divisibility, and fixed
   Diophantine obstruction checks.
4. `modular-arithmetic-v0`: CRT, modular inverse, residue witness checks.
5. `finite-fields-v0` (landed): prime-field axioms and composite-modulus
   counterexample.
6. `rationals-lra-v0`: density/trichotomy and exact rational LRA certificates.
7. `linear-algebra-rational-v0`: fixed matrices, LU replay, inconsistent
   system with Farkas evidence where available.
8. `polynomial-identities-v0` (landed): factor theorem and fixed-degree
   identities.
9. `counting-v0` (landed): combinations, pigeonhole, finite counting witnesses.
10. `number-theory-v0` (landed): CRT compatibility, quadratic residues,
    sum-of-two-squares, and bounded Diophantine checks.
11. `integer-lia-v0` (landed): signed order facts, linear equations,
    interval infeasibility, and GCD-test refutations.
12. `natural-arithmetic-v0` (landed): bounded successor/addition replay,
    commutativity, distributivity, and Peano-style bounded no-counterexamples.
13. `finite-cardinality-v0` (landed): finite bijections, finite cardinal
    inequalities, injection/surjection refutations, and infinite-cardinality
    Lean-horizon metadata.
14. `induction-obligations-v0` (landed): bounded base/step obligations,
    bounded conclusion checking, bad-step witnesses, and full-schema
    Lean-horizon metadata.
15. `logic-basics-v0` (landed): SAT witness replay, tautology and
    contradiction checks, De Morgan equivalence, and tiny CNF refutation.
16. `finite-predicate-v0` (landed): finite-domain quantifier expansion,
    universal/existential predicate replay, finite relation counterexamples,
    and general first-order Lean-horizon metadata.
17. `reals-rcf-shadow-v0` (landed): exact ordered-field replay, small
    nonlinear polynomial constraints, checked quadratic infeasibility rows,
    and real-completeness Lean-horizon metadata.
18. `sequence-limit-shadow-v0` (landed): bounded epsilon-tail replay, finite
    counterexamples, monotone bounded prefixes, fixed geometric partial sums,
    and general convergence Lean-horizon metadata.
19. `calculus-algebraic-shadow-v0` (landed): polynomial derivative replay,
    product-rule identity checks, tangent-line replay, critical-point checks,
    and analytic calculus Lean-horizon metadata.

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
`artifacts/examples/math/graph-reachability-v0/` now validates finite BFS
shortest-distance replay, deterministic DFS traversal replay, disconnected
no-path refutation, and edge-cut separation replay.
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
`artifacts/examples/math/finite-operator-v0/` now validates exact
finite-dimensional norm, matrix-operator, and Chebyshev recurrence checks.
`artifacts/examples/math/complex-algebraic-v0/` now validates exact complex
arithmetic, conjugate/norm replay, and a fixed polynomial-root witness using
real-pair algebra.

Recommended order:

1. `graph-coloring-v0` (landed) and `graph-reachability-v0` (landed): SAT
   colorings, non-colorability, finite reachability, traversal traces, and
   cut separation.
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

Status: learner-path scaffold, first walkthrough layer, and first end-to-end
lesson landed.
`docs/learn/math/README.md` now indexes the nine required concept clusters, and
each cluster page links concept rows, validated example packs, current
checkable slices, proof/numerical horizons, and a concrete encode/check
walkthrough using validated pack data. The end-to-end lessons now trace graph
coloring, rational midpoint replay, linear-system/LP replay, finite conditional
probability, finite topology/measure, and bounded dynamics/operators from data
row through replay result and proof/evidence status.

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

Status: active, with the first two integration increments landed. The Boolean
CNF DRAT/LRAT recipe now exists in the Proof Certificate Cookbook and is linked
from the graph coloring and proof-by-refutation example packs. The
proof-by-refutation pack now uses a checked finite CNF truth-table route for
its small pigeonhole UNSAT claim, while this recipe remains the route for
stronger proof-object evidence. A second pass added shared finite-model replay,
QF_LIA Diophantine, and Lean-horizon recipes, then linked the non-template math
example packs to their current evidence route or graduation target.

Deliverables:

- Proof recipe links from each example pack.
- New cookbook recipes where the resource plan exposes repeated gaps.

Priority recipes:

1. CNF/LRAT for pigeonhole and graph coloring. Status: landed as
   [Boolean CNF DRAT/LRAT Evidence](../proof-cookbook/recipes/boolean-cnf-lrat.md).
2. LRA/Farkas for rational inequalities and inconsistent systems. Status:
   landed as [QF_LRA Farkas Evidence](../proof-cookbook/recipes/qf-lra-farkas.md)
   and linked from rational/linear packs.
3. Finite-function/EUF congruence for relation/function packs. Status: base
   recipe landed as
   [QF_UF Congruence And Alethe Evidence](../proof-cookbook/recipes/qf-uf-congruence-alethe.md);
   `relations-functions-v0` now links it as the graduation route beyond finite
   table replay.
4. Bounded arithmetic/Diophantine route for number-theory packs. Status:
   landed as [QF_LIA Diophantine Evidence](../proof-cookbook/recipes/qf-lia-diophantine.md)
   and linked from `modular-arithmetic-v0` as the graduation route beyond finite
   replay.
5. "Lean horizon" recipe template for induction, topology, measure, and limits.
   Status: landed as
   [Lean Horizon Template](../proof-cookbook/recipes/lean-horizon-template.md)
   and linked from field-extension packs with infinite-theorem horizons.
6. Finite model replay route for SAT witnesses and bounded finite examples.
   Status: landed as
   [Finite Model Replay Evidence](../proof-cookbook/recipes/finite-model-replay.md)
   and linked from all current non-template math example packs.

Exit criteria:

- Every UNSAT example has either a checked route or a cookbook gap.
- The proof-gap dashboard is generated from pack metadata.
- At least one lesson shows the trusted-small-checking loop end to end.

### Phase M7: Generated Dashboards And CI Hook

Status: first dashboard and check-hook increments landed. The proof-gap
dashboard is still generated from the concept atlas, and now also reads math
example-pack metadata and `expected.json` rows to report pack-level route
coverage, validation commands, checked/replay/proof-gap counts, and the concrete
checks that still need stronger evidence. `just foundational-resources` and the
plain-shell fallback now validate the concept atlas, validate all math example
packs, regenerate dashboards, and fail if generated dashboard files are stale;
CI runs the same gate before docs link checking.

Deliverables:

- `docs/foundational-resources/generated/math-coverage.md`.
- `docs/foundational-resources/generated/math-field-dashboard.md`.
- `docs/foundational-resources/generated/proof-gap-dashboard.md`.
- Optional `just check-foundational-resources` target once scripts stabilize.

Exit criteria:

- Dashboards are deterministic.
- Validators run in the normal docs/check workflow or have a documented command.
  Status: landed through `just foundational-resources`,
  `scripts/check-foundational-resources.sh`, `just check`, `scripts/check.sh`,
  and the CI docs-resources/docs-links job.
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
5. Add `proof-methods-refutation-v0` with pigeonhole metadata, witness replay,
   and checked finite CNF refutation.
6. Add `modular-arithmetic-v0` from the curriculum backlog.
7. Add `rationals-lra-v0` with density/trichotomy checks.
8. Add `linear-algebra-rational-v0` with LU and inconsistent-system examples.
9. Add `graph-coloring-v0` as the first pure field-extension pack.
10. Add `finite-probability-v0` and `descriptive-statistics-v0` as the
    probability/statistics bridge.

Each commit should update `STATUS.md`, run the relevant validator, and keep the
docs link checker clean.

Progress: items 1-10, Phase M3 `finite-sets-v0`,
`relations-functions-v0`, `finite-fields-v0`,
`polynomial-identities-v0`, `counting-v0`, `gcd-bezout-v0`,
`number-theory-v0`, `integer-lia-v0`, `natural-arithmetic-v0`, and
`finite-cardinality-v0`, `induction-obligations-v0`, and `logic-basics-v0`,
Phase M4 items 4-10, and the Phase M5 learner-path scaffold plus first
encode/check walkthrough layer have landed for the math seed. End-to-end
lessons now exist for graph coloring, graph reachability/traversal, rational
arithmetic, linear algebra/optimization, probability/statistics, finite
structures, and analysis/topology horizons. Phase M6 now has cookbook links
from all current non-template math example packs, and
`proof-methods-refutation-v0` has a checked finite CNF truth-table route for its
pigeonhole refutation. Phase M7 now has generated pack-level proof-gap rows and
a normal foundational-resource check hook. Continue by adding the next graph
slice (matching, cuts beyond single-edge witnesses, or d-separation), by adding
the next curriculum-adjacent pack, or by replacing finite enumeration routes
with emitted, checked proof objects where appropriate.

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
