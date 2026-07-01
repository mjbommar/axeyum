# Math Curriculum Resource Buildout Plan

## Objective

Build the sibling-resource ecosystem outward from the existing
[formal mathematics curriculum](../curriculum/README.md). The curriculum DAG in
[`docs/curriculum/curriculum.toml`](../curriculum/curriculum.toml) is the seed:
every concept row, example pack, learner page, proof route, and dashboard entry
should trace back to either a curriculum node or an explicit extension field in
the [University Math Field Taxonomy](MATH-FIELDS.md).

For the current forward work plan, use the
[Curriculum Resource Execution Plan](CURRICULUM-RESOURCE-EXECUTION-PLAN.md).
For the owner-facing plan across every curriculum-based resource family
(education pages, ontology rows, example packs, proof artifacts, solver
feedback, rules/law transfer, consumer boundaries, and future libraries), use
the [Math Curriculum Comprehensive Resource Plan](MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md).
For the top-down curriculum-wide plan across layers, fields, proof routes,
solver reuse, and consumer boundaries, use the
[Math Curriculum Resource Master Plan](MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md).
For the practical curriculum-to-resource build sequence across educational
content, ontology rows, example packs, proof artifacts, solver feedback,
rules/law transfer, and future library boundaries, use the
[Math Curriculum Resource Build Sequence](MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md).
For commit-sized work selection across curriculum nodes, math fields, resource
gates, and proof routes, use the
[Math Curriculum Implementation Matrix](MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md).
For the current execution ledger over the existing math packs, unclassified
solver-reuse rows, learner-path work, proof-route depth, and field-by-field
next steps, use the
[Math Curriculum Detailed Build Plan](MATH-CURRICULUM-DETAILED-BUILD-PLAN.md).
For the current learner-spine audit over all non-template math packs, use the
[Learner Coverage Audit](LEARNER-COVERAGE-AUDIT.md).
For the detailed operating plan that expands the curriculum into ontology rows,
example packs, learner pages, proof routes, solver reuse, consumer boundaries,
rules/law transfer, and future library splits, use the
[Math Curriculum Resource Buildout Roadmap](RESOURCE-BUILDOUT-ROADMAP.md).
For the concrete rules/law transfer map from math-resource patterns into
policy and legal-rule checks, use the
[Rules/Law Crosswalk](RULES-LAW-CROSSWALK.md).
For copyable queries over the current rules-as-code JSON boundary, use the
[Rules/Law Resource Queries](RULES-LAW-QUERIES.md).
For the current map from reusable rules/law patterns to math concepts, proof
routes, rule packs, and query commands, use the
[Rules/Law Pattern Matrix](RULES-LAW-PATTERN-MATRIX.md).
For the learner-facing walkthrough from rule text to formal model, replayed
witness, checked obligation, and legal/theorem horizon, use
[Rules/Law Trust Boundary](../learn/rules-law-trust-boundary.md).
For the compact all-field consumer query surface, use the
[Field Readiness Query Matrix](FIELD-READINESS-QUERY-MATRIX.md).
For proof-route coverage queries, use the
[Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md).
For the compact execution selector that picks one replay-heavy family per proof
route and states when another negative row should be promoted, use the
[Proof Route Family Selection](PROOF-ROUTE-FAMILY-SELECTION.md).
For reusable learner-facing trust-boundary snippets across the checked proof
routes, use
[Proof Route Learner Snippets](../learn/math/proof-route-learner-snippets.md).
For matrix computation discovery by bridge concept and proof route, use the
[Matrix Computation Consumer Queries](MATRIX-COMPUTATION-QUERIES.md).
For probability/statistics discovery by bridge concept and proof route, use the
[Probability And Statistics Resource Consumer Queries](PROBABILITY-STATISTICS-QUERIES.md).
For finite measure discovery by bridge concept and proof route, use the
[Measure Theory Resource Consumer Queries](MEASURE-THEORY-QUERIES.md).
For topology/homology discovery by bridge concept and proof route, use the
[Topology And Homology Resource Consumer Queries](TOPOLOGY-HOMOLOGY-QUERIES.md).
For finite algebra discovery by bridge concept and proof route, use the
[Algebra Structure Consumer Queries](ALGEBRA-STRUCTURE-QUERIES.md).
For number/arithmetic discovery by bridge concept and proof route, use the
[Number And Arithmetic Resource Consumer Queries](NUMBER-ARITHMETIC-QUERIES.md).
For finite geometry discovery by bridge concept and proof route, use the
[Geometry Resource Consumer Queries](GEOMETRY-RESOURCE-QUERIES.md).
For graph/discrete discovery by bridge concept and proof route, use the
[Graph And Discrete Resource Consumer Queries](GRAPH-DISCRETE-QUERIES.md).
For optimization/convexity discovery by bridge concept and proof route, use the
[Optimization And Convexity Resource Consumer Queries](OPTIMIZATION-CONVEXITY-QUERIES.md).
For functional-analysis/operator discovery by bridge concept and proof route,
use the
[Functional Analysis And Operator Resource Consumer Queries](FUNCTIONAL-OPERATOR-QUERIES.md).
For real-analysis, numerical-analysis, and complex-analysis discovery by bridge
concept and proof route, use the
[Analysis And Numerical Resource Consumer Queries](ANALYSIS-NUMERICAL-QUERIES.md).
For differential-equations/dynamical-systems discovery by bridge concept and
proof route, use the
[Dynamics Resource Consumer Queries](DYNAMICS-QUERIES.md).
For logic/proof, set-foundations, and discrete-math discovery by bridge concept
and proof route, use the
[Foundations And Discrete Resource Consumer Queries](FOUNDATIONS-DISCRETE-QUERIES.md).
This file remains the phase contract and landed-history log.

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
    curriculum-status-audit.md
    math-field-dashboard.md
    proof-gap-dashboard.md
    learner-proof-upgrade-dashboard.md
    curriculum-pressure-by-fragment.md
    solver-reuse-disposition-audit.md

docs/learn/math/
  README.md
  <lesson>.md

scripts/
  validate-foundational-concepts.py
  validate-foundational-example-pack.py
  gen-foundational-dashboards.py
  consume-foundational-resources.py
  query-foundational-resources.py
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
- optional pack-level `solver_reuse`: candidate/promoted/non-benchmark-horizon
  status, solver pressure, evidence rows, and the next promotion step.

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
  validator command, optional solver-reuse candidate metadata;
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
- audit of source curriculum status versus generated resource maturity;
- coverage by math field;
- coverage by decidability class;
- coverage by proof/evidence route;
- list of example packs with validation commands;
- proof gaps grouped by solver fragment and field.
- overlapping curriculum pressure by solver/proof fragment.
- solver-reuse disposition totals and unclassified-pack queue.

Dashboards should be regenerated, not edited by hand.

## Curriculum Node Mapping

This table is the first expansion contract. Every curriculum node gets an atlas
row and a pack target, even if the initial pack is only proof-horizon metadata.

| Curriculum Node | Field IDs | First Resource Target | First Checkable Slice |
|---|---|---|---|
| `propositional-logic` | `logic_and_proof` | `logic-basics-v0` | SAT/UNSAT Boolean formulas, truth tables, CNF refutations. |
| `predicate-logic` | `logic_and_proof`, `set_theory_and_foundations` | `finite-predicate-v0` | Finite-domain quantifier expansion and counterexamples. |
| `proof-methods` | `logic_and_proof` | `proof-methods-refutation-v0`, `proof-methods-patterns-v0` | Negate-and-decide examples, direct proof, contrapositive, proof by cases, contradiction, and invalid-proof counterexamples. |
| `induction` | `logic_and_proof`, `number_theory` | `induction-obligations-v0`, `induction-patterns-v0` | Bounded base/step obligations, weak/strong induction prefixes, loop invariants, bad-step counterexamples; general induction marked Lean-horizon. |
| `sets` | `set_theory_and_foundations` | `finite-sets-v0`, `finite-order-lattices-v0` | Membership, subset, union/intersection, finite identities, finite Boolean lattices, and order-theoretic set structure. |
| `relations-and-functions` | `set_theory_and_foundations`, `discrete_math` | `relations-functions-v0`, `equivalence-classes-v0`, `function-composition-v0`, `finite-monoids-v0`, `finite-permutation-groups-v0`, `finite-group-actions-v0`, `finite-order-lattices-v0` | Finite relation properties, partial orders, lattices, monotone maps, injective/surjective checks, function composition, closed transformation monoids, permutation groups as bijective function tables, group actions as function tables, image/preimage, inverse tables, equivalence classes, quotient maps, and EUF slices. |
| `cardinality` | `set_theory_and_foundations`, `discrete_math` | `finite-cardinality-v0`, `cardinality-principles-v0`, `finite-order-lattices-v0` | Finite bijections/counting, inclusion-exclusion, disjoint unions, double counting, powersets, finite Boolean lattices, checked QF_LIA overlap-additivity conflict; infinite cardinality marked Lean-horizon. |
| `naturals` | `number_theory`, `discrete_math` | `natural-arithmetic-v0` | Bounded Peano arithmetic and LIA/BV arithmetic identities. |
| `integers` | `number_theory` | `integer-lia-v0` | Linear integer equations/inequalities and witnesses. |
| `rationals` | `real_analysis`, `linear_algebra` | `rationals-lra-v0`, `polynomial-factorization-rational-v0` | Exact rational order/field facts, density, trichotomy, Farkas links, rational polynomial division, GCD, factorization replay, and a QF_LRA discriminant conflict. |
| `reals` | `real_analysis`, `optimization_and_convexity` | `real-analysis-rational-v0`, `reals-rcf-shadow-v0`, `multivariable-calculus-rational-v0`, `finite-root-finding-v0`, `finite-separation-v0`, `finite-kkt-v0`, `finite-active-set-qp-v0`, `finite-sdp-v0`, `finite-gradient-descent-v0`, `finite-line-search-v0`, `finite-wolfe-line-search-v0`, `finite-projected-gradient-v0`, `finite-proximal-gradient-v0`, `finite-circle-geometry-v0`, `finite-inversion-geometry-v0`, `finite-cyclic-geometry-v0` | Bounded rational neighborhoods, algebraic real constraints through LRA/NRA, checked QF_LRA negative-discriminant shadow, exact rational gradients, Hessian checks, finite root-finding iteration replay, finite separating-hyperplane replay, finite KKT stationarity/complementarity replay, finite active-set QP face/slack replay with checked inactive-slack evidence, finite SDP objective/slack/gap replay, finite gradient-descent step replay, finite Armijo line-search replay, finite Wolfe sufficient-decrease/curvature replay, finite projected-gradient interval/decrease replay, finite proximal-gradient soft-threshold/composite-decrease and box-plus-L1 replay, finite circle point/tangent/chord/line replay, finite inversion replay, finite cyclic quadrilateral replay, and rational Ptolemy replay; completeness, separation theorems, KKT sufficiency, active-set method theory, SDP duality, descent-rate, Wolfe/line-search/projected/proximal-gradient convergence, circle/inversion/cyclic-geometry theorems, and convergence marked horizon. |
| `complex` | `complex_analysis`, `linear_algebra` | `complex-algebraic-v0`, `complex-plane-transforms-v0` | Complex arithmetic, unit-root cycles, conjugation, rational transforms, and checked false real-pair claims as algebraic constraints. |
| `divisibility-and-euclid` | `number_theory` | `gcd-bezout-v0` | GCD, Bezout witness replay, divisibility checks. |
| `modular-arithmetic` | `number_theory`, `abstract_algebra` | `modular-arithmetic-v0`, `finite-ideals-v0` | Congruences, inverses, CRT, fixed-modulus enumeration, checked QF_LIA nonunit and incompatible-CRT Diophantine obstructions, checked fixed-width QF_BV/DRAT nonunit-inverse and modulo-5 Fermat-unit searches, modular ring ideals, and quotient rings. |
| `groups` | `abstract_algebra` | `finite-groups-v0`, `finite-algebra-homomorphisms-v0`, `finite-monoids-v0`, `finite-permutation-groups-v0`, `finite-group-actions-v0`, `finite-vector-spaces-v0`, `finite-dual-spaces-v0`, `finite-modules-v0`, `finite-tensor-products-v0` | Cayley-table closure, identity, inverse, associativity, homomorphism, kernel/image, quotient, finite monoids, units/idempotents, finite permutation groups, cycle/sign replay, finite group actions, orbit/stabilizer replay, Burnside counting, vector-addition groups, dual-space additive groups, module-addition groups, finite tensor-product additive groups, and induced-map checks. |
| `rings` | `abstract_algebra` | `finite-rings-v0`, `finite-algebra-homomorphisms-v0`, `finite-modules-v0`, `finite-ideals-v0` | Two-operation table checks, distributivity, multiplicative identity, zero divisors, ring-homomorphism preservation, ideals, quotient rings, and finite module actions over rings. |
| `fields` | `abstract_algebra`, `number_theory` | `finite-fields-v0`, `finite-vector-spaces-v0`, `finite-dual-spaces-v0`, `finite-tensor-products-v0`, `polynomial-factorization-rational-v0` | Field axioms over small prime fields, composite modulus counterexamples, finite vector spaces over `F2`, covectors and dual bases, bilinear maps, tensor-product replay, and rational polynomial arithmetic over `Q[x]`. |
| `polynomials` | `abstract_algebra`, `real_analysis`, `complex_analysis` | `polynomial-identities-v0`, `polynomial-factorization-rational-v0`, `generating-functions-v0`, `finite-root-finding-v0`, `finite-circle-geometry-v0`, `finite-inversion-geometry-v0`, `finite-cyclic-geometry-v0` | Fixed-degree identities, factor theorem, root witness replay, rational factor products, polynomial division, Euclidean GCD, square-free decomposition, irreducible-quadratic rejection with QF_LRA/Farkas evidence, coefficient extraction, finite convolution, exact polynomial evaluation inside bisection/Newton steps, finite circle equations/tangent/chord/line intersections, finite inversion image/distance-product replay, finite cyclic-configuration replay, and rational Ptolemy product-sum replay. |
| `sequences-and-limits` | `real_analysis`, `topology` | `sequence-limit-shadow-v0`, `bounded-monotone-sequence-v0`, `finite-recurrence-prefix-v0`, `real-analysis-rational-v0`, `generating-functions-v0` | Bounded epsilon/N and epsilon-delta templates, algebraic sequence checks, finite monotone-prefix/supremum/tail-gap replay, finite recurrence-prefix and companion-matrix replay, and finite generating-function prefixes; general limits marked Lean-horizon. |
| `counting` | `discrete_math`, `probability_theory` | `counting-v0`, `finite-permutation-groups-v0`, `finite-group-actions-v0`, `finite-recurrence-prefix-v0`, `generating-functions-v0` | Permutations, combinations, pigeonhole finite instances, finite cycle/sign replay, finite orbit counting, Burnside fixed-point averages, recurrence-prefix replay, coefficient extraction, and Cauchy-product counting prefixes. |
| `number-theory` | `number_theory` | `number-theory-v0` | CRT, quadratic residues, sum of squares, bounded Diophantine witnesses and gcd obstructions. |
| `linear-algebra` | `linear_algebra`, `numerical_analysis`, `optimization_and_convexity` | `linear-algebra-rational-v0`, `finite-vector-spaces-v0`, `finite-dual-spaces-v0`, `inner-product-spaces-rational-v0`, `finite-modules-v0`, `finite-tensor-products-v0`, `multivariable-calculus-rational-v0`, `finite-separation-v0`, `finite-kkt-v0`, `finite-active-set-qp-v0`, `finite-sdp-v0`, `finite-gradient-descent-v0`, `finite-line-search-v0`, `finite-wolfe-line-search-v0`, `finite-projected-gradient-v0`, `finite-proximal-gradient-v0`, `finite-circle-geometry-v0`, `finite-inversion-geometry-v0`, `finite-cyclic-geometry-v0` | Fixed rational matrices, finite vector spaces and modules, finite dual spaces, covectors, annihilators, transpose maps, exact rational inner products, Gram matrices, projections, Gram-Schmidt replay, finite tensor products, bilinear maps, LU replay with checked bad product-entry evidence, nullspace replay with checked bad component evidence, inverse checks, inconsistent systems, subspaces, linear maps, quotient modules, rank-nullity replay, Jacobians, Hessians, exact separating-hyperplane dot-product replay, finite KKT stationarity/complementarity replay, finite active-face stationarity and checked inactive-slack replay, finite SDP PSD/slack/objective/gap replay, finite gradient-descent matrix-step replay, finite Armijo/Wolfe line-search replay, finite projected-gradient interval/decrease replay, finite proximal-gradient soft-threshold/composite-decrease and box-plus-L1 replay, finite circle tangent/chord/line replay, finite inversion scalar-vector/determinant replay, and finite cyclic diagonal/angle/Ptolemy product-sum replay. |
| `calculus` | `real_analysis`, `differential_equations_and_dynamical_systems`, `numerical_analysis` | `calculus-algebraic-shadow-v0`, `calculus-riemann-sum-v0`, `multivariable-calculus-rational-v0`, `real-analysis-rational-v0`, `finite-root-finding-v0`, `finite-kkt-v0`, `finite-active-set-qp-v0`, `finite-gradient-descent-v0`, `finite-line-search-v0`, `finite-wolfe-line-search-v0`, `finite-projected-gradient-v0`, `finite-proximal-gradient-v0` | Polynomial derivative identities, exact rational gradients/Jacobians/Hessians, finite Riemann sums, antiderivative endpoint replay, bounded epsilon-delta shadows, finite root-finding iteration replay, finite KKT stationarity/complementarity replay, finite active-set free-gradient and inactive-slack replay, finite gradient-descent step replay, finite Armijo/Wolfe line-search replay, finite projected-gradient interval/decrease replay, finite proximal-gradient soft-threshold/composite-decrease and box-plus-L1 replay, and algebraic inequalities; general integration, KKT sufficiency, active-set method theory, descent-rate, Wolfe/line-search/projected/proximal-gradient convergence, and convergence marked Lean-horizon. |

## Field Extensions Beyond The Current Curriculum

These rows widen the existing DAG into the 18-field university taxonomy without
losing the curriculum anchor.

| Field | Curriculum Anchor | First New Resource |
|---|---|---|
| `graph_theory` | sets, relations, counting | `graph-coloring-v0`, then reachability, search runtime/cost counters, matching, cuts, and d-separation. |
| `topology` | sets, reals, sequences-and-limits, linear algebra | `finite-topology-v0`, `finite-specialization-order-v0`, `finite-simplicial-homology-v0`, then metric balls, closure/interior, specialization preorder replay, checked finite axiom conflicts, continuous maps, compactness, connectedness, and finite chain-complex checks. |
| `measure_theory` | sets, rationals, probability | `finite-measure-v0`, `finite-measure-monotonicity-v0`, `finite-integration-v0`, `finite-product-measure-v0`, `finite-random-variables-v0`, `finite-conditional-expectation-v0`, `finite-stochastic-kernels-v0`, `finite-martingales-v0`, `finite-hitting-times-v0`, and `finite-concentration-v0` over finite universes; Lebesgue and convergence theory remain horizon. |
| `probability_theory` | counting, rationals, finite sets | `finite-probability-v0`, Bayes tables, finite expectations, finite random variables, finite conditional expectation, finite stochastic kernels, finite martingales, finite hitting times, finite concentration/tail bounds, product tables, exact discrete distributions, finite random-matrix moment tables, and the random-matrix moment learner-query index. |
| `statistics` | probability, rationals, linear algebra | `descriptive-statistics-v0`, `least-squares-regression-v0`, contingency tables, exact small tests, least-squares normal equations, finite stochastic-kernel checks, finite hitting-time checks, finite martingale checks, finite concentration checks, and finite random-matrix moment checks. |
| `optimization_and_convexity` | rationals, reals, linear algebra | `linear-optimization-v0`, `convexity-rational-v0`, `multivariable-calculus-rational-v0`, `finite-separation-v0`, `finite-kkt-v0`, `finite-active-set-qp-v0`, `finite-sdp-v0`, `finite-gradient-descent-v0`, `finite-line-search-v0`, `finite-wolfe-line-search-v0`, `finite-projected-gradient-v0`, `finite-proximal-gradient-v0`, LP feasibility, dual/Farkas certificates, finite convexity, gradients, Hessian checks, threshold checks, KKT stationarity/complementarity witnesses, active-set QP witnesses including inactive-slack conflicts, SDP primal/dual slack/gap replay, finite descent-step checks, finite Armijo/Wolfe line-search replay, finite projected-gradient interval/decrease replay, and finite proximal-gradient replay. |
| `numerical_analysis` | linear algebra, real algebra | `numerical-linear-algebra-v0`, `finite-euler-method-v0`, `multivariable-calculus-rational-v0`, LU replay, interval bounds, error recurrences, Jacobian/Hessian replay, and finite ODE step replay. |
| `differential_equations_and_dynamical_systems` | calculus, linear algebra | `bounded-dynamics-v0`, `finite-euler-method-v0`, recurrence traces, Euler-method steps, threshold reachability, finite error replay, and invariant checks before continuous theory. |
| `geometry` | reals, polynomials, linear algebra | `coordinate-geometry-v0`, `incidence-geometry-v0`, `rigid-configuration-geometry-v0`, `affine-geometry-v0`, `orientation-area-geometry-v0`, `finite-circle-geometry-v0`, `finite-inversion-geometry-v0`, `finite-cyclic-geometry-v0`, distance, midpoint, collinearity, line equations, distance tables, affine maps, signed area, barycentric replay, finite incidence preservation, finite isometry shadows, circle points, tangent lines, chord-midpoint perpendicularity, circle-line intersections, inversion images, inverse-distance products, cyclic quadrilateral replay, diagonal intersections, opposite-angle dot products, and rational Ptolemy product sums. |
| `functional_analysis_and_operator_theory` | linear algebra, real analysis | `finite-operator-v0`, `inner-product-spaces-rational-v0`, `finite-chebyshev-systems-v0`, norms, inner products, projections, matrices as operators, Chebyshev polynomial slices, finite interpolation/sign-pattern checks, and the Chebyshev/operator learner-query index. |

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
dashboards covering all 23 curriculum nodes and all 18 math fields. The
generator now reads committed non-template math example-pack metadata and
attaches validated packs to the corresponding field rows, so field dashboards
track current resource coverage instead of only the original starter packs.

Deliverables:

- `artifacts/ontology/foundational-concepts.schema.json`.
- `artifacts/ontology/foundational-concepts.json`.
- `scripts/validate-foundational-concepts.py`.

Implementation notes:

- Seed all 23 curriculum nodes from `curriculum.toml`.
- Add 18 field rows from [MATH-FIELDS.md](MATH-FIELDS.md).
- Merge non-template `artifacts/examples/math/*/metadata.json` field coverage
  into the field rows when regenerating the atlas.
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
the finite induction-pattern pack lives under
`artifacts/examples/math/induction-patterns-v0/`;
the first finite predicate-logic pack lives under
`artifacts/examples/math/finite-predicate-v0/`;
the first replay-checked, QF_LIA/Diophantine-promoted, and QF_BV/DRAT-promoted
modular number-theory pack lives under
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
the first finite order/lattice pack lives under
`artifacts/examples/math/finite-order-lattices-v0/`;
the first finite-cardinality foundations pack lives under
`artifacts/examples/math/finite-cardinality-v0/`;
the first finite-field core curriculum pack lives under
`artifacts/examples/math/finite-fields-v0/`;
the first fixed-degree polynomial core curriculum pack lives under
`artifacts/examples/math/polynomial-identities-v0/`;
the first exact rational polynomial-factorization pack lives under
`artifacts/examples/math/polynomial-factorization-rational-v0/`;
the first finite-counting core curriculum pack lives under
`artifacts/examples/math/counting-v0/`;
the first finite-group core-structure pack lives under
`artifacts/examples/math/finite-groups-v0/`;
the first finite group-action pack lives under
`artifacts/examples/math/finite-group-actions-v0/`;
the first finite monoid pack lives under
`artifacts/examples/math/finite-monoids-v0/`;
the first finite permutation-group pack lives under
`artifacts/examples/math/finite-permutation-groups-v0/`;
the first finite-ring core-structure pack lives under
`artifacts/examples/math/finite-rings-v0/`;
the first finite algebra homomorphism pack lives under
`artifacts/examples/math/finite-algebra-homomorphisms-v0/`;
the first finite ideal and quotient-ring pack lives under
`artifacts/examples/math/finite-ideals-v0/`;
the first finite vector-space pack lives under
`artifacts/examples/math/finite-vector-spaces-v0/`;
the first finite dual-space pack lives under
`artifacts/examples/math/finite-dual-spaces-v0/`;
the first finite module pack lives under
`artifacts/examples/math/finite-modules-v0/`;
the first exact-rational pack lives under `artifacts/examples/math/rationals-lra-v0/`;
the first algebraic real/RCF-shadow pack lives under
`artifacts/examples/math/reals-rcf-shadow-v0/`;
the first bounded rational real-analysis pack lives under
`artifacts/examples/math/real-analysis-rational-v0/`;
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
a checked rejection of a multi-valued graph plus a QF_UF/Alethe
function-consistency proof row. `equivalence-classes-v0` now
deepens that node with finite equivalence classes, quotient-map fibers,
partition-to-relation round trips, checked rejection of a non-transitive
relation, and a resource-backed QF_UF/Alethe quotient-map congruence proof row.
`function-composition-v0` now validates finite composition tables,
image/preimage replay, inverse tables for bijections, composition
associativity, non-injective inverse counterexamples, a QF_UF/Alethe
composition-application proof row, and a general function-law Lean-horizon row.
`finite-order-lattices-v0` now deepens the
finite relation path with Boolean-lattice partial-order replay, meet/join
table replay, distributivity checks, monotone-map fixed-point replay, checked
QF_UF/Alethe bad-order rejection, checked Bool/CNF bad top-element rejection,
and a general order/lattice Lean-horizon row.
`finite-fields-v0` now
validates prime-field inverse replay, exhaustive distributivity over a fixed
prime field, a checked composite-modulus non-field contrast, a checked bad
prime-field inverse candidate, and resource-backed QF_BV/DRAT proof-route rows
for both fixed-width conflicts.
`polynomial-identities-v0`
now validates exact coefficient identity replay, a factor-theorem root witness,
and a checked false rational-root rejection. `counting-v0` now validates fixed
permutation and binomial counts plus an exhaustive `3 -> 2` pigeonhole
refutation. `polynomial-factorization-rational-v0` now validates exact
rational factor-list product replay, polynomial division, Euclidean GCD replay,
square-free decomposition, checked irreducible-quadratic rejection, a
source-linked QF_LRA/Farkas discriminant conflict, and a general
factorization-theory Lean-horizon row. `generating-functions-v0` now
validates finite coefficient
extraction, Cauchy product convolution, Fibonacci generating-function prefix
replay, checked rejection of a bad convolution coefficient, and a
generating-functions Lean-horizon row. The recommended Phase M3 pack list has
landed. `finite-groups-v0`
now validates finite Cayley-table group axioms, inverse-table replay, and a
checked non-group operation plus a QF_UF/Alethe binary-operation congruence row.
`finite-permutation-groups-v0` now validates
`S3` as bijective function tables under composition, cycle/sign replay, natural
action orbit/stabilizer replay, checked QF_UF/Alethe bad-nonbijection
rejection, and a general permutation-group Lean-horizon row. `finite-group-actions-v0` now
validates finite action laws, orbit/stabilizer replay, orbit-stabilizer
cardinality, Burnside fixed-point counting, checked QF_UF/Alethe bad
identity-action and action-compatibility rejections, and a general
group-action Lean-horizon row.
`finite-monoids-v0` now validates finite monoid identity/associativity,
transformation-composition table replay from finite functions,
units/idempotents, a checked QF_UF/Alethe non-associative table rejection, and
a general monoid Lean-horizon row. `finite-rings-v0` now validates finite ring
tables, zero-divisor replay, checked non-distributive and bad
multiplicative-identity tables, and resource-backed QF_BV/DRAT proof-route
rows for both conflicts.
`finite-algebra-homomorphisms-v0` now extends the algebra core with finite
group-homomorphism replay, kernel/image recomputation, quotient and induced-map
checks, ring-homomorphism replay, a QF_UF/Alethe homomorphism-preservation row,
checked bad-homomorphism rejection, a concrete QF_UF/Alethe bad-map
refutation after table replay identifies `phi(1+1)=1` versus
`phi(1)+phi(1)=0`, and a general isomorphism-theorem Lean-horizon row.
`finite-vector-spaces-v0` now
bridges finite fields into linear algebra with `F2^2` vector-space table
replay, subspace/span checks, linear-map kernel/image replay, rank-nullity
replay, checked exact non-subspace replay, an explicit QF_UF/Alethe
additive-closure membership row, and a general vector-space/module
Lean-horizon row. `finite-modules-v0` now adds the finite ring-to-linear-algebra
bridge with `Z/4Z` module table replay, submodule/span replay,
module-homomorphism kernel/image replay, quotient-module table replay,
checked exact non-submodule replay, an explicit QF_UF/Alethe scalar-closure
membership row, and a general module-theory Lean-horizon row.
`finite-dual-spaces-v0` now adds the finite dual-space bridge with `F2^2`
covector linearity replay, pointwise dual operations, dual-basis pairing,
annihilator recomputation, transpose-map replay, checked QF_UF/Alethe
bad-covector rejection, and a general duality/functional-analysis Lean-horizon
row.
`finite-tensor-products-v0` now adds the finite multilinear-algebra bridge:
`F2^2 tensor F2` basis/dimension replay, finite bilinear-map table replay,
universal-factorization shadow through a linear map, Kronecker-product matrix
replay, checked QF_UF/Alethe bad-bilinear-map rejection, and a general
tensor-theory Lean-horizon row.
`finite-ideals-v0` now adds the finite quotient-ring bridge with `Z/6Z`
ideal replay, principal ideal generation, modulo-2 ring-homomorphism
kernel/image replay, quotient-ring table replay, checked QF_UF/Alethe
non-ideal rejection, checked quotient representative congruence, and a general
ideal-theory Lean-horizon row.
`gcd-bezout-v0` now
validates gcd/common-divisor replay, Bezout coefficient replay, direct
divisibility witnesses, and a source-linked checked linear Diophantine gcd
obstruction.
`number-theory-v0` now validates bounded CRT compatibility, quadratic-residue
replay, checked nonresidue enumeration plus QF_BV/DRAT proof-route rows,
sum-of-two-squares replay, checked mod-4 two-squares obstruction, bounded
Diophantine replay, and a checked QF_LIA/Diophantine gcd obstruction.
`integer-lia-v0`
now validates signed trichotomy, order transitivity, integer ring-identity
replay, linear equation witnesses, checked interval infeasibility, and a fixed
GCD-test Diophantine obstruction. `natural-arithmetic-v0` now validates
bounded successor/addition replay, addition commutativity, multiplication
distributivity, successor injectivity by bounded enumeration, zero-not-successor,
and nonnegative-domain checks. `finite-cardinality-v0` now validates finite
bijection replay, proper-subset injection replay, exhaustive no-injection and
no-surjection rows, and a Cantor-diagonal theorem target that stays
Lean-horizon. `cardinality-principles-v0` now validates finite
inclusion-exclusion, disjoint-union additivity, bipartite-edge double
counting, powerset cardinality, checked false disjoint-additivity rejection,
a source-linked QF_LIA/Diophantine overlap-additivity count contradiction, and
an arbitrary-cardinality Lean-horizon row. `induction-obligations-v0` now
validates exact prefix-sum base-case replay, bounded step-obligation
enumeration with a source-linked QF_LIA arithmetic-DPLL bad-step count
regression, bounded conclusion checking, a bad-step counterexample witness,
and a full-schema Lean-horizon row. `induction-patterns-v0` now validates finite weak-induction evenness
prefixes, a checked QF_LIA finite even-product parity obstruction,
strong-induction Fibonacci bounds, loop-invariant trace replay, checked
bad-step rejection, and a full-schema Lean-horizon row.
`logic-basics-v0` now validates SAT witness replay, tautology and
contradiction truth-table checks, De Morgan equivalence, and a tiny CNF
refutation by enumeration. `proof-methods-patterns-v0` now validates finite
direct-proof/modus-ponens replay, contrapositive equivalence, proof by cases,
contradiction refutation, invalid-converse counterexample evidence, and a
natural-deduction Lean-horizon row. `finite-predicate-v0` now validates finite-domain
universal/existential predicate replay, an exhaustive non-empty finite
`forall -> exists` row, an `exists`-not-`forall` counterexample, binary
relation asymmetry replay, and a general first-order Lean-horizon row.
`reals-rcf-shadow-v0` now validates exact ordered-field midpoint replay,
nonlinear real product replay, a quadratic real-root witness, checked
`x^2 < 0` infeasibility, checked negative-discriminant no-root infeasibility,
a source-linked QF_LRA/Farkas negative-discriminant conflict, and a
completeness/epsilon-delta Lean-horizon row. `real-analysis-rational-v0`
now validates exact rational interval/ball inclusion, a bounded linear
epsilon-delta sample, finite squeeze-style polynomial side conditions, checked
QF_LRA/Farkas rejection of a false delta, and a general real-analysis
Lean-horizon row.
`sequence-limit-shadow-v0` now validates finite epsilon-tail replay, finite
limit-counterexample replay, monotone bounded prefix replay, a fixed geometric
partial-sum identity, a bounded Cauchy-tail no-counterexample row, checked
bad reciprocal-tail bound rejection, and a general convergence Lean-horizon
row. `bounded-monotone-sequence-v0` now
validates finite monotone-prefix replay, finite prefix supremum replay, finite
tail-gap replay, checked QF_LRA/Farkas rejection of false upper-bound and
tail-gap rows, and a monotone-convergence Lean-horizon row.
`finite-recurrence-prefix-v0` now
validates Fibonacci prefix replay, affine recurrence replay,
companion-matrix state replay, checked QF_LRA/Farkas rejection of false
finite recurrence-value and affine-step claims, and a recurrence-theory
Lean-horizon row.
`finite-root-finding-v0` now validates one exact bisection step, one exact
Newton step, fixed residual-decrease replay, checked QF_LRA/Farkas rejection
of false Newton-iterate and bisection-width claims, and a root-finding
convergence/stability Lean-horizon row.
`finite-separation-v0` now validates exact convex-combination replay, finite
separating-hyperplane dot-product replay, supporting-face replay, checked
QF_LRA/Farkas rejection of false convex-combination and separator claims, and
a general separation-theorem Lean-horizon row.
`finite-kkt-v0` now validates exact constrained-quadratic grid replay,
stationarity replay, complementary-slackness replay, checked QF_LRA/Farkas
rejection of a false stationarity multiplier and false complementarity product,
and a general KKT-sufficiency Lean-horizon row.
`finite-active-set-qp-v0` now validates exact unconstrained-minimizer replay,
active-face candidate replay, KKT stationarity/complementarity replay,
inactive-constraint slack replay, degenerate active-bound replay, checked
QF_LRA/Farkas rejection of false free-coordinate stationarity, false
inactive-slack, and false degenerate-multiplier claims, and a general
active-set-method Lean-horizon row.
`finite-sdp-v0` now validates exact two-by-two PSD replay, trace/objective
arithmetic, dual-slack matrix replay, zero duality-gap checking, checked
QF_LRA/Farkas rejection of false objective and false duality-gap claims, and a
general SDP-duality Lean-horizon row.
`finite-gradient-descent-v0` now validates exact quadratic gradient replay,
finite descent-step arithmetic, objective-decrease and descent-bound replay,
checked QF_LRA/Farkas rejection of false decrease, false step-coordinate, and
false descent-bound claims, and a general gradient-descent convergence
Lean-horizon row.
`finite-line-search-v0` now validates exact descent-direction replay, Armijo
trial-step rejection, accepted backtracked-step replay, checked QF_LRA/Farkas
rejection of false descent-direction, Armijo acceptance, and
accepted-candidate claims, and a general line-search convergence Lean-horizon
row.
`finite-wolfe-line-search-v0` now validates exact descent-direction replay,
exact line-minimizer replay, Wolfe sufficient-decrease and curvature replay,
checked QF_LRA/Farkas rejection of false line-minimizer and curvature claims,
and a general Wolfe line-search Lean-horizon row.
`finite-projected-gradient-v0` now validates exact derivative replay,
unconstrained-step replay, interval projection, projected-descent replay,
checked QF_LRA/Farkas rejection of false projected-point and projected-decrease
claims, and a general projected-gradient convergence Lean-horizon row.
`finite-proximal-gradient-v0` now validates exact smooth-derivative replay,
ordinary trial-step replay, L1 soft-threshold proximal replay, composite
objective-decrease replay, checked QF_LRA/Farkas rejection of a false proximal
point, and a general proximal-gradient convergence Lean-horizon row.
`calculus-algebraic-shadow-v0` now
validates polynomial derivative coefficient replay, a checked product-rule
polynomial identity, tangent-line replay, convex quadratic critical-point
replay, false derivative rejection, and a general calculus Lean-horizon row.
`calculus-riemann-sum-v0` now validates exact finite Riemann sums, midpoint
and trapezoid replay, polynomial antiderivative endpoint replay, monotone lower
and upper sums, checked false integral rejection, and a fundamental-theorem
Lean-horizon row. `multivariable-calculus-rational-v0` now validates exact
rational bivariate-polynomial value/gradient replay, directional derivatives
as gradient dot products, Jacobian chain-rule matrix replay, Hessian
positive-definiteness by leading principal minors, checked bad-gradient
rejection, and a multivariable-calculus Lean-horizon row.
`proof-methods-refutation-v0`
now validates the `PHP(2,2)` control witness and the `PHP(3,2)` refutation by
deterministic CNF truth-table enumeration plus a source-linked Bool/CNF
DRAT/LRAT route regression.

Recommended order:

1. `proof-methods-refutation-v0` (landed) and
   `proof-methods-patterns-v0` (landed): negation-as-query, pigeonhole,
   direct proof, contrapositive, cases, contradiction, invalid converse
   counterexamples, checked finite CNF/truth-table refutations, and
   source-linked DRAT/LRAT evidence for the PHP and contradiction rows.
2. `finite-sets-v0` (landed), `relations-functions-v0` (landed),
   `equivalence-classes-v0` (landed), `function-composition-v0` (landed),
   `finite-monoids-v0` (landed), `finite-permutation-groups-v0` (landed),
   and `finite-order-lattices-v0` (landed):
   finite set identities, relation properties, partial orders, lattice
   meet/join tables, monotone maps, function properties, composition,
   image/preimage, inverse tables, closed transformation monoids,
   permutation groups as bijective function tables, equivalence classes,
   partitions, and quotient maps.
3. `gcd-bezout-v0` (landed): gcd, Bezout, divisibility, and fixed
   Diophantine obstruction checks.
4. `modular-arithmetic-v0` and `finite-ideals-v0`: CRT, modular inverse,
   residue witness checks, checked QF_LIA nonunit and incompatible-CRT
   Diophantine obstructions, checked fixed-width QF_BV/DRAT nonunit-inverse and Fermat-unit searches,
   modular ring ideals, quotient-ring replay,
   quotient representative congruence, and ring-homomorphism kernel/image
   checks.
5. `finite-fields-v0` (landed), `finite-algebra-homomorphisms-v0`
   (landed), `finite-ideals-v0` (landed), `finite-vector-spaces-v0`
   (landed), `finite-dual-spaces-v0` (landed), `finite-modules-v0`
   (landed), `finite-monoids-v0` (landed),
   `finite-permutation-groups-v0` (landed), `finite-group-actions-v0`
   (landed), and
   `finite-tensor-products-v0` (landed): prime-field axioms,
   composite-modulus counterexample, finite homomorphism tables, kernel/image
   replay, quotient maps, quotient rings, induced-map checks, QF_UF/Alethe
   homomorphism-preservation and quotient representative congruence proof rows,
   finite monoids, unit/idempotent replay,
   finite permutation groups, cycle/sign replay,
   finite group actions, orbit/stabilizer replay, Burnside counting, finite
   vector spaces over `F2`, finite dual spaces and
   covectors, finite modules over `Z/4Z`, bilinear maps, and tensor product
   replay.
6. `rationals-lra-v0`: density/trichotomy and exact rational LRA certificates.
7. `linear-algebra-rational-v0`, `finite-vector-spaces-v0`,
   `finite-dual-spaces-v0`, `finite-modules-v0`,
   `finite-tensor-products-v0`, and
   `multivariable-calculus-rational-v0` (landed): fixed matrices, finite
   vector spaces over `F2`, finite modules over `Z/4Z`, subspaces, spans,
   dual bases, annihilators, transpose maps, quotient modules, tensor
   products, bilinear maps, Kronecker products, linear maps, rank-nullity
   replay, LU replay, Jacobian/Hessian matrix replay, and inconsistent systems
   with Farkas evidence where available.
8. `polynomial-identities-v0`, `polynomial-factorization-rational-v0`,
   and `generating-functions-v0` (landed): factor theorem, fixed-degree
   identities, rational factor products, polynomial division, Euclidean GCD,
   square-free decomposition, irreducible-quadratic rejection, finite
   coefficient extraction, Cauchy products, and bounded
   recurrence/generating-function prefixes.
9. `counting-v0` (landed), `finite-permutation-groups-v0` (landed), and
   `finite-group-actions-v0` (landed): combinations, pigeonhole, finite
   counting witnesses, finite cycle/sign replay, finite orbit counts, and
   Burnside fixed-point averages.
10. `number-theory-v0` (landed): CRT compatibility, quadratic residues,
    QF_BV/DRAT residue evidence, sum-of-two-squares, bounded Diophantine
    witnesses, and checked QF_LIA gcd obstruction evidence.
11. `integer-lia-v0` (landed): signed order facts, linear equations,
    interval infeasibility, and GCD-test refutations.
12. `natural-arithmetic-v0` (landed): bounded successor/addition replay,
    commutativity, distributivity, and Peano-style bounded no-counterexamples.
13. `finite-cardinality-v0` (landed),
    `cardinality-principles-v0` (landed), and
    `finite-order-lattices-v0` (landed): finite bijections, finite cardinal
    inequalities, injection/surjection refutations, inclusion-exclusion,
    disjoint unions, double counting, powersets, finite Boolean lattices, and
    infinite-cardinality Lean-horizon metadata.
14. `induction-obligations-v0` (landed) and `induction-patterns-v0` (landed):
    bounded base/step obligations, finite weak and strong induction patterns,
    a checked QF_LIA arithmetic-DPLL bad-step count obstruction, a checked
    QF_LIA finite even-product parity obstruction, loop-invariant replay,
    bad-step witnesses, and full-schema Lean-horizon metadata.
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
    checked bounded Cauchy-tail and bad reciprocal-tail Farkas rows, and
    general convergence Lean-horizon metadata.
19. `bounded-monotone-sequence-v0` (landed): finite monotone-prefix,
    finite supremum, finite tail-gap replay, checked bad upper-bound and
    bad tail-gap QF_LRA/Farkas rejections, and monotone-convergence
    Lean-horizon metadata.
20. `finite-recurrence-prefix-v0` (landed): Fibonacci prefix replay, affine
    recurrence replay, companion-matrix state replay, checked bad finite-value
    and bad affine-step QF_LRA/Farkas rejections, and recurrence-theory
    Lean-horizon metadata.
21. `finite-root-finding-v0` (landed): exact bisection and Newton-step
    replay, fixed residual decrease, checked bad Newton-step and bad
    bisection-width QF_LRA/Farkas rejections, and convergence/stability
    Lean-horizon metadata.
22. `calculus-algebraic-shadow-v0` (landed),
    `calculus-riemann-sum-v0` (landed), and
    `multivariable-calculus-rational-v0` (landed): polynomial derivative
    replay, product-rule identity checks, tangent-line replay, critical-point
    checks, exact rational gradients, directional derivatives, Jacobian
    chain-rule replay, Hessian minors, finite Riemann sums, antiderivative
    endpoint replay, false derivative/integral rejection, and analytic
    calculus Lean-horizon metadata.
23. `real-analysis-rational-v0` (landed): exact rational interval/ball
    inclusion, bounded epsilon-delta samples, squeeze-style polynomial side
    conditions, QF_LRA/Farkas bad-delta rejection, adjacent metric-continuity
    bad-preimage evidence, and general real-analysis Lean-horizon metadata.

Exit criteria:

- At least eight packs validate.
- At least three packs include checked UNSAT evidence, not only SAT witnesses.
- Curriculum rows for `planned` nodes are updated as packs land.
- Any missing proof route is explicitly listed in the proof-gap dashboard.

### Phase M4: Field Expansion Packs

Add the fields users naturally expect from an undergraduate/graduate math map.

Status: first field-extension packs landed.
`artifacts/examples/math/graph-coloring-v0/` now validates coloring witnesses
and a tiny exhaustive non-colorability check, with both CNF/LRAT and one-bit
QF_BV/DRAT proof-route regressions for triangle non-2-colorability.
`artifacts/examples/math/graph-reachability-v0/` now validates finite BFS
shortest-distance replay, deterministic DFS traversal replay, disconnected
no-path refutation, and edge-cut separation replay.
`artifacts/examples/math/graph-search-runtime-v0/` now validates finite BFS and
DFS target-discovery cost counters, shortcut-tail family replay, checked
rejection of a false DFS cost bound, and an asymptotic search-runtime
Lean-horizon row.
`artifacts/examples/math/graph-matching-v0/` now validates finite matching
witness replay, invalid-overlap rejection, augmenting-path flip replay, and a
perfect-matching obstruction by exhaustive enumeration.
`artifacts/examples/math/graph-d-separation-v0/` now validates finite DAG
d-separation checks for chains, forks, colliders, and descendant-opened
colliders, with source-linked CNF/DRAT/LRAT evidence for both
conditioned-chain and unconditioned-collider blocker rows.
`artifacts/examples/math/graph-cut-v0/` now validates finite minimum edge-cut
and vertex-cut certificates, plus checked rejection of non-separating one-edge
and one-vertex cuts.
`artifacts/examples/math/finite-probability-v0/` now validates finite
probability mass tables, conditional probability, Bayes posterior replay,
finite independence replay, total variation replay, and checked QF_LRA/Farkas
rejection of false normalization, conditional-probability, Bayes-posterior,
independence, and total-variation claims.
`artifacts/examples/math/descriptive-statistics-v0/` now validates exact
mean/variance identities, checked rejection of a bad variance claim,
contingency-table margins, and a Simpson's paradox count-table witness.
`artifacts/examples/math/least-squares-regression-v0/` now validates exact
least-squares normal equations, residual orthogonality, mean-baseline RSS
comparison, checked QF_LRA/Farkas rejection of bad RSS-improvement and bad
coefficient claims, and a regression-statistics Lean-horizon row.
`artifacts/examples/math/linear-optimization-v0/` now validates LP feasibility
witnesses, objective-threshold replay, and a tiny checked Farkas certificate.
`artifacts/examples/math/convexity-rational-v0/` now validates exact rational
midpoint convexity, finite-grid second differences, affine monotonicity
threshold replay, checked rejection of bad midpoint-convexity and
affine-threshold claims, and a general convex-analysis Lean-horizon row.
`artifacts/examples/math/multivariable-calculus-rational-v0/` now validates
exact rational gradient/value replay, directional-derivative dot products,
Jacobian chain-rule matrix replay, Hessian positive-definiteness by principal
minors, checked rejection of a bad gradient, and a multivariable-calculus
Lean-horizon row.
`artifacts/examples/math/coordinate-geometry-v0/` now validates exact midpoint,
collinearity, squared-distance coordinate checks, and checked QF_LRA/Farkas
rejection of bad midpoint-coordinate and squared-distance claims.
`artifacts/examples/math/incidence-geometry-v0/` now validates exact
line-equation replay, non-parallel line intersection, point-on-line replay,
checked QF_LRA/Farkas rejection of false intersection-coordinate and incidence
claims, and a projective/synthetic geometry Lean-horizon row.
`artifacts/examples/math/rigid-configuration-geometry-v0/` now validates exact
triangle distance-table replay, translation isometry replay, congruent-triangle
distance replay, checked QF_LRA/Farkas rejection of a false distance-table
claim, and a graph-rigidity/rigid-motion-classification Lean-horizon row.
`artifacts/examples/math/affine-geometry-v0/` now validates exact affine
point-image replay, midpoint preservation, collinearity preservation, checked
QF_LRA/Farkas rejection of false affine midpoint-coordinate,
collinearity-determinant, and distance-preservation claims, and a general
affine-geometry Lean-horizon row.
`artifacts/examples/math/orientation-area-geometry-v0/` now validates exact
signed-area/orientation replay, affine area scaling by determinant,
barycentric point-inside replay, checked QF_LRA/Farkas rejection of false
affine-area scaling and orientation claims, and a general oriented-geometry
Lean-horizon row.
`artifacts/examples/math/finite-circle-geometry-v0/` now validates exact
point-on-circle replay, tangent-line/radius perpendicularity, chord-midpoint
perpendicularity, circle-line intersection replay, checked QF_LRA/Farkas
rejection of false radius and line-intersection claims, and a general
circle-geometry Lean-horizon row.
`artifacts/examples/math/finite-inversion-geometry-v0/` now validates exact
unit-circle inversion replay, inverse-distance product checking, collinearity
replay, checked QF_LRA/Farkas rejection of false inverse-coordinate and
inverse-distance-product claims, and a general inversion-geometry Lean-horizon
row.
`artifacts/examples/math/finite-cyclic-geometry-v0/` now validates exact
cyclic quadrilateral replay, diagonal-intersection and diagonal-perpendicularity
replay, opposite-angle dot-product replay, rational Ptolemy replay, checked
QF_LRA/Farkas rejection of false diagonal-intersection, opposite-angle, and
Ptolemy claims, and a general cyclic-geometry Lean-horizon row.
`artifacts/examples/math/finite-topology-v0/` now validates finite topology
axioms, closure/interior computation, exact finite metric-ball replay, and a
checked Bool/CNF DRAT/LRAT rejection of a malformed open-set family that omits
the empty set.
`artifacts/examples/math/metric-continuity-v0/` now validates finite
Lipschitz, epsilon-delta, and open-ball preimage checks with exact rational
metrics, plus checked QF_LRA/Farkas rejection of an overlarge delta and a
malformed open-ball preimage row.
`artifacts/examples/math/finite-compactness-v0/` now validates finite
open-cover/subcover checks, minimal subcover enumeration,
finite-intersection-family replay, checked Bool/CNF bad-cover rejection, and a
compactness Lean-horizon row.
`artifacts/examples/math/finite-connectedness-v0/` now validates finite
connectedness by clopen-subset enumeration, open-separation replay, checked
Bool/CNF rejection of a false connectedness claim, and a connectedness
Lean-horizon row.
`artifacts/examples/math/finite-continuous-maps-v0/` now validates finite
continuity by open-set preimage enumeration, finite homeomorphism replay,
checked QF_UF/Alethe rejection of a bad preimage-membership row, checked
rejection of false continuity and homeomorphism claims, and a continuous-map
Lean-horizon row.
`artifacts/examples/math/finite-simplicial-homology-v0/` now validates finite
simplicial-complex closure, oriented-boundary replay, the finite
`boundary^2 = 0` chain-complex identity, fixed Betti-rank replay over `Q`,
checked rejection of a bad boundary sign, a checked QF_LIA bad boundary
coefficient obstruction, and a general homology Lean-horizon row.
`artifacts/examples/math/finite-measure-v0/` now validates finite
sigma-algebra axioms, exact finite additivity, event/complement measure
replay, and checked QF_LRA/Farkas rejection of a bad complement-measure row.
`artifacts/examples/math/finite-measure-monotonicity-v0/` now validates
normalized finite measure-table replay, subset monotonicity, union
subadditivity, checked QF_LRA/Farkas rejection of bad subset-measure and
union-subadditivity rows, and a convergence/countable-measure Lean-horizon row.
`artifacts/examples/math/finite-integration-v0/` now validates exact finite
simple-function integrals, indicator integrals, integral linearity, checked
QF_LRA/Farkas rejection of a false expectation, and a Lebesgue-integration
Lean-horizon row.
`artifacts/examples/math/finite-product-measure-v0/` now validates exact
finite product-measure tables, rectangle probabilities, left and right
marginals, finite Fubini replay, checked QF_LRA/Farkas rejection of a false
product probability and a false marginal, and a Fubini/Tonelli Lean-horizon
row.
`artifacts/examples/math/finite-random-variables-v0/` now validates exact
finite random-variable pushforwards, expectation through pushforward
distributions, finite independence checks, checked QF_LRA/Farkas rejection of
a false pushforward distribution and a false expectation-through-pushforward
claim, and a general random-variable/conditional expectation Lean-horizon row.
`artifacts/examples/math/finite-conditional-expectation-v0/` now validates
exact finite partition conditional expectations, the law of total expectation,
the finite tower property over nested partitions, finite conditional-variance
decomposition, checked QF_LRA/Farkas rejection of false
conditional-expectation, total-expectation, tower-property, and
variance-decomposition tables, and a general conditional-expectation/martingale
Lean-horizon row.
`artifacts/examples/math/finite-martingales-v0/` now validates exact finite
filtrations, adaptedness, martingale conditional-expectation equalities,
finite square-submartingale inequalities, bounded stopping-time replay, checked
QF_LRA/Farkas rejection of false stopped-expectation and martingale tables, and
a general martingale Lean-horizon row.
`artifacts/examples/math/finite-stochastic-kernels-v0/` now validates exact
finite source-to-target probability kernels, pushforward distributions, joint
factorization/disintegration replay, kernel composition, checked rejection of a
malformed kernel row with QF_LRA/Farkas evidence, and a
regular-conditional-probability Lean-horizon row.
`artifacts/examples/math/finite-hitting-times-v0/` now validates exact finite
first-hit distributions, survival probabilities, absorption-probability
fixed-point equations, expected hitting-time equations, checked QF_LRA/Farkas
rejection of false survival-mass and expected-time tables, and a
recurrence/transience Lean-horizon row.
`artifacts/examples/math/finite-concentration-v0/` now validates exact finite
Markov, Chebyshev, and union-bound replays over rational atom tables, checked
rejection of false tail and union bounds, and a concentration/limit-theorem
Lean-horizon row.
`artifacts/examples/math/bounded-dynamics-v0/` now validates exact rational
recurrence traces, bounded invariant witnesses, threshold reachability replay,
and checked QF_LRA/Farkas rejection of bad transition-step, bad threshold-step, and invariant-bound
rows.
`artifacts/examples/math/finite-euler-method-v0/` now validates exact finite
Euler-method traces, polynomial-solution error replay, invariant checks,
checked QF_LRA/Farkas rejection of bad max-error, bad terminal-error, and bad
Euler-step rows, and an ODE-theory Lean-horizon row.
`artifacts/examples/math/finite-operator-v0/` now validates exact
finite-dimensional norm, matrix-operator, Chebyshev recurrence checks, and a
checked QF_LRA/Farkas bad `l1` norm row, bad operator-bound row, and bad
Chebyshev-prefix row.
`artifacts/examples/math/inner-product-spaces-rational-v0/` now validates
exact rational Gram matrices, positive-definite principal minors,
Cauchy-Schwarz replay for fixed vectors, orthogonal projection replay,
Gram-Schmidt replay, checked QF_LRA/Farkas rejection of a bad inner product
and bad projection-orthogonality claim, and a general
inner-product/Hilbert-space Lean-horizon row.
`artifacts/examples/math/finite-chebyshev-systems-v0/` now validates exact
finite Vandermonde unisolvence, interpolation matrix replay, alternating
residual sign patterns, checked QF_LRA/Farkas rejection of duplicate-node
determinant and bad interpolation-sample conflicts, and a general
Chebyshev-system Lean-horizon row.
`artifacts/examples/math/complex-algebraic-v0/` now validates exact complex
arithmetic, conjugate/norm replay, checked QF_LRA/Farkas rejection of bad
product-coordinate and norm-squared rows, and a fixed polynomial-root witness
using real-pair algebra.
`artifacts/examples/math/complex-plane-transforms-v0/` now validates exact
unit-root cycles, conjugation/product replay, rational Mobius-transform
replay, checked rejection of false conjugation-product imaginary-part and
unit-square real-part claims, and a complex-analysis Lean-horizon row.
`artifacts/examples/math/numerical-linear-algebra-v0/` now validates exact
residual bounds, rational solution boxes, Jacobi one-step contraction replay,
and checked QF_LRA/Farkas rejection of false residual, solution-box, and
Jacobi error bounds.
`artifacts/examples/math/finite-root-finding-v0/` now validates exact
bisection and Newton-step replay, fixed residual decrease, checked
QF_LRA/Farkas rejection of false Newton-iterate and bisection-width claims,
and a root-finding-convergence/stability Lean-horizon row.
`artifacts/examples/math/finite-separation-v0/` now validates exact
convex-combination replay, separating-hyperplane score replay, supporting-face
checks, checked QF_LRA/Farkas rejection of a false separator, and a
separation/duality Lean-horizon row.
`artifacts/examples/math/finite-kkt-v0/` now validates exact
constrained-quadratic grid replay, stationarity replay,
complementary-slackness replay, checked QF_LRA/Farkas rejection of a false
stationarity multiplier, and a KKT-sufficiency Lean-horizon row.
`artifacts/examples/math/finite-sdp-v0/` now validates exact two-by-two PSD
replay, trace/objective arithmetic, dual-slack matrix replay, zero-gap replay,
checked QF_LRA/Farkas rejection of false objective and false duality-gap claims, and an SDP-duality
Lean-horizon row.
`artifacts/examples/math/finite-gradient-descent-v0/` now validates exact
quadratic gradient replay, finite descent-step arithmetic, objective-decrease
and descent-bound replay, checked QF_LRA/Farkas rejection of false decrease,
false step-coordinate, and false descent-bound claims, and a gradient-descent
convergence Lean-horizon row.
`artifacts/examples/math/finite-line-search-v0/` now validates exact
descent-direction replay, rejected Armijo trial-step arithmetic,
accepted backtracked-step replay, checked QF_LRA/Farkas rejection of a false
descent-direction claim, a false Armijo acceptance claim, and a false
accepted-candidate claim, and a line-search convergence Lean-horizon row.
`artifacts/examples/math/finite-wolfe-line-search-v0/` now validates exact
descent-direction replay, exact one-dimensional line minimization,
Wolfe sufficient-decrease and curvature checks, checked QF_LRA/Farkas
rejection of false line-minimizer and curvature claims, and a Wolfe
line-search Lean-horizon row.
`artifacts/examples/math/finite-projected-gradient-v0/` now validates exact
projected-gradient interval replay, unconstrained-step arithmetic, projection
onto `[0,1]`, projected objective decrease, checked QF_LRA/Farkas rejection of
false projected-point and projected-decrease claims, and a projected-gradient
convergence Lean-horizon row.
`artifacts/examples/math/finite-proximal-gradient-v0/` now validates exact
proximal-gradient L1 soft-threshold replay, ordinary trial-step arithmetic,
composite objective decrease, checked QF_LRA/Farkas rejection of a false
proximal point, and a proximal-gradient convergence Lean-horizon row.
`artifacts/examples/math/spectral-linear-algebra-v0/` now validates exact
finite eigenpair replay, orthogonal eigenbasis checks, Rayleigh quotients,
spectral decomposition replay, and checked QF_LRA/Farkas rejection of false
Rayleigh-quotient and eigenpair claims.
`artifacts/examples/math/matrix-invariants-v0/` now validates exact
trace/determinant characteristic-polynomial replay, characteristic roots,
Cayley-Hamilton replay, finite Gershgorin intervals, and checked QF_LRA/Farkas
rejection of false trace and characteristic-polynomial claims.
`artifacts/examples/math/random-matrix-finite-v0/` now validates exact finite
random-matrix moment replay, expected Gram matrices, rank probabilities, and
checked QF_LRA/Farkas rejection of false trace-square and expected-rank
claims.
`artifacts/examples/math/finite-markov-chain-v0/` now validates exact
row-stochastic matrix replay, finite-horizon distribution evolution,
stationary-distribution replay, and checked QF_LRA/Farkas rejection of a
malformed transition row plus a false stationary-distribution row.
`artifacts/examples/math/exact-statistical-tests-v0/` now validates exact
binomial tails, hypergeometric point probabilities, one-sided and
probability-ordered two-sided Fisher p-values, probability-ordered exact
multinomial p-values, checked QF_LRA/Farkas rejection of false Fisher and
multinomial p-values, and a checked QF_LIA bad tail-count obstruction.

Recommended order:

1. Graph resources landed: `graph-coloring-v0`, `graph-reachability-v0`,
   `graph-search-runtime-v0`, `graph-matching-v0`,
   `graph-d-separation-v0`, and `graph-cut-v0` validate SAT colorings,
   non-colorability, finite reachability, traversal traces, finite search
   cost counters, cut separation, matching witnesses, augmenting paths, finite
   DAG d-separation including checked conditioned-chain and
   unconditioned-collider CNF blockers, and minimum cut certificates.
2. `finite-probability-v0`: probability mass, conditioning, Bayes rule,
   finite independence, total variation, and checked bad normalization/
   Bayes-posterior/independence/total-variation certificates.
3. `descriptive-statistics-v0` and `least-squares-regression-v0`:
   mean/variance identities, checked bad-variance rejection, contingency
   tables, Simpson witness, least-squares normal equations, residual
   orthogonality, bad RSS-improvement rejection, and bad-coefficient
   rejection.
4. `linear-optimization-v0`: LP feasibility, threshold cliffs, Farkas links.
5. `convexity-rational-v0`: midpoint convexity, finite second differences,
   monotonicity thresholds, and checked bad midpoint-convexity plus
   affine-threshold rejection.
6. `multivariable-calculus-rational-v0`: exact rational gradients,
   directional derivatives, Jacobian chain-rule replay, Hessian minors, and
   bad-gradient rejection for calculus, optimization, and numerical analysis.
7. `coordinate-geometry-v0`, `incidence-geometry-v0`,
   `rigid-configuration-geometry-v0`, `affine-geometry-v0`,
   `orientation-area-geometry-v0`, `finite-circle-geometry-v0`,
   `finite-inversion-geometry-v0`, and `finite-cyclic-geometry-v0`:
   collinearity, midpoint, distance
   constraints, line equations, point-on-line replay, non-parallel
   intersections, triangle distance tables, finite isometry shadows, affine
   maps, signed area/orientation, barycentric replay, circle point/tangent/chord
   replay, inversion image/distance-product replay, finite incidence
   preservation, QF_LRA/Farkas false squared-distance rejection,
   QF_LRA/Farkas false incidence rejection, QF_LRA/Farkas false
   distance-table rejection, QF_LRA/Farkas false distance-preservation
   rejection, QF_LRA/Farkas false area-scaling rejection, and QF_LRA/Farkas
   false orientation rejection.
8. `finite-topology-v0`: finite closure/interior, metric-ball examples, and
   checked Bool/CNF bad-empty-open rejection.
9. `finite-measure-v0` and `finite-measure-monotonicity-v0`: finite
   sigma-algebras, finite measure checks, monotonicity/subadditivity, and
   QF_LRA/Farkas false complement-measure, false subset-measure, and false
   union-subadditivity rejection.
10. `bounded-dynamics-v0` and `finite-euler-method-v0`: recurrence systems,
   Euler step replay, finite error checks, invariants, and QF_LRA/Farkas bad
   error-bound plus fixed-step rejection.
11. `finite-operator-v0` and `inner-product-spaces-rational-v0`:
   finite-dimensional norms/operators, exact rational inner products,
   projections, Gram-Schmidt replay, QF_LRA/Farkas bad-bound, bad-norm, and
   bad projection-orthogonality rejections, and Chebyshev polynomial examples.
12. `complex-algebraic-v0` and `complex-plane-transforms-v0`: complex
    arithmetic, unit-root cycles, conjugation/product replay, QF_LRA/Farkas
    bad product-coordinate/norm/conjugation-product/unit-square rejections,
    and rational Mobius transforms as real-pair algebra.
13. `numerical-linear-algebra-v0`: residual bounds, rational solution boxes,
    exact iterative-method error replay, and checked bad residual,
    solution-box, and Jacobi error bounds.
14. `random-matrix-finite-v0`: finite matrix-valued probability tables,
    exact moments, Gram expectations, rank distributions, and checked
    QF_LRA/Farkas bad trace-square and expected-rank certificates.
15. `finite-markov-chain-v0`: stochastic matrices, finite-horizon
    distribution replay, stationary distributions, bad transition rows, and
    checked bad stationary claims.
16. `exact-statistical-tests-v0`: exact binomial and hypergeometric p-values
    for finite statistical tests, plus a checked QF_LIA bad-count certificate.
17. `spectral-linear-algebra-v0`: exact eigenpairs, orthogonal eigenbases,
    Rayleigh quotients, finite spectral decomposition, and QF_LRA/Farkas
    bad-Rayleigh-quotient and bad-eigenpair rejections.
18. `matrix-invariants-v0`: trace/determinant characteristic polynomials,
    roots, Cayley-Hamilton replay, finite eigenvalue intervals, and
    QF_LRA/Farkas bad-trace and bad-characteristic-polynomial rejections.
19. `metric-continuity-v0`: finite Lipschitz, epsilon-delta, open-ball
    preimage, and checked QF_LRA/Farkas bad-delta and bad-preimage checks over
    exact rational metric spaces.
20. `finite-compactness-v0`: finite open covers, minimal subcover
    enumeration, finite-intersection families, and checked Bool/CNF bad-cover
    rejection.
21. `finite-connectedness-v0`: finite connected spaces, open separations,
    clopen-subset enumeration, and checked Bool/CNF bad-connected-claim
    rejection.
22. `finite-continuous-maps-v0`: finite topological continuity, open-set
    preimages, homeomorphism replay, and bad-map rejection.
23. `finite-simplicial-homology-v0`: finite simplicial-complex closure,
    oriented-boundary replay, `boundary^2 = 0`, fixed Betti-rank replay, and
    bad-boundary rejection with a checked QF_LIA bad-coefficient certificate.
24. `finite-integration-v0`: finite simple-function integrals, indicator
    integrals, exact linearity, and bad-expectation rejection.
25. `finite-product-measure-v0`: finite product probability tables,
    rectangle probabilities, marginals, finite Fubini replay, and bad
    product-probability and bad marginal rejection.
26. `finite-random-variables-v0`: finite random-variable pushforwards,
    expectation through pushforward distributions, independence checks, and
    bad pushforward and bad expectation-through-pushforward rejection.
27. `finite-conditional-expectation-v0`: finite partition conditional
    expectations, law of total expectation, tower property replay, conditional
    variance decomposition, and QF_LRA/Farkas bad conditional-expectation, bad
    total-expectation, bad tower-property, and bad variance-decomposition
    rejections.
28. `finite-martingales-v0`: finite filtrations, adaptedness, martingale
    equalities, square submartingale inequalities, bounded stopping replay, and
    QF_LRA/Farkas bad stopped-expectation/martingale rejection.
29. `finite-stochastic-kernels-v0`: finite source-to-target kernels,
    pushforward distributions, joint disintegration replay, kernel
    composition, and QF_LRA/Farkas bad kernel-row and bad composition-entry
    rejections.
30. `finite-hitting-times-v0`: finite first-hit distributions, survival
    probabilities, absorption-probability equations, expected hitting-time
    equations, and bad survival-mass/expected-time rejection.
31. `finite-concentration-v0`: finite Markov, Chebyshev, and union-bound
    tail checks, plus rejection of a false concentration bound.
32. `finite-chebyshev-systems-v0`: finite Vandermonde unisolvence,
    interpolation replay, alternating residual signs, duplicate-node rejection,
    and checked bad interpolation-sample rejection.
33. `finite-root-finding-v0`: exact bisection/Newton iteration replay,
    residual-decrease checking, and checked QF_LRA/Farkas bad-step plus
    bad-width rejection, while convergence and floating-point stability remain
    horizon claims.
34. `finite-separation-v0`: exact convex-hull membership, separating
    hyperplane score replay, supporting-face checks, and checked QF_LRA/Farkas
    bad convex-combination plus bad-separator rejection, while general
    separation and duality theorems remain horizon claims.
35. `finite-kkt-v0`: exact constrained-quadratic grid replay, stationarity,
    complementary slackness, checked QF_LRA/Farkas bad-stationarity
    rejection, and checked QF_LRA/Farkas bad-complementarity rejection, while
    general KKT sufficiency and constraint qualifications remain horizon
    claims.
36. `finite-active-set-qp-v0`: exact unconstrained-minimizer replay,
    active-face candidate replay, KKT stationarity/complementarity,
    inactive-constraint slack replay, degenerate active-bound replay, and
    checked QF_LRA/Farkas bad-free-gradient, bad-inactive-slack, and
    bad-degenerate-multiplier rejections, while finite termination, broader
    degeneracy handling, anti-cycling, and active-set convergence theorems
    remain horizon claims.
37. `finite-sdp-v0`: exact two-by-two PSD replay, trace/objective arithmetic,
    dual-slack matrix replay, zero duality-gap checking, and checked
    QF_LRA/Farkas bad-objective, bad-duality-gap, and bad-slack-entry
    rejections, while general SDP duality and
    convergence theorems remain horizon claims.
38. `finite-gradient-descent-v0`: exact quadratic gradient replay, descent-step
    arithmetic, objective-decrease and descent-bound replay, and checked
    QF_LRA/Farkas bad-decrease, bad step-coordinate, and bad descent-bound
    rejections, while rate, stochastic, and convergence theorems remain horizon
    claims.
39. `finite-line-search-v0`: exact Armijo descent-direction replay, trial-step
    rejection, accepted-backtrack replay, and checked QF_LRA/Farkas bad-Armijo
    bad descent-direction, and bad accepted-candidate rejections, while strong
    Wolfe variants, projected/stochastic line search, and convergence theorems
    remain horizon claims.
40. `finite-wolfe-line-search-v0`: exact descent-direction replay, exact
    line-minimizer replay, Wolfe sufficient-decrease/curvature replay, and
    checked QF_LRA/Farkas bad-minimizer, bad sufficient-decrease, and
    bad-curvature rejections, while strong Wolfe variants, stochastic line
    search, and convergence theorems remain horizon claims.
41. `finite-projected-gradient-v0`: exact gradient replay, unconstrained-step
    arithmetic, interval projection, projected descent, and checked QF_LRA/Farkas
    bad-projection and bad projected-decrease rejections, while active-set,
    proximal, stochastic, and projected-gradient convergence theorems remain
    horizon claims.
42. `finite-proximal-gradient-v0`: exact smooth-gradient replay, ordinary
    trial-step arithmetic, L1 soft-threshold replay, box-plus-L1 constrained
    replay, composite descent, and checked QF_LRA/Farkas bad-proximal-point
    plus bad box-proximal-point rejections, while composite convex-analysis,
    stochastic, active-set, and proximal-gradient convergence theorems remain
    horizon claims.

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
walkthrough using validated pack data. The end-to-end lessons now trace
propositional truth-table replay, finite predicate replay, proof-by-refutation
replay, proof-pattern replay, bounded induction-obligation replay,
induction-pattern replay, graph coloring, bounded natural-arithmetic replay,
signed integer-LIA replay, gcd/Bezout replay, modular-arithmetic replay,
modular nonunit/CRT Diophantine evidence, modular nonunit-inverse and Fermat-unit QF_BV/DRAT
evidence, bounded number-theory replay, complex
real-pair replay, rational midpoint
replay, bounded rational real-analysis replay, real-algebra RCF-shadow replay,
metric-continuity replay, polynomial-identity replay, rational
polynomial-factorization replay, complex plane transform replay,
matrix-invariant replay, linear-system/LP replay, finite conditional
probability, rational multivariable-calculus replay, rational inner-product
replay, finite set and relation/function replay, equivalence-class replay,
function-composition replay, finite group table replay, finite monoid replay,
finite permutation-group replay, finite group-action/Burnside replay, finite
order/lattice replay, finite cardinality replay, cardinality-principle replay,
finite ring/field replay, finite ideal and quotient-ring replay, finite
algebra-homomorphism replay, finite vector-space/dual/module/tensor replay,
finite topology/measure including checked bad-empty-open and
bad-complement-measure rows, bounded dynamics/operators, finite
Euler-step/error replay, finite compactness/connectedness/continuous-map
replay, finite simplicial-homology replay, finite integration replay, finite
product-measure/Fubini replay, finite random-variable replay, and finite
conditional-expectation replay, finite martingale replay, and finite
stochastic-kernel replay, finite hitting-time replay, finite concentration
replay, and finite Chebyshev-system
interpolation/alternation, plus spectral-linear-algebra
eigenpair/decomposition replay and finite random-matrix moment/rank replay
plus finite Markov-chain transition/stationary replay and
numerical-linear-algebra residual/solution-box/Jacobi replay from data row
through replay result and proof/evidence status, and exact descriptive
statistics/regression replay for finite samples, count tables, and normal
equations, plus coordinate/incidence/rigid/affine/oriented/circle/inversion/cyclic
geometry replay for finite rational points, line equations, maps, areas,
barycentric coordinates, circle points, and inversion images, plus finite topology/measure
replay for set-family axioms, metric balls, checked missing-empty-set rejection,
sigma-algebras, additivity, and event complements.
The finite topology and finite measure first-principles stories are now also
split into focused standalone pages, while the combined topology/measure page
remains the cross-field bridge.
The exact linear-optimization first-principles story is now also split into a
focused standalone LP/Farkas page, while the combined linear-system/LP page
remains the matrix-to-optimization bridge.
The exact finite-probability first-principles story is now also split into a
focused standalone probability mass-table page, while the broad
finite-probability page remains the stochastic-process bridge.

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
   `relations-functions-v0` now has a checked function single-valuedness artifact,
   and `equivalence-classes-v0` has a checked quotient-map congruence artifact.
4. Bounded arithmetic/Diophantine route for number-theory packs. Status:
   landed as [QF_LIA Diophantine Evidence](../proof-cookbook/recipes/qf-lia-diophantine.md)
   and promoted in `modular-arithmetic-v0` for the nonunit inverse gcd
   obstruction and incompatible non-coprime CRT obstruction, and in
   `exact-statistical-tests-v0` for the bad binomial tail-count contradiction.
   The exact Fisher left-tail p-value contradiction is covered by the
   QF_LRA/Farkas lane. The first secondary statistics exact-rational and
   margin/count rows are now promoted in `descriptive-statistics-v0` for the
   bad variance and bad contingency total, while broader modular, exact-test,
   and statistics finite-search rows remain finite replay.
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

Status: dashboard and check-hook increments landed. The proof-gap dashboard is
still generated from the concept atlas, and now also reads math example-pack
metadata and `expected.json` rows to report pack-level route coverage,
validation commands, checked/replay/proof-gap counts, and the concrete checks
that still need stronger evidence. The learner/proof-upgrade dashboard scans
math learner pages for explicit pack references, reports focused/path-only/
missing learner coverage, and groups non-checked proof rows by candidate
cookbook route. The curriculum-pressure dashboard groups packs into overlapping
Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, finite-replay, and Lean-horizon buckets
so solver/proof demand is visible without hand-maintained scans. The
solver-reuse disposition audit now reports every math pack's promoted,
non-benchmark-horizon, or unclassified status, with a concrete unclassified
queue so new packs cannot drift outside the R4-to-R5 promotion workflow. The
curriculum-status audit now separates source `curriculum_status` from generated
`resource_status`, so source `planned` rows with validated resource packs are
reviewed as explicit `covered` versus `lean-horizon` decisions instead of
hidden inside historical seed status. `just foundational-resources` and the
plain-shell fallback now regenerate the concept
atlas, validate it, validate all math example packs, require committed invalid
example-pack fixtures to fail with expected diagnostics, regenerate dashboards,
and fail if generated atlas or dashboard files are stale; CI runs the same gate
before docs link checking.

Deliverables:

- `docs/foundational-resources/generated/math-coverage.md`.
- `docs/foundational-resources/generated/curriculum-status-audit.md`.
- `docs/foundational-resources/generated/math-field-dashboard.md`.
- `docs/foundational-resources/generated/proof-gap-dashboard.md`.
- `docs/foundational-resources/generated/learner-proof-upgrade-dashboard.md`.
- `docs/foundational-resources/generated/curriculum-pressure-by-fragment.md`.
- `docs/foundational-resources/generated/solver-reuse-disposition-audit.md`.
- Optional `just check-foundational-resources` target once scripts stabilize.

Exit criteria:

- Dashboards are deterministic.
- Validators run in the normal docs/check workflow or have a documented command.
  Status: landed through `just foundational-resources`,
  `scripts/check-foundational-resources.sh`, `just check`, `scripts/check.sh`,
  and the CI docs-resources/docs-links job. The example-pack validator now also
  has negative fixtures for unknown fields, metadata/check id drift, and
  missing witness references.
- Dashboard output names gaps without manual editing.

### Phase M8: Library Boundary Decision

Only after the data and examples reveal repeated logic, decide whether to add a
workspace crate or split a sibling repository.

Status: initial decision landed in
[Foundational Resource Library Boundary Decision](LIBRARY-BOUNDARY-DECISION.md).
The resource lane stays in-repo for now. The stable boundary is the committed
JSON/schema/metadata contract plus generated dashboards, smoke-tested by
`scripts/consume-foundational-resources.py` and exercised through sample
consumer queries in `scripts/query-foundational-resources.py` and
[Foundational Resource Consumer Queries](CONSUMER-QUERIES.md). The generated
dashboards now also surface conservative R0-R6 gate and next-gate columns, so
pack-level solver-reuse and consumer-boundary progress is visible without
manual scans. The consumer query helper now also exposes field-readiness
summaries for curriculum navigation across pack counts, check counts, proof
routes, solver-reuse statuses, and Lean-horizon packs; crates or repo splits
are deferred until external consumers, generated typed APIs, or shared encoders
require them. The smoke examples now cover probability/Farkas and
differential-equations/dynamics Farkas readiness, plus measure/Farkas field
readiness, measure bridge concept lookup, and checked measure rows, so
table-probability, recurrence/Euler-style finite-analysis, and finite
measure/integration lanes are exercised at the consumer boundary.

Possible boundaries:

- `axeyum-foundational-data`: generated JSON and schema consumers.
- `axeyum-math-examples`: reusable encoders for graph, finite algebra, matrix,
  and finite probability examples.
- Separate repository only if the resources gain an independent release cycle,
  large corpora, or users who do not need the Axeyum source tree.

Exit criteria:

- At least 40 validated concept rows.
  Status: 119 atlas rows validate, including generated bridge-concept rows for
  finite model replay, counterexample proof, bounded theorem shadows,
  refutation-as-query, finite proof-pattern replay, finite quantifier
  expansion, bounded induction obligations, Boolean CNF DRAT/LRAT anatomy,
  QF_LRA Farkas certificate anatomy, exact-vs-floating arithmetic, LP
  objective-threshold replay, rational convexity/gradient shadows, QF_UF
  Alethe certificate anatomy, QF_BV bit-blast
  certificate anatomy, gcd/divisibility witnesses, modular CRT/inverse
  witnesses, finite counting replay, finite graph replay/obstruction, finite
  dynamics/Euler replay, bounded-family/asymptotic boundaries, polynomial
  coefficient/factor replay, finite Boolean algebra, finite
  partition/relation roundtrips, finite
  image/preimage/inverse tables, finite
  bijection/cardinality, cardinality theorem horizons, metric balls, bounded
  epsilon-delta shadows, rational interval replay, sequence-tail shadows,
  Cauchy-tail shadows, squeeze shadows, derivative-identity shadows,
  integration horizons, compactness shadows, connectedness shadows,
  continuity-by-preimage, finite topology-operator/homeomorphism replay,
  finite quotient-topology replay, finite specialization-order replay, finite boundary-operator replay, finite
  chain-complex/homology replay, finite torsion-homology replay, finite
  cohomology replay, finite cup-product replay, LU
  factorization replay, rank-nullity replay,
  residual bounds, eigenpair witnesses, characteristic-polynomial replay,
  finite random-matrix moments, finite measure additivity, finite probability
  mass tables, finite pushforward distributions, finite stochastic kernels,
  finite conditional expectations, finite product-measure/integration replay,
  finite tail/count obstructions, homomorphism preservation, kernel/image
  replay, quotient maps, ideal closure, module actions, tensor bilinearity,
  finite group actions, totality conventions,
  coordinate/incidence/rigid/oriented geometry replay, finite
  circle/inversion/cyclic geometry replay, complex real-pair transform replay,
  finite inner-product/projection replay,
  finite operator/Chebyshev replay, and Lean horizons, plus example-family rows
  for recurring finite-algebra QF_UF/Alethe conflicts, exact-rational
  QF_LRA/Farkas infeasibility, Boolean CNF/LRAT refutations, integer/count
  Diophantine obstructions, and fixed-width QF_BV/DRAT rows.
- At least 12 validated example packs.
  Status: 108 non-template math example packs validate.
- At least 6 packs with checked proof/evidence routes.
  Status: 108 non-template packs have at least one `checked` expected-result row.
- At least one downstream consumer can read the data without repository-internal
  knowledge.
  Status: `scripts/consume-foundational-resources.py` reads the committed atlas
  and example-pack JSON files directly without importing generator or validator
  internals. `scripts/query-foundational-resources.py` now adds sample
  consumer-facing queries over that same committed data boundary for summary
  counts, pack discovery, field-plus-proof-route discovery, checked-row mining,
  solver-reuse rows, atlas concept lookup, and field-level curriculum readiness.
  Generated dashboards expose gate/next-gate status, status-audit
  recommendations, and fragment-pressure buckets derived from the same files.

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

Progress: items 1-10, Phase M3 `proof-methods-patterns-v0`, `finite-sets-v0`,
`relations-functions-v0`, `equivalence-classes-v0`, `function-composition-v0`,
`finite-monoids-v0`,
`finite-permutation-groups-v0`,
`finite-order-lattices-v0`,
`finite-fields-v0`, `finite-algebra-homomorphisms-v0`,
`finite-group-actions-v0`,
`finite-ideals-v0`,
`finite-vector-spaces-v0`, `finite-dual-spaces-v0`,
`inner-product-spaces-rational-v0`,
`finite-tensor-products-v0`,
`finite-modules-v0`,
`polynomial-identities-v0`, `polynomial-factorization-rational-v0`,
`counting-v0`, `gcd-bezout-v0`,
`number-theory-v0`, `integer-lia-v0`, `natural-arithmetic-v0`, and
`finite-cardinality-v0`, `cardinality-principles-v0`,
`induction-obligations-v0`, `induction-patterns-v0`, `logic-basics-v0`, and
`real-analysis-rational-v0`, `calculus-riemann-sum-v0`,
`multivariable-calculus-rational-v0`, Phase M4 graph-resource
group and items 4-31, and
the Phase M5 learner-path scaffold plus first encode/check walkthrough layer
the route-oriented matrix-computation index, the matrix corpus/benchmark
boundary note, and the analysis/calculus theorem-horizon map have landed for
the math seed.
End-to-end lessons now exist for propositional
logic basics, finite predicate logic, proof by refutation, proof method
patterns, induction obligations, induction patterns, graph coloring, graph
reachability, traversal, search runtime, matching, finite DAG d-separation,
finite cut certificates, bounded natural arithmetic, rational arithmetic,
integer linear arithmetic, gcd/Bezout arithmetic, modular arithmetic, bounded
number theory, complex algebraic replay, bounded rational real analysis,
real-algebra RCF shadows, polynomial identities, rational polynomial
factorization, matrix invariants, linear algebra/optimization, rational
convexity, probability/statistics, rational multivariable calculus, rational
inner products, finite sets, finite groups, relations/functions, equivalence
classes,
finite monoids, finite permutation groups, function composition, finite group
actions, finite order lattices, finite cardinality, cardinality principles,
finite rings, finite fields, finite algebra homomorphisms, finite ideals and
quotient rings, finite vector spaces, finite dual spaces, finite modules,
finite tensor products, finite structures, and analysis/topology horizons.
Phase M6 now has cookbook links from all current non-template math example
packs, and `proof-methods-refutation-v0` has a checked finite CNF truth-table
route for its pigeonhole refutation. Phase M7 now has
generated pack-level proof-gap rows and a normal foundational-resource check
hook. `numerical-linear-algebra-v0` now adds the first exact residual/error-bound
numerical-analysis slice with checked QF_LRA/Farkas bad residual and
Jacobi-bound certificates,
and `random-matrix-finite-v0` adds the first exact finite random-matrix bridge
across linear algebra, probability, statistics, and
numerical analysis, now with checked QF_LRA/Farkas bad trace-square and
expected-rank regressions. `finite-markov-chain-v0` now adds the first exact finite
stochastic-process bridge across probability, linear algebra, statistics, and
dynamics, with checked QF_LRA/Farkas bad stochastic-row and bad stationary
distribution regressions.
`exact-statistical-tests-v0` now adds the first exact finite
statistical-test slice for p-values as rational finite sums, with a checked
QF_LRA/Farkas bad Fisher left-tail, two-sided, and multinomial rows and a
checked QF_LIA/Diophantine bad tail-count row.
`proof-methods-patterns-v0` now deepens the proof-methods curriculum row with
finite direct proof, contrapositive, proof-by-cases, contradiction, invalid
converse counterexample, and natural-deduction Lean-horizon examples.
`induction-patterns-v0` now deepens the induction curriculum row with finite
weak induction, a checked QF_LIA finite even-product parity obstruction, strong
induction, loop-invariant replay, invalid-step counterexamples, and
full-schema Lean-horizon examples.
`cardinality-principles-v0` now deepens the cardinality curriculum row with
finite inclusion-exclusion, disjoint-union additivity, bipartite-edge double
counting, powerset enumeration, invalid additivity counterexamples, a checked
QF_LIA/Diophantine overlap-additivity count obstruction, and
infinite-cardinality Lean-horizon examples.
`calculus-riemann-sum-v0` now deepens the calculus curriculum row with exact
finite Riemann sums, midpoint/trapezoid replay, antiderivative endpoint
replay, monotone lower/upper sums, false integral counterexamples, and
fundamental-theorem Lean-horizon examples.
`equivalence-classes-v0` now deepens the relations/functions curriculum row
with exact finite equivalence classes, quotient-map fibers, partition
round-trips, a checked non-transitive counterexample, and a QF_UF/Alethe
proof-object row for quotient-map congruence.
`function-composition-v0` now deepens the relations/functions curriculum row
with finite composition, image/preimage, inverse-table, associativity,
non-injective inverse counterexample, a QF_UF/Alethe composition-application
proof row, and general function-law Lean-horizon examples.
`convexity-rational-v0` now adds the first exact finite convexity bridge for
optimization learners: midpoint Jensen replay, finite second differences,
affine threshold monotonicity, and checked bad midpoint-convexity plus
affine-threshold rejection.
`spectral-linear-algebra-v0` now adds the first exact finite
spectral-linear-algebra slice for eigenpair, Rayleigh quotient, and
decomposition replay, with checked QF_LRA/Farkas false-eigenpair rejection.
`matrix-invariants-v0` now adds the characteristic
polynomial, Cayley-Hamilton, and finite eigenvalue-interval step needed before
broader spectral claims, with checked QF_LRA/Farkas false-characteristic
polynomial rejection. `metric-continuity-v0` now adds the finite
epsilon-delta and open-ball preimage bridge for analysis/topology learners.
`metric-ball-epsilon-delta-index.md` now ties the bounded rational-ball,
finite metric-continuity, sequence-tail, finite compactness, finite
connectedness, and finite open-preimage resources into one learner path while
keeping quantified continuity, compactness, connectedness, and convergence
theorems in the Lean-horizon lane.
`finite-compactness-v0` now adds the finite open-cover/subcover and
finite-intersection bridge to the compactness horizon.
`finite-connectedness-v0` now adds the finite clopen-subset/open-separation
bridge to the connectedness horizon, with checked Bool/CNF evidence for the
bad connectedness row. `finite-continuous-maps-v0` now adds the finite
preimage/homeomorphism bridge connecting continuity to compactness and
connectedness horizons, with checked QF_UF/Alethe evidence for a bad
preimage-membership row. `finite-simplicial-homology-v0` now adds the exact
finite algebraic-topology bridge: simplicial closure, oriented boundaries,
`boundary^2 = 0`, fixed Betti-rank replay, bad-boundary rejection, a checked
QF_LIA/Diophantine bad-coefficient row, and a homology Lean-horizon row.
`finite-integration-v0` now adds the exact finite
simple-function integral bridge and checked QF_LRA/Farkas bad-expectation row
between finite measure, probability, and statistics.
`finite-product-measure-v0` now adds the exact finite product
measure, marginalization, Fubini bridge, and checked QF_LRA/Farkas bad-product
probability row toward general measure/probability theory.
`finite-random-variables-v0` now adds the exact finite random-variable
pushforward, expectation, independence bridge, and checked QF_LRA/Farkas
bad-pushforward and bad expectation-through-pushforward rows toward
probability/statistics and measure-theory semantics.
`finite-conditional-expectation-v0` now adds the
finite partition conditional-expectation, total-expectation, tower-property,
and conditional-variance-decomposition bridge toward martingales and general
conditional expectation, with checked QF_LRA/Farkas evidence for bad high-block,
total-expectation, tower-property, and variance-decomposition rows.
`finite-martingales-v0` now adds the exact finite filtration, martingale,
submartingale, and bounded-stopping bridge toward stochastic-process theory,
with checked QF_LRA/Farkas evidence for bad conditional-expectation and
bad tower-property rows.
`finite-stochastic-kernels-v0` now adds the finite conditional-distribution,
pushforward, disintegration, and composition bridge toward Markov kernels and
regular conditional probabilities, with a checked QF_LRA/Farkas bad-row
normalization seed. `finite-hitting-times-v0` now adds the
finite first-hit, survival, absorption-probability, and expected-hitting-time
bridge toward recurrence/transience and potential-theory horizons.
`finite-concentration-v0` now adds the finite Markov/Chebyshev/union-bound
tail-probability bridge toward concentration inequalities, limit theorems,
martingale concentration, and asymptotic statistics.
`finite-chebyshev-systems-v0` now adds the finite Vandermonde/interpolation
and alternation-sign bridge toward Chebyshev-system, Haar-space, minimax, and
approximation-theory horizons.
`incidence-geometry-v0` now adds the exact finite incidence bridge for
geometry: line-equation replay, non-parallel line intersection, point-on-line
replay, checked QF_LRA/Farkas rejection of false intersection-coordinate and
incidence claims, and a projective/synthetic geometry Lean-horizon row.
`rigid-configuration-geometry-v0` now adds the exact finite rigidity bridge for
geometry: triangle distance-table replay, translation isometry replay,
congruent-triangle distance replay, checked QF_LRA/Farkas rejection of false
distance-table data, and a graph-rigidity/rigid-motion-classification
Lean-horizon row.
`affine-geometry-v0` now adds the exact finite affine-map bridge for geometry:
point-image replay, midpoint preservation, collinearity preservation, checked
QF_LRA/Farkas rejection of false midpoint-coordinate,
collinearity-determinant, and distance-preservation claims, and an
affine-geometry Lean-horizon row.
`orientation-area-geometry-v0` now adds the exact finite orientation/area
bridge for geometry: signed-area replay, affine determinant area scaling,
barycentric point-inside replay, checked QF_LRA/Farkas rejection of false
affine-area scaling and orientation claims, and an oriented-geometry
Lean-horizon row.
`finite-circle-geometry-v0` now adds the exact finite circle bridge for
geometry: point-on-circle replay, tangent-line/radius perpendicularity,
chord-midpoint perpendicularity, circle-line intersection replay, checked
QF_LRA/Farkas rejection of false radius and line-intersection coordinates, and
a circle-geometry Lean-horizon row.
`finite-inversion-geometry-v0` now adds the exact finite inversion bridge for
geometry: unit-circle inversion-image replay, inverse-distance product replay,
collinearity replay, checked QF_LRA/Farkas rejection of false inverse
coordinates and inverse-distance products, and an inversion-geometry
Lean-horizon row.
`finite-cyclic-geometry-v0` now adds the exact finite cyclic bridge for
geometry: cyclic quadrilateral replay, diagonal-intersection and
diagonal-perpendicularity replay, opposite-angle dot-product replay, rational
Ptolemy replay, checked QF_LRA/Farkas rejection of false
diagonal-intersection coordinates, false opposite-angle dot products, and
false Ptolemy values, and a cyclic-geometry Lean-horizon row.
`complex-plane-transforms-v0` now adds the next exact finite complex-analysis
bridge: unit-root cycles, conjugation/product replay, rational
Mobius-transform replay, checked rejection of false conjugation-product
imaginary-part and unit-square real-part claims, and a complex-analysis
Lean-horizon row.
`least-squares-regression-v0` now adds the next exact finite statistics bridge:
least-squares normal equations, residual orthogonality, mean-baseline RSS
comparison, checked QF_LRA/Farkas rejection of bad RSS-improvement and bad
coefficient claims, and a regression-statistics Lean-horizon row.
`generating-functions-v0` now adds the next exact finite discrete/polynomial
bridge: coefficient extraction, Cauchy product convolution, Fibonacci
generating-function prefix replay, checked rejection of a bad convolution
coefficient, and a generating-functions Lean-horizon row.
`polynomial-factorization-rational-v0` now adds the next exact finite
polynomial bridge: rational factor-list product replay, polynomial division,
Euclidean GCD replay, square-free decomposition, checked irreducible-quadratic
rejection, a checked QF_LRA/Farkas discriminant conflict, and a general
polynomial-factorization Lean-horizon row.
`finite-euler-method-v0` now adds the next exact finite dynamics/numerical
bridge: explicit Euler replay, polynomial-solution error replay, finite
invariant checks, checked QF_LRA/Farkas rejection of bad max-error, bad
terminal-error, and bad Euler-step rows, and an ODE-theory Lean-horizon row. `finite-algebra-homomorphisms-v0` now adds the
next exact finite algebra bridge after group/ring tables: homomorphism preservation,
kernel/image replay, quotient/induced-map replay, QF_UF/Alethe preservation
congruence, checked bad-homomorphism rejection, concrete bad-map Alethe
refutation, and an isomorphism-theorem Lean-horizon row.
`finite-vector-spaces-v0` now adds the exact finite linear-algebra bridge over
`F2`: vector-space laws, subspace/span replay, linear-map kernel/image replay,
rank-nullity by finite cardinality, checked exact non-subspace replay, an
explicit QF_UF/Alethe additive-closure membership row, and a
vector-space/module Lean-horizon row.
`finite-dual-spaces-v0` now adds the exact finite dual-space bridge over `F2`:
covector linearity, pointwise dual operations, dual-basis pairing,
annihilator recomputation, transpose-map replay, checked QF_UF/Alethe
bad-covector rejection, and a duality/functional-analysis Lean-horizon row.
`finite-group-actions-v0` now adds the exact finite group-action bridge:
action-law replay, orbit/stabilizer recomputation, orbit-stabilizer
cardinality, Burnside fixed-point counting, checked QF_UF/Alethe bad
identity-action and action-compatibility rejections, and a group-action
Lean-horizon row.
`finite-monoids-v0` now adds the exact finite function/algebra bridge:
monoid identity/associativity replay, transformation-composition table replay,
unit and idempotent recomputation, checked QF_UF/Alethe non-associative table
rejection, and a monoid/semigroup Lean-horizon row.
`finite-permutation-groups-v0` now adds the exact finite permutation bridge:
`S3` group-law replay, composition-table replay from bijective function maps,
cycle-length and sign homomorphism replay, natural action orbit/stabilizer
replay, checked QF_UF/Alethe bad-nonbijection rejection, and a
permutation-group Lean-horizon row.
`inner-product-spaces-rational-v0` now adds the exact rational
inner-product-space bridge: Gram matrices, positive-definite minors,
Cauchy-Schwarz replay, orthogonal projections, Gram-Schmidt residuals,
checked QF_LRA/Farkas bad-inner-product and bad projection-orthogonality
rejections, and an inner-product/Hilbert-space Lean-horizon row.
`finite-modules-v0` now adds the exact finite algebra/linear-algebra bridge
over `Z/4Z`: module laws, submodule/span replay, module-homomorphism
kernel/image replay, quotient-module tables, checked exact non-submodule
replay, an explicit QF_UF/Alethe scalar-closure membership row, and a
module-theory Lean-horizon row.
`finite-tensor-products-v0` now adds the exact finite multilinear-algebra
bridge over `F2`: tensor-product basis/dimension replay, bilinear-map table
replay, universal-factorization shadow through a linear map, Kronecker-product
matrix replay, checked QF_UF/Alethe bad-bilinear-map rejection, and a
tensor-theory Lean-horizon row.
`finite-ideals-v0` now adds the exact finite quotient-ring bridge over `Z/6Z`:
ideal laws, principal ideal generation, modulo-2 ring-homomorphism
kernel/image replay, quotient-ring tables, checked QF_UF/Alethe non-ideal
rejection, checked quotient representative congruence, and an ideal-theory
Lean-horizon row.
`finite-order-lattices-v0` now adds the exact finite order-theory bridge:
Boolean-lattice partial-order replay, meet/join table checks, distributivity,
monotone-map fixed-point replay, checked QF_UF/Alethe bad-order rejection,
checked Bool/CNF bad top-element rejection, and an order/lattice Lean-horizon
row.
`multivariable-calculus-rational-v0` now adds the exact finite multivariable
calculus bridge: bivariate-polynomial gradient/value replay, directional
derivatives as gradient dot products, Jacobian chain-rule replay, Hessian
minor checks for local convexity, checked bad-gradient rejection, and a
multivariable-analysis Lean-horizon row.
`convexity-rational-v0` now has a learner-facing end-to-end lesson for exact
midpoint Jensen replay, finite second-difference checks, affine threshold
monotonicity, checked bad midpoint-convexity and affine-threshold rejections,
and the general
convex-analysis Lean horizon.
`finite-kkt-v0` now has a learner-facing end-to-end lesson for exact
constrained-quadratic grid replay, KKT stationarity and complementary
slackness, checked bad-stationarity and bad-complementarity rejection with
QF_LRA/Farkas evidence, and the general KKT sufficiency Lean horizon.
`finite-active-set-qp-v0` now has a learner-facing end-to-end lesson for exact
unconstrained-minimizer replay, active-face candidate replay, inactive slack,
KKT stationarity/complementarity, checked bad-free-gradient, bad-inactive-slack,
and bad-degenerate-multiplier rejections with QF_LRA/Farkas evidence, and the
general active-set-method Lean horizon.
`finite-sdp-v0` now has a learner-facing end-to-end lesson for exact two-by-two
PSD replay, trace/objective arithmetic, dual-slack matrix replay, zero-gap
replay, checked bad-objective, bad-duality-gap, and bad-slack-entry rejections with
QF_LRA/Farkas evidence, and the general SDP-duality Lean horizon.
`finite-gradient-descent-v0` now has a learner-facing end-to-end lesson for
exact quadratic gradient replay, finite descent-step arithmetic,
objective-decrease and descent-bound replay, checked bad-decrease and bad
step-coordinate plus bad descent-bound rejections with QF_LRA/Farkas evidence,
and the general convergence Lean horizon.
`finite-line-search-v0` now has a learner-facing end-to-end lesson for exact
descent-direction replay, Armijo trial rejection, accepted-backtrack replay,
checked bad-Armijo, bad descent-direction, and bad accepted-candidate
rejection with QF_LRA/Farkas evidence, and the general line-search convergence
Lean horizon.
`finite-wolfe-line-search-v0` now has a learner-facing end-to-end lesson for
exact descent-direction replay, exact line-minimizer replay, Wolfe
sufficient-decrease and curvature replay, checked bad-minimizer and
bad-curvature rejections with QF_LRA/Farkas evidence, and the general Wolfe
line-search Lean horizon.
`finite-projected-gradient-v0` now has a learner-facing end-to-end lesson for
exact gradient replay, unconstrained-step replay, interval projection,
projected descent, checked bad-projection and bad projected-decrease rejections
with QF_LRA/Farkas evidence, and the general projected-gradient convergence
Lean horizon.
`finite-proximal-gradient-v0` now has a learner-facing end-to-end lesson for
exact smooth-gradient replay, ordinary trial-step replay, L1 soft-threshold
proximal replay, box-plus-L1 constrained replay, composite descent, checked
bad-proximal-point and bad box-proximal-point rejection with QF_LRA/Farkas
evidence, and the general proximal-gradient convergence Lean horizon.
`finite-chebyshev-systems-v0` now has a learner-facing end-to-end lesson for
exact Vandermonde unisolvence, interpolation, alternating residual signs,
checked duplicate-node-grid, bad interpolation-sample, and bad
alternation-magnitude rejection with QF_LRA/Farkas evidence, and the
Chebyshev/Haar/minimax Lean horizon.
`spectral-linear-algebra-v0` now has a learner-facing end-to-end lesson for
exact eigenpair replay, orthogonal eigenbasis arithmetic, Rayleigh quotient
checking, spectral decomposition reconstruction, checked bad-Rayleigh-quotient
and bad-eigenpair rejection with QF_LRA/Farkas evidence, and the general spectral/numerical
horizon.
`random-matrix-finite-v0` now has a learner-facing end-to-end lesson for exact
matrix-valued probability tables, trace/determinant moments, expected Gram
matrices, rank probabilities, checked QF_LRA/Farkas bad trace-square and
expected-rank rejection, and the asymptotic random-matrix/numerical horizon.
`numerical-linear-algebra-v0` now has a learner-facing end-to-end lesson for
exact residual infinity-norm replay, rational solution-box checking, one-step
Jacobi contraction replay, checked QF_LRA/Farkas bad residual-bound and
Jacobi error-bound rejection,
and the floating-point/stability/convergence horizon.
`descriptive-statistics-v0` and `least-squares-regression-v0` now have a
learner-facing end-to-end lesson for exact mean/variance replay, checked bad
variance rejection, contingency table margins, Simpson's paradox counts,
least-squares normal equations, residual orthogonality, RSS comparison,
checked QF_LRA/Farkas bad RSS-improvement and bad-coefficients rejection, and
the statistical inference/numerical regression horizon.
`coordinate-geometry-v0`, `incidence-geometry-v0`,
`rigid-configuration-geometry-v0`, `affine-geometry-v0`,
`orientation-area-geometry-v0`, `finite-circle-geometry-v0`,
`finite-inversion-geometry-v0`, and `finite-cyclic-geometry-v0` now have
learner-facing end-to-end lessons for
exact midpoint, collinearity, squared-distance, line-equation, point-on-line,
line-intersection, triangle distance-table replay, finite isometry shadows,
affine-map, signed-area, area-scaling, barycentric, point-on-circle,
tangent-line/radius perpendicularity, chord-midpoint perpendicularity,
circle-line intersection replay, unit-circle inversion replay, inverse-distance products, inversion
collinearity, cyclic quadrilateral replay, diagonal-intersection replay,
opposite-angle dot-product replay, rational Ptolemy replay,
checked QF_LRA/Farkas bad midpoint-coordinate and bad squared-distance,
checked QF_LRA/Farkas bad intersection-coordinate and bad incidence,
checked QF_LRA/Farkas bad translation-image and bad distance-table data, checked QF_LRA/Farkas
bad affine midpoint-coordinate and bad-distance-preservation, checked QF_LRA/Farkas bad area-scaling,
checked QF_LRA/Farkas bad-orientation, checked QF_LRA/Farkas bad-radius and bad line-intersection, checked QF_LRA/Farkas bad inverse-coordinate and bad inverse-distance-product,
checked QF_LRA/Farkas bad diagonal-intersection, bad opposite-angle, and bad Ptolemy rows,
and general geometry Lean-horizon rows.
`finite-topology-v0` and `finite-measure-v0` now have a learner-facing
end-to-end lesson for finite topology axioms, closure/interior, finite
metric-ball replay, checked Bool/CNF bad-empty-open rejection, finite
sigma-algebra closure, exact finite additivity, event complements, checked
QF_LRA/Farkas bad-complement rejection, and the topology/measure Lean horizon.
They now also have standalone finite-topology and finite-measure pages so
learners can start from one pack before crossing the topology/measure boundary.
`bounded-dynamics-v0` and `finite-euler-method-v0` now have a learner-facing
end-to-end lesson for bounded recurrence traces, invariant replay, threshold
reachability, checked bad transition-step, bad threshold-step, and invariant-bound rejection with
QF_LRA/Farkas evidence, explicit Euler replay, exact finite error tables, checked bad
terminal-error and bad Euler-step rejections with QF_LRA/Farkas evidence, and the
ODE/numerical-analysis Lean horizon.
`bounded-dynamics-v0` now also has a standalone bounded recurrence dynamics
lesson for exact trace replay, finite invariant checking, threshold
reachability, checked QF_LRA/Farkas bad transition-step, bad threshold-step, and bad
invariant-bound rejection, and the continuous-dynamics/ODE Lean horizon.
`finite-euler-method-v0` now also has a standalone finite Euler method lesson
for exact explicit-Euler transition replay, finite polynomial-solution error
tables, monotone invariant checking, checked QF_LRA/Farkas bad max-error plus
bad terminal-error and bad-step rejection, and the ODE/numerical-analysis Lean horizon.
`finite-operator-v0` now also has a standalone finite-dimensional operator
lesson for exact `l1` norm replay, row-sum operator-bound replay, finite
Chebyshev recurrence replay, checked QF_LRA/Farkas bad `l1` norm,
bad operator-bound, and bad Chebyshev-prefix rejection, and the
Banach/Hilbert/compact-operator Lean
horizon.
`proof-methods-refutation-v0` now also has a proof-object anatomy lesson that
follows the PHP(3,2) source claim through committed CNF, emitted DRAT/LRAT
proof objects, and same-artifact corrupted-proof rejection.
`linear-optimization-v0` now has a Farkas certificate anatomy lesson that
follows the exact LP threshold conflict through source SMT-LIB, emitted
`UnsatFarkas` evidence, and same-artifact multiplier tamper rejection.
It now also has a standalone linear-optimization page for exact feasible-point
replay, objective-threshold replay, checked QF_LRA/Farkas evidence, and
tampered-certificate rejection.
`finite-probability-v0` now also has a standalone finite-probability
mass-table page for exact PMF normalization, conditional probability replay,
Bayes posterior replay, checked QF_LRA/Farkas bad-normalization rejection,
checked bad-conditional-probability rejection, checked bad-posterior rejection,
finite independence replay, checked bad-independence rejection, total
variation replay, and checked bad-total-variation rejection.
`equivalence-classes-v0` now has an Alethe certificate anatomy lesson that
follows the quotient-map congruence conflict through source SMT-LIB, emitted
zero-trust `UnsatAletheProof` evidence, and same-artifact truncated-proof
rejection.
`modular-arithmetic-v0` now has a Diophantine certificate anatomy lesson that
follows the nonunit inverse obstruction through source SMT-LIB, emitted
`UnsatDiophantine` evidence, same-artifact contradiction-row tamper rejection,
and the sibling incompatible non-coprime CRT row.
`finite-fields-v0` now has a QF_BV bit-blast certificate anatomy lesson that
follows fixed-width finite-field BV rows through source SMT-LIB, generated
DIMACS/DRAT evidence, and same-artifact truncated-DRAT rejection.
The concept atlas now gives these certificate lessons first-class proof-object
anatomy bridge rows for Boolean CNF DRAT/LRAT, QF_LRA/Farkas, QF_UF/Alethe, and
QF_BV bit-blast evidence, so packs can point at shared route vocabulary instead
of repeating the trust-boundary prose locally.
`complex-plane-transforms-v0` now has a learner-facing end-to-end lesson for
unit-root cycle replay, conjugation over products, rational Mobius-transform
replay, checked bad conjugation-product imaginary-part and unit-square
rejections, and the complex-analysis Lean horizon.
`exact-statistical-tests-v0` now has a learner-facing end-to-end lesson for
one-sided exact binomial tails, hypergeometric point probability, one-sided
Fisher tail replay, probability-ordered two-sided Fisher replay, checked
QF_LRA/Farkas bad Fisher and multinomial p-value rejection, a checked QF_LIA
bad tail-count certificate, and the statistical
numerical-honesty horizon.
`metric-continuity-v0` now has a learner-facing end-to-end lesson for finite
metric-table replay, finite Lipschitz checks, epsilon-delta containment,
open-ball preimage replay, checked QF_LRA/Farkas bad-delta and bad-preimage
rejections, and the continuity Lean horizon.
`finite-compactness-v0` now has a learner-facing end-to-end lesson for finite
open-cover replay, subcover replay, minimal-subcover enumeration,
finite-intersection-family replay, checked Bool/CNF bad-cover rejection, and
the compactness Lean horizon.
`finite-connectedness-v0` now has a learner-facing end-to-end lesson for finite
connected-space replay, open-separation replay, clopen-subset disconnection,
checked bad-connectedness rejection, and the connectedness Lean horizon.
`finite-continuous-maps-v0` now has a learner-facing end-to-end lesson for
finite open-preimage replay, continuity checking, homeomorphism replay, checked
bad-continuity rejection, checked bad-homeomorphism rejection, and the
continuous-map Lean horizon.
`finite-simplicial-homology-v0` now has a learner-facing end-to-end lesson for
finite simplicial-complex closure, oriented-boundary replay, `boundary^2 = 0`,
Betti-rank replay over `Q`, checked bad-boundary rejection, a checked QF_LIA
bad-coefficient certificate, and the homology Lean horizon.
`finite-integration-v0` now has a learner-facing end-to-end lesson for finite
simple-function integrals, indicator integrals, integral linearity, checked bad
expectation rejection, and the Lebesgue-integration Lean horizon.
`finite-product-measure-v0` now has a learner-facing end-to-end lesson for
Cartesian-product probability tables, rectangle probabilities, marginals,
finite Fubini replay, checked bad product-probability and bad marginal
rejection, and the Fubini/Tonelli Lean horizon.
`finite-random-variables-v0` now has a learner-facing end-to-end lesson for
finite random-variable functions, pushforward distributions, expectation
through pushforwards, finite independence, checked bad pushforward and bad
expectation-through-pushforward rejection, and the general random-variable
Lean horizon.
`finite-conditional-expectation-v0` now has a learner-facing end-to-end lesson
for finite conditioning partitions, blockwise conditional expectations, total
expectation replay, tower-property replay, conditional-variance decomposition,
checked QF_LRA/Farkas bad table, bad total-expectation, bad tower-property, and
bad variance-decomposition rejection, and the general conditional-expectation
Lean horizon.
`finite-martingales-v0` now has a learner-facing end-to-end lesson for finite
filtrations, adaptedness, martingale conditional-expectation equalities,
square-submartingale inequalities, bounded stopping replay, checked bad
stopped-expectation and martingale rejection with QF_LRA/Farkas evidence, and
the general martingale Lean horizon.
`finite-stochastic-kernels-v0` now has a learner-facing end-to-end lesson for
row-normalized finite kernels, pushforward distributions, joint
factorization/disintegration, kernel composition, checked QF_LRA/Farkas bad
kernel-row rejection, and the regular-conditional-probability Lean horizon.
`finite-hitting-times-v0` now has a learner-facing end-to-end lesson for finite
absorbing-chain first-hit distributions, survival mass, absorption equations,
expected hitting-time equations, checked QF_LRA/Farkas bad survival-mass and
bad expected-time rejection, and the general hitting-theory Lean horizon.
`finite-concentration-v0` now has a learner-facing end-to-end lesson for exact
finite Markov, Chebyshev, and union-bound replay over rational atom tables,
checked bad concentration-bound rejection, and the general concentration Lean
horizon.
`finite-markov-chain-v0` now has a learner-facing end-to-end lesson for exact
row-stochastic transition matrices, finite-horizon distribution replay,
stationary distributions, checked QF_LRA/Farkas bad transition-row and
bad stationary-distribution rejection,
and the Markov-chain convergence Lean horizon.
`generating-functions-v0` now has a learner-facing end-to-end lesson for finite
coefficient extraction, Cauchy product convolution, bounded Fibonacci
generating-function prefix replay, checked bad Cauchy-product rejection, and
the general generating-function Lean horizon.
`graph-reachability-v0` now has a learner-facing end-to-end lesson for finite
BFS shortest-distance replay, deterministic DFS traversal replay, checked
disconnected no-path refutation, and edge-cut separation.
`graph-search-runtime-v0` now has a learner-facing end-to-end lesson for
finite BFS/DFS visited-node counter replay, shortcut-tail family checks,
checked bad DFS-bound rejection, a source-linked QF_LIA arithmetic-DPLL
regression for the bad finite cost bound, and the asymptotic graph-search
runtime Lean horizon. `graph-traversal-runtime-index.md` now ties finite
reachability, deterministic BFS/DFS traces, shortcut-tail visited-node
counters, checked QF_LIA cost refutations, and asymptotic runtime horizons
into one graph learner path.
`graph-matching-v0` now has a learner-facing end-to-end lesson for finite
matching witness replay, overlapping-edge rejection, augmenting-path flip
replay, checked `K3` perfect-matching refutation, and the general matching
theory horizon.
`graph-cut-v0` now has a learner-facing end-to-end lesson for finite
minimum-edge-cut and minimum-vertex-cut certificates, rejected one-cut claims,
checked smaller-cut enumeration, and the general max-flow/min-cut theorem
horizon.
`graph-d-separation-v0` now has a learner-facing end-to-end lesson for finite
active-chain replay, conditioned chain/fork blocking, unconditioned-collider
blocking, descendant-opened collider replay, and the causal-identification
proof horizon.
`counting-v0` now has a learner-facing end-to-end lesson for a fixed
permutation count, one Pascal-identity instance, finite pigeonhole
enumeration, and the Boolean CNF/LRAT proof-upgrade route.
`sequence-limit-shadow-v0` now has a learner-facing end-to-end lesson for
finite epsilon-tail replay, proposed-limit counterexample replay, monotone
bounded prefix checks, geometric partial sums, finite Cauchy-tail
enumeration, bad reciprocal-tail bound rejection, and the general limit Lean
horizon.
`bounded-monotone-sequence-v0` now has a learner-facing end-to-end lesson for
finite monotone-prefix replay, finite prefix supremum, finite tail-gap replay,
checked QF_LRA/Farkas bad upper-bound and bad tail-gap rejections, and the
monotone convergence Lean horizon.
`calculus-algebraic-shadow-v0` and `calculus-riemann-sum-v0` now have a
combined learner-facing end-to-end lesson for polynomial derivative replay,
product-rule and tangent checks, finite Riemann sums, antiderivative endpoint
replay, checked false derivative/integral rejection, and the differentiability,
integrability, and fundamental-theorem Lean horizons.
The next proof/certificate layer is now organized in
[PROOF-UPGRADE-FRONTIER.md](PROOF-UPGRADE-FRONTIER.md): classify the two
`needs-proof-route` packs, then mine CNF/LRAT, QF_LRA/Farkas, QF_UF/Alethe,
QF_LIA/Diophantine, QF_BV bit-blast, and Lean-horizon routes in that order.
The current `needs-proof-route` cleanup is now classified: descriptive
statistics points to finite replay plus QF_LRA/Farkas and QF_LIA/Diophantine
graduation routes, and finite probability points to finite replay plus
QF_LRA/Farkas graduation routes.
The QF_LIA/Diophantine proof-upgrade lane now also has
`exact-statistical-tests-v0` promoted for its bad binomial tail-count row and
`finite-simplicial-homology-v0` promoted for its bad boundary coefficient row,
`induction-patterns-v0` promoted for its finite even-product parity row, and
`descriptive-statistics-v0` promoted for its bad variance and bad contingency
total rows, with
`integer-lia-v0` and `number-theory-v0` now promoted for gcd divisibility
obstructions. The
related LIA arithmetic-DPLL solver-reuse lane also has
`induction-obligations-v0` promoted for its bounded bad-step count row,
`graph-search-runtime-v0` promoted for its bad finite DFS cost-bound row, and
`natural-arithmetic-v0` promoted for its bad bounded negative-domain row.
`cardinality-principles-v0` is now promoted for a QF_LIA/Diophantine
overlap-additivity count contradiction after finite replay computes the true
union count.
The QF_BV/DRAT solver-reuse lane now also has `number-theory-v0` promoted for
its modulo-7 quadratic nonresidue row and a bad square-root witness row, and
`modular-arithmetic-v0` promoted for the fixed-width nonunit-inverse and
modulo-5 Fermat-unit counterexample searches.
The Boolean proof-upgrade lane has its first concrete resource-backed proof
regression: `graph-coloring-v0` now carries a DIMACS CNF artifact for triangle
non-2-colorability, and the CNF crate test emits DRAT, elaborates LRAT, and
checks both proof objects.
`proof-methods-patterns-v0` now carries promoted solver-reuse metadata for the
same CNF/DRAT/LRAT regression pattern on the contradiction row `p`, `p -> q`,
`not q`.
`finite-sets-v0` now carries promoted solver-reuse metadata for the malformed
distributive-law counterexample at element `c`, completing the first Boolean
CNF/LRAT proof-upgrade target set.
`bounded-dynamics-v0` now carries promoted solver-reuse metadata for bad
transition-step, bad threshold-step, and bad invariant-bound rows: exact
recurrence replay computes the local next state `4`, threshold-step state `6`
below threshold `7`, and terminal/max state `8`, and the source QF_LRA
artifacts are checked by the bounded-dynamics `math_resource_lra_routes`
regressions.
The QF_LRA/Farkas lane now has a source-linked solver-reuse promotion for
`rationals-lra-v0`: fixed trichotomy impossible branches and the fixed
order-transitivity violating branch carry SMT-LIB artifacts with Axeyum
`UnsatFarkas` evidence that is independently rechecked.
`linear-algebra-rational-v0` now also routes its singular inconsistent system,
malformed LU product-entry row, and malformed nullspace-component row through
source-linked checked Farkas evidence paths.
`linear-optimization-v0` now routes its infeasible objective-threshold conflict
through a source-linked Axeyum `UnsatFarkas` artifact rather than only
pack-local multiplier replay.
`convexity-rational-v0` now routes its bad midpoint-convexity row through the
same source-linked checked Farkas evidence path after reducing the midpoint
inequality to division-free linear form, and now routes a bad affine-threshold
row through the same path after exact replay computes the shortfall
`1 - g(1/2) = 3/2`.
`finite-concentration-v0` now routes its bad finite tail-bound and bad
union-bound rows through source-linked checked Farkas evidence paths after
finite replay computes the tail probability and the exact event-union
probability, and its metadata promotes those rows for solver reuse.
`finite-probability-v0` now routes its bad normalization row through the same
checked Farkas evidence path after exact replay computes the atom total.
It also routes bad conditional-probability and diagnostic-test Bayes posterior
rows through the same checked Farkas evidence path after exact replay computes
the relevant conditioning, disease-positive, and evidence probabilities.
It now routes a bad finite-independence row through the same checked Farkas
evidence path after exact replay computes `P(heads)=1/2`, `P(red)=1/2`, and
`P(heads and red)=1/4`. It also routes a bad total-variation row through that
path after exact replay computes the atomwise absolute differences, `l1`
distance `1/3`, and `TV=1/6`.
`finite-measure-v0` now routes its bad complement-measure row through the same
checked Farkas evidence path after finite replay computes `mu(A) = 1/3` and
`mu(U) = 1`.
`finite-measure-monotonicity-v0` routes its bad subset-measure and bad
union-subadditivity rows through the same checked Farkas evidence path after
finite replay computes `mu({a}) = 1/6`, `mu({a,b}) = 1/2`, and
`mu(A)+mu(B)=4/3` for the overlapping union witness.
`finite-markov-chain-v0` now routes its bad stochastic-row and
bad stationary-distribution rejections through the same checked Farkas evidence
path after exact replay computes the row sum and the next distribution.
`finite-stochastic-kernels-v0` now routes its bad kernel-row and bad
composition-entry rejections through the same checked Farkas evidence path
after exact replay computes the malformed row sum `3/5 + 3/5 = 6/5` and the
composed transition `(K;L)(rainy, early) = 22/75`.
`finite-hitting-times-v0` now routes its bad survival-mass and bad expected-time
rows through source-linked checked Farkas evidence paths after exact first-hit
replay computes `P(T > 4)=5/16` and clearing denominators in the finite
expected-time equation, and its metadata promotes those rows for solver reuse.
`least-squares-regression-v0` now routes its bad coefficient and bad
RSS-improvement rows through the same checked Farkas evidence path using the
first failed normal equation and exact mean-baseline RSS replay.
`real-analysis-rational-v0` now routes its bad linear-delta row through the
same checked Farkas evidence path using the final output-bound contradiction.
`bounded-monotone-sequence-v0` now routes its bad upper-bound row through the
same checked Farkas evidence path after exact finite-prefix replay computes
`a_6 = 6/7`, and now routes its bad finite tail-gap row after exact replay
computes `a_2 = 2/3` and gap excess `1/12`.
`finite-recurrence-prefix-v0` now routes its bad finite-value and bad
affine-step rows through the same checked Farkas evidence path after exact
recurrence replay computes `F_6 = 8` and `x_4 = 15` instead of the malformed
affine claim `14`.
`finite-root-finding-v0` now routes its bad Newton-step and bad
bisection-width rows through the same checked Farkas evidence path after exact
replay computes the next iterate `17/12` and the selected width `1/2`.
`finite-separation-v0` now routes its bad convex-combination and bad separator
rows through the same checked Farkas evidence path after exact convex-hull
replay computes point `(1/3,1/3)` and separator replay computes the outside
score `4`.
`finite-kkt-v0` now routes its bad stationarity and bad complementarity rows
through the same checked Farkas evidence path after exact KKT replay computes
stationarity residual `-1`, stationarity error `1`, complementary-slackness
product `0`, and complementarity error `1`.
`finite-active-set-qp-v0` now routes its bad free-gradient, bad inactive-slack,
and bad degenerate-multiplier rows through the same checked Farkas evidence path
after exact active-face replay computes free-coordinate stationarity error `2`,
inactive lower-bound slack `1`, and degenerate active-bound replay computes
false positive-multiplier error `1`.
`finite-sdp-v0` now routes its bad objective, bad duality-gap, and bad
slack-entry rows through
the same checked Farkas evidence path after exact SDP replay computes objective
value `1`, dual objective `1`, objective error `1`, gap error `1/2`, and
bottom-right slack-entry gap `1/2`.
`finite-gradient-descent-v0` now routes its bad decrease, bad step-coordinate,
and bad descent-bound rows through the same checked Farkas evidence path after
exact descent-step replay computes decrease `11/4`, decrease error `3/4`,
`next_x = 1/2`, and descent slack `1/4`.
`finite-line-search-v0` now routes its bad Armijo, bad descent-direction, and
bad accepted-candidate rows through the same checked Farkas evidence path after
exact line-search replay computes rejected-step violation `1`, directional
derivative `-4`, and accepted point `0`.
`finite-wolfe-line-search-v0` now routes its bad minimizer, bad
sufficient-decrease, and bad curvature rows through the same checked Farkas
evidence path after exact Wolfe replay computes minimizer `alpha=1/2`,
sufficient-decrease slack `1/2`, and curvature violation `2`.
`finite-projected-gradient-v0` now routes its bad projection and bad
projected-decrease rows through the same checked Farkas evidence path after
exact interval-projection replay rejects `3/2` for the interval `[0,1]` and
exact objective replay computes projected decrease `3`.
`finite-proximal-gradient-v0` now routes its bad proximal point row through the
same checked Farkas evidence path after exact L1 soft-threshold replay computes
residual `-3/2` for the malformed point.
`polynomial-factorization-rational-v0` now routes its fixed
irreducible-quadratic discriminant row through the same checked Farkas evidence
path after exact replay computes `D = -4`.
`reals-rcf-shadow-v0` now routes its fixed negative-discriminant no-real-root
row through the same checked Farkas evidence path after exact replay computes
`D = -4`, while keeping square-nonnegativity and general SOS/CAD/RCF proof
routes distinct.
`finite-conditional-expectation-v0` now routes its bad high-block,
total-expectation, tower-property, and variance-decomposition tables through
source-linked checked Farkas evidence paths using the denominator-cleared
block-average contradiction, the law-of-total-expectation scalar contradiction,
the scalar tower-value contradiction, and the total-variance decomposition
contradiction, and its metadata promotes all four rows for solver reuse.
`finite-euler-method-v0` now routes its bad fixed-step transition, bad
terminal-error, and bad max-error bound through source-linked checked Farkas
evidence paths after exact derivative and finite error-table replay, and its
metadata promotes those rows for solver reuse.
`orientation-area-geometry-v0` now routes its bad affine-area-scaling and bad
fixed-orientation rows through the same checked Farkas evidence path after
exact signed-area replay.
`incidence-geometry-v0` now routes its bad intersection-coordinate and bad
point-on-line rows through the same checked Farkas evidence path after exact
line-intersection and line-value replay.
`rigid-configuration-geometry-v0` now routes its bad translation-image and bad
distance-table rows through the same checked Farkas evidence path after exact
translation and squared-distance replay.
`numerical-linear-algebra-v0` now routes its bad residual-bound, solution-box
upper-bound, and Jacobi error-bound rows through the same checked Farkas
evidence path after exact residual-norm, solution-box, and iteration replay.
`random-matrix-finite-v0` now routes its bad trace-square and expected-rank
rows through the same checked Farkas evidence path after exact finite moment
and rank replay.
`affine-geometry-v0` now routes its bad midpoint-coordinate,
collinearity-determinant, and distance-preservation rows through the same
checked Farkas evidence path after exact affine-midpoint, collinearity, and
squared-distance replay.
`finite-circle-geometry-v0` now routes its bad radius and bad
line-intersection rows through the same checked Farkas evidence path after
exact coordinate replay computes squared radius `2` for the malformed
unit-circle point and right-intersection x-coordinate `1` for the malformed
horizontal diameter claim.
`finite-inversion-geometry-v0` now routes its bad inverse-coordinate and bad
inverse-distance-product rows through the same checked Farkas evidence path
after exact inversion replay computes inverse x-coordinate `2/5` and
squared-radius product `1` for the malformed unit-circle inversion claims.
`finite-cyclic-geometry-v0` now routes its bad diagonal-intersection, bad
opposite-angle, and bad Ptolemy rows through the same checked Farkas evidence
path after exact cyclic-configuration replay computes intersection
x-coordinate `0`, angle dot product `0`, and Ptolemy right-hand side `25` for
the malformed cyclic quadrilateral claims.
`inner-product-spaces-rational-v0` now routes its bad inner-product and bad
projection-orthogonality rows through the same checked Farkas evidence path
after exact negative-norm and projection residual replay.
`spectral-linear-algebra-v0` now routes its bad Rayleigh-quotient and bad
eigenpair rows through the same checked Farkas evidence path after exact
quotient and matrix-vector replay.
`matrix-invariants-v0` now routes its bad trace and bad
characteristic-polynomial rows through the same checked Farkas evidence path
after exact trace and witness-root replay.
The matrix-corpus regression pass now proves the committed SMT-LIB artifacts
directly for least-squares bad coefficients, numerical residual bounds, finite
random-matrix trace-square moments, spectral bad eigenpairs, and matrix
bad-characteristic rows; the inner-product negative-norm row remains on its
existing inline Farkas route until the strict-inequality artifact shape is
accepted by the SMT-LIB parser/evidence path.
`calculus-algebraic-shadow-v0` now routes its false derivative-value row
through the same checked Farkas evidence path after exact polynomial derivative
replay computes the derivative at the fixed point.
`complex-plane-transforms-v0` now routes its bad conjugation-product
imaginary-part and bad unit-square real-part rows through the same checked
Farkas evidence path after exact real-pair replay computes
`conjugate(z*w) = conjugate(z)*conjugate(w) = 5 - 5i` and `i^2 = -1`.
The structured atlas now records these recurring exact-rational contradictions
as `family_exact_rational_farkas`, scoped to the optimization/Farkas
proof-route lane and backed by the shared
`math_resource_lra_routes` regression.
The structured atlas now also records recurring finite Boolean CNF/LRAT
refutations as `family_boolean_cnf_lrat`, spanning logic, counting, graph,
finite-set, and finite-topology packs backed by the shared
`math_resource_boolean_routes` regression.
Recurring integer/count obstructions now also have `family_integer_diophantine`,
spanning number theory, induction, counting, statistics, graph-search,
polynomial, and homology packs backed by the shared `math_resource_lia_routes`
regression.
Recurring fixed-width finite algebra, residue, and one-bit graph encodings now
also have `family_fixed_width_bv_drat`, spanning finite fields, finite rings,
graph coloring, and bounded number-theory residue search/bad-witness packs
backed by the shared `math_resource_bv_routes` regression.
The rules/law transfer lane now has five concrete packs beyond the crosswalk:
`authorization-policy-v0` reuses finite predicates, tenant/resource relations,
explicit deny precedence, bounded version-delta witnesses, and checked
Bool/QF_LIA evidence for tenant isolation, deny precedence, admin tenant
boundaries, and implementation equivalence; `tax-benefit-arithmetic-v0` reuses
integer thresholds, household-size adjustments, caps, active phase-out
monotonicity, effective-date witnesses, and checked Bool/QF_LIA evidence for
non-negative benefit, cap, active phase-out monotonicity, and bounded
implementation equivalence, while the rules validator replays the full
piecewise finite sample; `procurement-scoring-v0` reuses finite predicate
exclusions, bid caps, deadline arithmetic, small-business bonus-threshold
witnesses, score monotonicity, and checked Bool/QF_LIA evidence for debarment,
late submission, bid-cap, score-monotonicity, and bounded
implementation-equivalence obligations; `grant-allocation-v0` reuses exact
rational shares, budget balance, shelter/clinic minimum floors,
administrative caps, finite allocation witnesses, and checked QF_LRA/Farkas
evidence for total-budget, minimum-share, cap, and bounded
implementation-equivalence obligations.
The rules/law lane now also has a generated
[`rules-query-dashboard.md`](../rules-as-code/generated/rules-query-dashboard.md)
that reads the committed rule-pack JSON and exposes 1,007 bounded sample rows,
links deterministic generated query-row JSON under
[`generated/queries/`](../rules-as-code/generated/queries/), and replays 1,766
coverage, equivalence, threshold, cap, deadline, version-delta, monotonicity,
and rational-allocation rows through the rules validator.
[`RULES-LAW-QUERIES.md`](RULES-LAW-QUERIES.md) now exposes the same boundary
through copyable `scripts/query-rules-as-code.py` commands for summary counts,
pack lookup, checked obligations, generated query families, and bounded row
inspection; `just rules-as-code` smoke-checks those queries.
The consumer query layer now also exposes topology readiness:
`CONSUMER-QUERIES.md` shows the Boolean/Diophantine field summaries,
metric/compactness/preimage/closure/homeomorphism/specialization/boundary/homology
bridge lookups, concept queries for metric-ball, bounded epsilon-delta,
finite topology-operator/homeomorphism,
finite specialization-order, finite boundary-operator, and finite homology
rows, and checked
Boolean/Alethe/Diophantine topology row drill-downs. The
foundational-resource smoke check runs those same queries so finite topology
axioms, finite open-cover and connectedness refutations, closure/interior
replay, finite homeomorphism replay, finite specialization preorder replay,
continuous-map preimage consistency, finite boundary-operator and homology
checks, metric-ball examples, and bounded epsilon-delta shadows stay visible
through the public JSON boundary without promoting arbitrary compactness,
connectedness, specialization-order theorems, homeomorphism invariance,
homology invariance, exact sequences, or cohomology theorems.
The consumer query layer now also exposes statistics readiness:
`CONSUMER-QUERIES.md` shows the Farkas field summary, finite-table and
tail-count bridge lookups, random-matrix bridge lookups, concept-scoped
`bridge_random_matrix_finite_moment` pack and checked-row drill-downs, and
checked Farkas/Diophantine statistics row drill-downs. The
foundational-resource smoke check runs those same queries so exact finite
tests, contingency tables, least-squares RSS/normal-equation rows, random-matrix finite
moments, finite probability/process tables, concentration rows, and
stochastic-kernel checks stay visible through the public JSON boundary without
promoting floating-point inference, asymptotic sampling, MCMC, VI,
model-calibration claims, random-matrix asymptotics, universality, simulation
quality, or high-dimensional limit laws.
The consumer query layer now also exposes linear-algebra readiness:
`CONSUMER-QUERIES.md` shows Farkas and Alethe field summaries, rank and
projection bridge lookups, and checked exact-rational/equality-heavy
linear-algebra row drill-downs. The foundational-resource smoke check runs
those same queries so rational systems, residual bounds, least-squares RSS rows,
eigenpair checks, matrix invariants, finite vector spaces, dual spaces,
modules, tensors, geometry dot products, finite SDP/KKT/active-set rows, and
matrix-process equations stay visible through the public JSON boundary without
promoting spectral-theorem, conditioning/stability, or general
vector-space/module theorem claims.
The consumer query layer now also exposes core algebra, number-theory, and
graph-theory readiness: `CONSUMER-QUERIES.md` shows abstract-algebra Alethe
field summaries, homomorphism/ideal bridge lookups, checked Alethe and
concept-scoped homomorphism-preservation Alethe rows, fixed-width QF_BV
finite-algebra rows, set/foundations and discrete finite-Boolean-algebra
Boolean route drill-downs, number-theory Diophantine field summaries with
finite-family lookups and checked integer-arithmetic rows, and graph-theory
Boolean and LIA field summaries with checked finite coloring, reachability,
matching, cut, d-separation, and BFS/DFS runtime-counter rows.
The foundational-resource
smoke check runs those same queries so the core curriculum lanes are visible
through the public JSON boundary without promoting arbitrary algebraic
structure theorems, unbounded number-theory claims, asymptotic graph
algorithms, or general graph theorems.
The consumer query layer now also exposes analysis, numerical-analysis, and
complex-analysis readiness: `CONSUMER-QUERIES.md` shows real-analysis Farkas
field summaries, epsilon/gradient bridge lookups, checked bounded-analysis
row drill-downs, numerical-analysis Farkas field summaries, residual/operator
bridge lookups, checked exact numerical row drill-downs, complex-analysis
Farkas field summaries, real-pair bridge lookup, and checked algebraic complex
row drill-downs. The foundational-resource smoke check runs those same
queries so bounded real-analysis shadows, exact derivative/integral and
root-finding rows, residual/Euler/operator/recurrence/optimization-step rows,
and real-pair complex algebra stay visible through the public JSON boundary
without promoting completeness, convergence, floating-point stability,
holomorphic, analytic-continuation, or theorem-level calculus claims.
The consumer query layer now also exposes foundations, discrete-math, and
probability readiness: `CONSUMER-QUERIES.md` shows logic/proof Boolean field
summaries, proof-vocabulary lookups, checked proof-pattern/CNF rows,
set-theory/foundations Alethe field summaries, partition bridge lookups,
checked finite relation/function/quotient rows, discrete-math Diophantine
field summaries, finite-family lookups, checked counting/coefficient/tail-count
rows, probability-theory Farkas field summaries, probability-table bridge
lookups, and checked finite probability/process row drill-downs. The
foundational-resource smoke check runs those same queries so the first
curriculum and finite-probability lanes are visible through the public JSON
boundary without promoting proof automation, ZFC/infinite set theory,
asymptotic combinatorics, continuous probability, stochastic-process limits, or
theorem-level probability claims.
The consumer-boundary layer now also has
[`FIELD-READINESS-QUERY-MATRIX.md`](FIELD-READINESS-QUERY-MATRIX.md), a compact
18-field table for downstream consumers. Each row records the current
pack/check counts, the smoke-checked readiness route, bridge lookup terms,
checked-row drilldown, and the theorem-horizon boundary to avoid overclaiming.
This is still a documentation layer over committed JSON and
`query-foundational-resources.py`, not a new crate, typed API, or repository
split.
The matrix-resource consumer layer now also has
[`MATRIX-COMPUTATION-QUERIES.md`](MATRIX-COMPUTATION-QUERIES.md), and
`query-foundational-resources.py` supports exact atlas concept filters on
`packs` and `checks`. This makes LU, residual, rank/nullity, eigenpair,
random-matrix, tensor/module, operator, and Chebyshev rows discoverable by
bridge concept plus proof route while preserving the JSON-first R6 boundary.
The probability/statistics consumer layer now also has
[`PROBABILITY-STATISTICS-QUERIES.md`](PROBABILITY-STATISTICS-QUERIES.md). The
guide and resource smoke expose probability-mass, finite-measure,
product/integration, pushforward, conditional-expectation, stochastic-kernel,
tail-count, and random-matrix moment bridge concepts through concept-scoped
Farkas queries, making exact finite-table rows discoverable while keeping
continuous probability, asymptotic statistics, stochastic-process limits,
simulation quality, and floating-point inference claims in proof-horizon or
numerical-honesty lanes.
The measure-theory consumer layer now also has
[`MEASURE-THEORY-QUERIES.md`](MEASURE-THEORY-QUERIES.md). The guide and
resource smoke expose finite measure additivity, complement, monotonicity,
subadditivity, product measure, marginals, integration, pushforward,
conditional expectation, martingale/stopped expectation, stochastic-kernel,
hitting-time, and concentration rows through concept-scoped and pack-scoped
Farkas queries, making finite measure resources discoverable while keeping
sigma-algebra construction, countable additivity, Lebesgue measure,
product-measure existence, convergence theorems, almost-everywhere reasoning,
stochastic-process limits, simulation quality, and floating-point claims in
the horizon lanes.
The topology/homology consumer layer now also has
[`TOPOLOGY-HOMOLOGY-QUERIES.md`](TOPOLOGY-HOMOLOGY-QUERIES.md). The guide and
resource smoke expose metric, bounded epsilon-delta, compactness,
connectedness, topology-operator/homeomorphism, quotient, specialization,
boundary/homology, torsion, cohomology, universal-coefficient, and cup-product
bridge concepts through route-scoped Boolean, Farkas, Alethe, Diophantine, and
QF_BV queries, making finite topology rows discoverable while keeping general
topology and algebraic-topology theorem claims in the proof-horizon lane.
The finite-algebra consumer layer now also has
[`ALGEBRA-STRUCTURE-QUERIES.md`](ALGEBRA-STRUCTURE-QUERIES.md). The guide and
resource smoke expose homomorphism, group-action, module-action, ideal, and
modular residue bridge concepts through Alethe/QF_BV pack/check queries,
making finite algebra rows discoverable while keeping arbitrary algebraic
structure theorems in the proof-horizon lane.
The number/arithmetic consumer layer now also has
[`NUMBER-ARITHMETIC-QUERIES.md`](NUMBER-ARITHMETIC-QUERIES.md). The guide and
resource smoke expose gcd/divisibility, modular CRT/inverse, QF_BV bit-blast,
totality, ideal/quotient, and exact-vs-floating bridge concepts through
Diophantine, QF_BV, Alethe, and Farkas queries, making finite arithmetic rows
discoverable while keeping analytic number theory, algebraic number theory,
unbounded induction, and floating-point guarantees in the proof-horizon or
numerical-honesty lanes.
The finite-geometry consumer layer now also has
[`GEOMETRY-RESOURCE-QUERIES.md`](GEOMETRY-RESOURCE-QUERIES.md). The guide and
resource smoke expose `bridge_coordinate_orientation_geometry` and
`bridge_finite_circle_inversion_cyclic_replay` through concept-scoped Farkas
pack/check queries, making coordinate/incidence/rigid/affine/orientation rows
and circle/inversion/cyclic rows discoverable while keeping broad geometry
theorems in the proof-horizon lane.
The graph/discrete consumer layer now also has
[`GRAPH-DISCRETE-QUERIES.md`](GRAPH-DISCRETE-QUERIES.md). The guide and
resource smoke expose `bridge_finite_graph_replay_obstruction` through
concept-scoped Boolean, QF_BV, and LIA pack/check queries, making finite
coloring, reachability, matching, cut, d-separation, fixed-width coloring, and
BFS/DFS runtime rows discoverable while keeping general graph theorems and
asymptotic algorithm claims in the proof-horizon lane.
The optimization/convexity consumer layer now also has
[`OPTIMIZATION-CONVEXITY-QUERIES.md`](OPTIMIZATION-CONVEXITY-QUERIES.md). The
guide and resource smoke expose LP objective/Farkas rows, rational convexity
shadows, projection/residual rows, exact-vs-floating boundary rows, and
pack-specific KKT, active-set QP, SDP, gradient-descent, Armijo/Wolfe
line-search, projected-gradient, and proximal-gradient rows through
concept-scoped or pack-scoped Farkas queries, making finite optimization
resources discoverable while keeping duality, KKT sufficiency, SDP strong
duality, convergence, stability, and benchmark claims in the horizon lanes.
The functional-analysis/operator consumer layer now also has
[`FUNCTIONAL-OPERATOR-QUERIES.md`](FUNCTIONAL-OPERATOR-QUERIES.md). The guide
and resource smoke expose finite operator/Chebyshev rows, eigenpair and
Rayleigh rows, inner-product/projection rows, and finite dual/tensor equality
rows through concept-scoped Farkas and Alethe queries, making finite
functional/operator resources discoverable while keeping Banach/Hilbert-space,
compact-operator, topological-dual, minimax, Haar-space, alternation-theorem,
stability, and infinite-dimensional approximation claims in the horizon lanes.
The analysis/numerical/complex consumer layer now also has
[`ANALYSIS-NUMERICAL-QUERIES.md`](ANALYSIS-NUMERICAL-QUERIES.md). The guide and
resource smoke expose bounded epsilon-delta and metric-ball rows, algebraic
derivative/integral rows, Newton/root-finding rows, finite dynamics/Euler rows,
residual and numerical-linear-algebra rows, exact-vs-floating boundary rows,
and complex real-pair rows through concept-scoped or pack-scoped Farkas
queries, making finite analysis resources discoverable while keeping
completeness, IVT/MVT/FTC, convergence, numerical stability, floating-point
error, holomorphicity, contour-integration, analytic-continuation, and
algebraic-closure claims in the horizon lanes.
The dynamics consumer layer now also has
[`DYNAMICS-QUERIES.md`](DYNAMICS-QUERIES.md). The guide and resource smoke
expose finite recurrence, transition, invariant, Euler, stochastic-kernel,
Markov-chain, hitting-time, and calculus-shadow rows through concept-scoped
and pack-scoped Farkas queries, making finite dynamics resources discoverable
while keeping continuous ODE/PDE theory, flow/stability/bifurcation theorems,
chaos/ergodic theory, Euler convergence, stochastic-process limits,
continuous-time Markov processes, numerical stability, and floating-point
claims in the horizon lanes.
The foundations/discrete consumer layer now also has
[`FOUNDATIONS-DISCRETE-QUERIES.md`](FOUNDATIONS-DISCRETE-QUERIES.md). The
guide and resource smoke expose Boolean proof/CNF rows, refutation-as-query
rows, finite proof-pattern rows, bounded induction and arithmetic obligations,
finite quantifier rows, finite cardinality/bijection rows, finite Boolean
algebra rows, finite counting rows, partition/equivalence rows, and finite
relation/function/image/preimage rows through Boolean, Alethe, Diophantine, and
LIA queries, making finite foundations resources discoverable while keeping
proof automation, ZFC, infinite sets/cardinality, unbounded induction,
asymptotic enumeration, and broad combinatorial theorem families in the
horizon lanes.
The proof-route consumer layer now also has
[`PROOF-ROUTE-QUERY-MATRIX.md`](PROOF-ROUTE-QUERY-MATRIX.md), and
`query-foundational-resources.py routes` summarizes route coverage from
proof-cookbook recipe links. The smoke check exercises Boolean, QF_BV,
QF_LIA/Diophantine, QF_LRA/Farkas, QF_UF/Alethe, and Lean-horizon route
queries, including field-scoped route summaries, without adding a typed API.
The consumer query layer now also exposes optimization/convexity readiness:
`CONSUMER-QUERIES.md` shows the Farkas field summary, LP-objective and
convexity bridge lookups, and checked optimization/convexity Farkas row
drill-downs. The foundational-resource smoke check runs the same queries so
exact LP thresholds, finite convexity shadows, least-squares normal equations
and RSS rows, gradient/Hessian replay, KKT stationarity/complementarity replay,
finite active-set QP replay,
finite SDP objective/slack/gap replay, finite gradient-descent replay, finite
line-search replay, residual bounds, finite Wolfe line-search replay, finite
projected-gradient replay, finite proximal-gradient replay, and
matrix witnesses stay visible through the public JSON boundary without
promoting duality, KKT sufficiency, SDP strong duality, gradient-descent,
line-search, active-set method theory, Wolfe line-search, projected-gradient
convergence, proximal-gradient convergence, or convergence-theorem claims.
The consumer query layer now also exposes functional-analysis/operator
readiness: `CONSUMER-QUERIES.md` shows the Farkas field summary,
operator/Chebyshev bridge lookup, concept-scoped
`bridge_finite_operator_chebyshev` pack and checked-row drill-downs, and
checked finite-operator norm/bound/Chebyshev-prefix, inner-product, Chebyshev, spectral, and
characteristic-polynomial Farkas rows. The foundational-resource smoke check
runs those same queries so finite-dimensional operator bounds, inner-product
positivity and projection-orthogonality, finite Chebyshev-prefix conflicts,
Chebyshev duplicate-node grids,
interpolation/residual rows, alternation-magnitude refutations,
spectral/eigenpair witnesses,
characteristic-polynomial arithmetic, and
dual-space rows remain visible through the public JSON boundary without
promoting Banach, Hilbert, compact-operator, Haar-space, minimax, alternation,
or infinite-dimensional approximation theorem claims.
The learner layer now also has
[`matrix-computation-index.md`](../learn/math/matrix-computation-index.md),
which groups LU, rank/nullity, residual, projection, eigenpair,
characteristic-polynomial, finite random-matrix, chain-complex, operator,
module, and tensor rows by replay, QF_LRA/Farkas, QF_UF/Alethe,
QF_LIA/Diophantine, Lean-horizon, and numerical-honesty boundaries.
The learner layer now also has
[`chebyshev-operator-index.md`](../learn/math/chebyshev-operator-index.md),
which groups finite operator bounds, Chebyshev recurrence values,
bad Chebyshev-prefix values, Vandermonde interpolation matrices, alternating residuals, spectral rows, and
characteristic-polynomial arithmetic by exact replay, QF_LRA/Farkas evidence,
and functional-analysis theorem horizons.
The learner layer now also has
[`random-matrix-moment-index.md`](../learn/math/random-matrix-moment-index.md),
which groups finite matrix-valued atom tables, exact trace/determinant
moments, expected Gram matrices, rank-mixture probabilities, checked
QF_LRA/Farkas bad trace-square and expected-rank evidence, and random-matrix
asymptotic or simulation horizons.
The learner/planning layer now also has
[`matrix-corpus-benchmark-boundary.md`](../learn/math/matrix-corpus-benchmark-boundary.md),
which separates educational matrix resources, solver regressions,
benchmark-corpus rows, and theorem-horizon claims before any matrix row is used
for solver-reuse, performance, or parity language.
The learner/planning layer now also has
[`analysis-calculus-theorem-horizon-map.md`](../learn/math/analysis-calculus-theorem-horizon-map.md),
which maps real completeness, IVT/MVT/FTC, compactness, convergence,
root-finding, optimization, measure/probability, functional-analysis/operator,
and dynamics finite shadows to checked evidence routes, missing Lean/theorem
dependencies, and next build artifacts without counting finite checks as
general theorem proofs.
The learner/planning layer now also has
[`real-completeness-theorem-boundary.md`](../learn/math/real-completeness-theorem-boundary.md),
which expands the real-completeness row into a concrete dependency ledger:
least-upper-bound completeness, Cauchy completeness, monotone convergence,
RCF shadows, metric continuity, and compactness prerequisites are linked to
existing checked packs, copyable queries, replay commands, missing Lean
dependencies, and graduation criteria while keeping finite samples separate
from theorem-level real-analysis claims.
The learner/planning layer now also has
[`algebra-equality-certificate-boundary.md`](../learn/math/algebra-equality-certificate-boundary.md),
which turns the algebra queue rule into an explicit promotion boundary:
finite table replay must find the concrete equality, congruence, closure,
representative, preservation, identity-action, action-compatibility, or
bilinearity conflict before
a scoped QF_UF/Alethe certificate row can graduate. It links finite groups,
monoids, permutation groups, group actions, homomorphisms, ideals, vector
spaces, dual spaces, modules, and tensor products to copyable concept, pack,
checked-row, and replay commands while keeping general algebraic theorem
claims in the Lean-horizon lane.
The number-system concept layer now also has `bridge_gcd_divisibility_witness`.
It groups gcd/common-divisor replay, Bezout replay, quotient witnesses,
modular nonunit obstructions, and checked gcd non-divisibility certificates
across `gcd-bezout-v0`, `integer-lia-v0`, `modular-arithmetic-v0`, and
`number-theory-v0`, and the foundational-resource smoke check now exercises
the number-theory gcd concept lookup through the public JSON/query boundary.
The number-system concept layer now also has
`bridge_modular_crt_inverse_witness`. It groups concrete CRT congruence
witnesses, modular inverse witnesses, fixed residue searches, finite-field
unit/nonunit contrasts, quotient-ring-adjacent vocabulary, and checked nonunit
Diophantine evidence across `modular-arithmetic-v0`, `number-theory-v0`,
`finite-fields-v0`, and `finite-ideals-v0`. The foundational-resource smoke
check now exercises the number-theory CRT concept lookup through the public
JSON/query boundary while keeping full CRT, arbitrary field theory, and
quotient-ring theorem claims in the horizon lane.
The discrete/counting concept layer now also has
`bridge_finite_counting_replay`. It groups permutation/Pascal rows,
pigeonhole proof routes, double-counting tables, coefficient extraction,
finite orbit-count replay, and exact finite tail-count contradictions across
`counting-v0`, `proof-methods-refutation-v0`, `cardinality-principles-v0`,
`generating-functions-v0`, `finite-group-actions-v0`, and
`exact-statistical-tests-v0`. The foundational-resource smoke check now
exercises discrete-math counting lookup plus concept-scoped Boolean and
Diophantine route queries while keeping asymptotic counting and unbounded
combinatorics in the horizon lane.
The finite Boolean-algebra concept layer now also exposes the
`finite-order-lattices-v0` false top-element row alongside finite-set and
finite-topology set-family contradictions. The foundational-resource smoke
check exercises concept-scoped Boolean queries for
`bridge_finite_boolean_algebra`, keeping powerset/lattice replay concrete
while leaving arbitrary order/lattice and infinite Boolean-algebra theorems in
the horizon lane.
The topology concept layer now also has
`bridge_finite_topology_operator_homeomorphism`. It groups finite topology
axiom replay, closure/interior replay, continuity by open preimage, finite
homeomorphism replay, checked malformed-topology Bool/CNF rows, and checked
malformed-preimage QF_UF/Alethe rows across `finite-topology-v0`,
`finite-continuous-maps-v0`, `finite-compactness-v0`, and
`finite-connectedness-v0`. The foundational-resource smoke check now exercises
topology closure/homeomorphism lookup plus concept-scoped Alethe route queries
while keeping closure-operator theorems, homeomorphism invariance,
compactness/connectedness preservation, homology invariance, and general
topology in the horizon lane.
The topology concept layer now also has
`bridge_finite_specialization_order_replay`. It groups finite topology to
preorder replay, singleton-closure characterization, finite `T0` antisymmetry
replay, and checked bad `T0` QF_UF/Alethe evidence across
`finite-specialization-order-v0`, `finite-topology-v0`, and finite
relations/functions vocabulary. The foundational-resource smoke check now
exercises topology specialization lookup plus concept-scoped Alethe route
queries while keeping T0 quotients, sobriety, Alexandroff-space/domain-theory
results, and arbitrary-space specialization-order theorems in the horizon lane.
The topology concept layer now also has
`bridge_finite_boundary_operator_replay`. It groups oriented boundary
coefficients, boundary-of-boundary cancellation, boundary-matrix shape, and
checked bad-boundary coefficient plus boundary-square cancellation evidence across
`finite-simplicial-homology-v0`. The foundational-resource smoke check now
exercises topology boundary lookup plus concept-scoped Diophantine route
queries while keeping functoriality, exactness, homology invariance,
cohomology-operation laws, and general algebraic topology in the horizon lane.
The topology concept layer now also has `bridge_finite_cohomology_replay`. It
groups finite F2 cochain coboundary replay, `delta^2 = 0`,
cohomology-rank replay, non-coboundary cocycle checking, and checked bad
coboundary-value QF_UF/Alethe evidence across
`finite-simplicial-cohomology-v0`. The foundational-resource smoke check now
exercises topology cohomology lookup plus concept-scoped Alethe route queries
while keeping cohomology functoriality, cohomology-operation laws, universal
coefficients, de Rham comparison, sheaf cohomology, duality, and invariance
theorems in the horizon lane.
The topology concept layer now also has `bridge_finite_cup_product_replay`. It
groups ordered F2 cup-product replay, one finite coboundary-Leibniz row, and
checked bad cup-product QF_BV/DRAT evidence across
`finite-simplicial-cup-products-v0`. The foundational-resource smoke check now
exercises topology cup lookup plus concept-scoped QF_BV route queries while
keeping associativity, graded commutativity, naturality, cohomology-ring
quotienting, universal coefficients, and invariance theorems in the horizon
lane.
The topology concept layer now also has
`bridge_finite_torsion_homology_replay`. It groups one finite integer chain
complex, one-entry Smith diagonal replay, `H0 = Z/2`, and checked bad
torsion-generator QF_LIA/Diophantine evidence across
`finite-chain-complex-torsion-v0`. The foundational-resource smoke check now
exercises topology torsion lookup plus concept-scoped Diophantine route queries
while keeping general Smith normal form, universal coefficients, Ext/Tor
functor laws, exact sequences, and homology invariance in the horizon lane.
The topology concept layer now also has
`bridge_finite_universal_coefficient_shadow`. It groups one dual integer
cochain complex, `H^1 = Z/2`, degree-one Hom/Ext bookkeeping, and checked bad
`H^1 = 0` QF_UF/Alethe evidence across
`finite-universal-coefficient-shadow-v0`. The foundational-resource smoke check
now exercises topology universal-coefficient lookup plus concept-scoped Alethe
route queries while keeping the universal coefficient theorem, naturality,
splitting choices, Ext/Tor laws, exact sequences, and invariance in the
horizon lane.
The KKT optimization pack now also has a second source-linked checked
QF_LRA/Farkas row: `bad-kkt-complementarity-rejected` in `finite-kkt-v0`.
Exact replay computes `lambda * (x - bound) = 0` for the boundary quadratic
witness while the malformed row claims product `1`, so the resource now covers
both stationarity and complementary-slackness refutations without claiming
general KKT sufficiency or constraint-qualification theorems.
The projected-gradient optimization pack now also has a second source-linked
checked QF_LRA/Farkas row: `bad-projected-decrease-rejected` in
`finite-projected-gradient-v0`. Exact replay computes `f(0) = 4`, `f(1) = 1`,
and projected decrease `3`, while the malformed row claims decrease `4`, so the
resource now covers both projection-feasibility and projected-decrease
refutations without claiming projected-gradient convergence or rate theorems.
The concept atlas now also has a bounded-family/asymptotic boundary bridge:
`bridge_bounded_family_asymptotic_boundary` groups finite BFS/DFS runtime
counters, finite recurrence prefixes, fixed coefficient windows, bounded
dynamics traces, and finite Euler error rows under one queryable concept. It
keeps exact finite replay plus checked LIA/Farkas rows separate from
asymptotic runtime, closed-form recurrence, convergence-rate, and limiting
theorem claims.
The concept atlas now also has a polynomial coefficient/factor replay bridge:
`bridge_polynomial_coefficient_factor_replay` groups fixed coefficient tuples,
division and factor witnesses, finite coefficient windows, root-finding steps,
derivative shadows, and rational polynomial-geometry obligations under one
queryable concept. Concept-scoped Diophantine and Farkas queries now return
checked rows while general factorization, algebraic closure, root distribution,
and generating-function convergence remain proof-horizon work.
The finite vector-space pack now also splits its bad-subspace closure evidence:
`bad-subspace-rejected` remains the exact finite replay row that computes
`10 + 01 = 11` outside `{00,10,01}`, while
`qf-uf-bad-subspace-addition-closure` owns the checked QF_UF/Alethe
membership-conflict artifact and direct pack/route/text query.
Continue by adding the next curriculum-adjacent pack from the field ledger
or by replacing finite enumeration routes with emitted, checked proof objects
where appropriate.

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
