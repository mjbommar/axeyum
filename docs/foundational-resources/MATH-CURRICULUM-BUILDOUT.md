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
| `proof-methods` | `logic_and_proof` | `proof-methods-refutation-v0`, `proof-methods-patterns-v0` | Negate-and-decide examples, direct proof, contrapositive, proof by cases, contradiction, and invalid-proof counterexamples. |
| `induction` | `logic_and_proof`, `number_theory` | `induction-obligations-v0`, `induction-patterns-v0` | Bounded base/step obligations, weak/strong induction prefixes, loop invariants, bad-step counterexamples; general induction marked Lean-horizon. |
| `sets` | `set_theory_and_foundations` | `finite-sets-v0` | Membership, subset, union/intersection, finite identities. |
| `relations-and-functions` | `set_theory_and_foundations`, `discrete_math` | `relations-functions-v0`, `equivalence-classes-v0`, `function-composition-v0` | Finite relation properties, injective/surjective checks, function composition, image/preimage, inverse tables, equivalence classes, quotient maps, and EUF slices. |
| `cardinality` | `set_theory_and_foundations`, `discrete_math` | `finite-cardinality-v0`, `cardinality-principles-v0` | Finite bijections/counting, inclusion-exclusion, disjoint unions, double counting, powersets; infinite cardinality marked Lean-horizon. |
| `naturals` | `number_theory`, `discrete_math` | `natural-arithmetic-v0` | Bounded Peano arithmetic and LIA/BV arithmetic identities. |
| `integers` | `number_theory` | `integer-lia-v0` | Linear integer equations/inequalities and witnesses. |
| `rationals` | `real_analysis`, `linear_algebra` | `rationals-lra-v0` | Exact rational order/field facts, density, trichotomy, Farkas links. |
| `reals` | `real_analysis`, `optimization_and_convexity` | `real-analysis-rational-v0`, `reals-rcf-shadow-v0` | Bounded rational neighborhoods and algebraic real constraints through LRA/NRA; completeness marked horizon. |
| `complex` | `complex_analysis`, `linear_algebra` | `complex-algebraic-v0`, `complex-plane-transforms-v0` | Complex arithmetic, unit-root cycles, conjugation, and rational transforms as real-pair algebraic constraints. |
| `divisibility-and-euclid` | `number_theory` | `gcd-bezout-v0` | GCD, Bezout witness replay, divisibility checks. |
| `modular-arithmetic` | `number_theory`, `abstract_algebra` | `modular-arithmetic-v0` | Congruences, inverses, CRT, fixed-modulus enumeration. |
| `groups` | `abstract_algebra` | `finite-groups-v0`, `finite-algebra-homomorphisms-v0` | Cayley-table closure, identity, inverse, associativity, homomorphism, kernel/image, quotient, and induced-map checks. |
| `rings` | `abstract_algebra` | `finite-rings-v0`, `finite-algebra-homomorphisms-v0` | Two-operation table checks, distributivity, zero divisors, and ring-homomorphism preservation. |
| `fields` | `abstract_algebra`, `number_theory` | `finite-fields-v0` | Field axioms over small prime fields; composite modulus counterexamples. |
| `polynomials` | `abstract_algebra`, `real_analysis`, `complex_analysis` | `polynomial-identities-v0`, `generating-functions-v0` | Fixed-degree identities, factor theorem, root witness replay, coefficient extraction, and finite convolution. |
| `sequences-and-limits` | `real_analysis`, `topology` | `sequence-limit-shadow-v0`, `real-analysis-rational-v0`, `generating-functions-v0` | Bounded epsilon/N and epsilon-delta templates, algebraic sequence checks, and finite recurrence/generating-function prefixes; general limits marked Lean-horizon. |
| `counting` | `discrete_math`, `probability_theory` | `counting-v0`, `generating-functions-v0` | Permutations, combinations, pigeonhole finite instances, coefficient extraction, and Cauchy-product counting prefixes. |
| `number-theory` | `number_theory` | `number-theory-v0` | CRT, quadratic residues, sum of squares, bounded Diophantine checks. |
| `linear-algebra` | `linear_algebra`, `numerical_analysis`, `optimization_and_convexity` | `linear-algebra-rational-v0` | Fixed rational matrices, LU replay, inverse checks, inconsistent systems. |
| `calculus` | `real_analysis`, `differential_equations_and_dynamical_systems`, `numerical_analysis` | `calculus-algebraic-shadow-v0`, `calculus-riemann-sum-v0`, `real-analysis-rational-v0` | Polynomial derivative identities, finite Riemann sums, antiderivative endpoint replay, bounded epsilon-delta shadows, and algebraic inequalities; general integration marked Lean-horizon. |

## Field Extensions Beyond The Current Curriculum

These rows widen the existing DAG into the 18-field university taxonomy without
losing the curriculum anchor.

| Field | Curriculum Anchor | First New Resource |
|---|---|---|
| `graph_theory` | sets, relations, counting | `graph-coloring-v0`, then reachability, search runtime/cost counters, matching, cuts, and d-separation. |
| `topology` | sets, reals, sequences-and-limits, linear algebra | `finite-topology-v0`, `finite-simplicial-homology-v0`, then metric balls, closure/interior, continuous maps, compactness, connectedness, and finite chain-complex checks. |
| `measure_theory` | sets, rationals, probability | `finite-measure-v0`, `finite-integration-v0`, `finite-product-measure-v0`, `finite-random-variables-v0`, `finite-conditional-expectation-v0`, `finite-stochastic-kernels-v0`, `finite-martingales-v0`, `finite-hitting-times-v0`, and `finite-concentration-v0` over finite universes; Lebesgue theory remains horizon. |
| `probability_theory` | counting, rationals, finite sets | `finite-probability-v0`, Bayes tables, finite expectations, finite random variables, finite conditional expectation, finite stochastic kernels, finite martingales, finite hitting times, finite concentration/tail bounds, product tables, exact discrete distributions. |
| `statistics` | probability, rationals, linear algebra | `descriptive-statistics-v0`, `least-squares-regression-v0`, contingency tables, exact small tests, least-squares normal equations, finite stochastic-kernel checks, finite hitting-time checks, finite martingale checks, and finite concentration checks. |
| `optimization_and_convexity` | rationals, reals, linear algebra | `linear-optimization-v0`, `convexity-rational-v0`, LP feasibility, dual/Farkas certificates, finite convexity, and threshold checks. |
| `numerical_analysis` | linear algebra, real algebra | `numerical-linear-algebra-v0`, `finite-euler-method-v0`, LU replay, interval bounds, error recurrences, and finite ODE step replay. |
| `differential_equations_and_dynamical_systems` | calculus, linear algebra | `bounded-dynamics-v0`, `finite-euler-method-v0`, recurrence traces, Euler-method steps, finite error replay, and invariant checks before continuous theory. |
| `geometry` | reals, polynomials, linear algebra | `coordinate-geometry-v0`, `affine-geometry-v0`, `orientation-area-geometry-v0`, incidence, distance, midpoint, collinearity, affine maps, signed area, barycentric replay, and finite incidence preservation. |
| `functional_analysis_and_operator_theory` | linear algebra, real analysis | `finite-operator-v0`, `finite-chebyshev-systems-v0`, norms, matrices as operators, Chebyshev polynomial slices, finite interpolation/sign-pattern checks. |

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
the first finite algebra homomorphism pack lives under
`artifacts/examples/math/finite-algebra-homomorphisms-v0/`;
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
a checked rejection of a multi-valued graph. `equivalence-classes-v0` now
deepens that node with finite equivalence classes, quotient-map fibers,
partition-to-relation round trips, checked rejection of a non-transitive
relation, and an explicit QF_UF/Alethe proof-gap row.
`function-composition-v0` now validates finite composition tables,
image/preimage replay, inverse tables for bijections, composition
associativity, non-injective inverse counterexamples, and a general
function-law Lean-horizon row. `finite-fields-v0` now
validates prime-field inverse replay, exhaustive distributivity over a fixed
prime field, and a checked composite-modulus non-field contrast.
`polynomial-identities-v0`
now validates exact coefficient identity replay, a factor-theorem root witness,
and a checked false rational-root rejection. `counting-v0` now validates fixed
permutation and binomial counts plus an exhaustive `3 -> 2` pigeonhole
refutation. `generating-functions-v0` now validates finite coefficient
extraction, Cauchy product convolution, Fibonacci generating-function prefix
replay, checked rejection of a bad convolution coefficient, and a
generating-functions Lean-horizon row. The recommended Phase M3 pack list has
landed. `finite-groups-v0`
now validates finite Cayley-table group axioms, inverse-table replay, and a
checked non-group operation. `finite-rings-v0` now validates finite ring tables,
zero-divisor replay, and a checked non-distributive table.
`finite-algebra-homomorphisms-v0` now extends the algebra core with finite
group-homomorphism replay, kernel/image recomputation, quotient and induced-map
checks, ring-homomorphism replay, checked bad-homomorphism rejection, and a
general isomorphism-theorem Lean-horizon row. `gcd-bezout-v0` now
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
Lean-horizon. `cardinality-principles-v0` now validates finite
inclusion-exclusion, disjoint-union additivity, bipartite-edge double
counting, powerset cardinality, checked false disjoint-additivity rejection,
and an arbitrary-cardinality Lean-horizon row. `induction-obligations-v0` now
validates exact prefix-sum
base-case replay, bounded step-obligation enumeration, bounded conclusion
checking, a bad-step counterexample witness, and a full-schema Lean-horizon
row. `induction-patterns-v0` now validates finite weak-induction evenness
prefixes, strong-induction Fibonacci bounds, loop-invariant trace replay,
checked bad-step rejection, and a full-schema Lean-horizon row.
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
and a completeness/epsilon-delta Lean-horizon row. `real-analysis-rational-v0`
now validates exact rational interval/ball inclusion, a bounded linear
epsilon-delta sample, finite squeeze-style polynomial side conditions, checked
rejection of a false delta, and a general real-analysis Lean-horizon row.
`sequence-limit-shadow-v0` now validates finite epsilon-tail replay, finite
limit-counterexample replay, monotone bounded prefix replay, a fixed geometric
partial-sum identity, a bounded Cauchy-tail no-counterexample row, and a
general convergence Lean-horizon row. `calculus-algebraic-shadow-v0` now
validates polynomial derivative coefficient replay, a checked product-rule
polynomial identity, tangent-line replay, convex quadratic critical-point
replay, false derivative rejection, and a general calculus Lean-horizon row.
`calculus-riemann-sum-v0` now validates exact finite Riemann sums, midpoint
and trapezoid replay, polynomial antiderivative endpoint replay, monotone lower
and upper sums, checked false integral rejection, and a fundamental-theorem
Lean-horizon row. `proof-methods-refutation-v0`
now validates the `PHP(2,2)` control witness and the `PHP(3,2)` refutation by
deterministic CNF truth-table enumeration; LRAT/DRAT proof objects remain its
graduation route, not a pack-level proof gap.

Recommended order:

1. `proof-methods-refutation-v0` (landed) and
   `proof-methods-patterns-v0` (landed): negation-as-query, pigeonhole,
   direct proof, contrapositive, cases, contradiction, invalid converse
   counterexamples, and checked finite CNF/truth-table refutations; LRAT/DRAT
   remains the stronger proof-object graduation route.
2. `finite-sets-v0` (landed), `relations-functions-v0` (landed),
   `equivalence-classes-v0` (landed), and `function-composition-v0` (landed):
   finite set identities, relation properties, function properties,
   composition, image/preimage, inverse tables, equivalence classes,
   partitions, and quotient maps.
3. `gcd-bezout-v0` (landed): gcd, Bezout, divisibility, and fixed
   Diophantine obstruction checks.
4. `modular-arithmetic-v0`: CRT, modular inverse, residue witness checks.
5. `finite-fields-v0` (landed) and `finite-algebra-homomorphisms-v0`
   (landed): prime-field axioms, composite-modulus counterexample, finite
   homomorphism tables, kernel/image replay, quotient maps, and induced-map
   checks.
6. `rationals-lra-v0`: density/trichotomy and exact rational LRA certificates.
7. `linear-algebra-rational-v0`: fixed matrices, LU replay, inconsistent
   system with Farkas evidence where available.
8. `polynomial-identities-v0` and `generating-functions-v0` (landed): factor
   theorem, fixed-degree identities, finite coefficient extraction, Cauchy
   products, and bounded recurrence/generating-function prefixes.
9. `counting-v0` (landed): combinations, pigeonhole, finite counting witnesses.
10. `number-theory-v0` (landed): CRT compatibility, quadratic residues,
    sum-of-two-squares, and bounded Diophantine checks.
11. `integer-lia-v0` (landed): signed order facts, linear equations,
    interval infeasibility, and GCD-test refutations.
12. `natural-arithmetic-v0` (landed): bounded successor/addition replay,
    commutativity, distributivity, and Peano-style bounded no-counterexamples.
13. `finite-cardinality-v0` (landed) and
    `cardinality-principles-v0` (landed): finite bijections, finite cardinal
    inequalities, injection/surjection refutations, inclusion-exclusion,
    disjoint unions, double counting, powersets, and infinite-cardinality
    Lean-horizon metadata.
14. `induction-obligations-v0` (landed) and `induction-patterns-v0` (landed):
    bounded base/step obligations, finite weak and strong induction patterns,
    loop-invariant replay, bad-step witnesses, and full-schema Lean-horizon
    metadata.
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
19. `calculus-algebraic-shadow-v0` (landed) and
    `calculus-riemann-sum-v0` (landed): polynomial derivative replay,
    product-rule identity checks, tangent-line replay, critical-point checks,
    finite Riemann sums, antiderivative endpoint replay, false integral
    rejection, and analytic calculus Lean-horizon metadata.
20. `real-analysis-rational-v0` (landed): exact rational interval/ball
    inclusion, bounded epsilon-delta samples, squeeze-style polynomial side
    conditions, bad-delta rejection, and general real-analysis Lean-horizon
    metadata.

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
`artifacts/examples/math/graph-search-runtime-v0/` now validates finite BFS and
DFS target-discovery cost counters, shortcut-tail family replay, checked
rejection of a false DFS cost bound, and an asymptotic search-runtime
Lean-horizon row.
`artifacts/examples/math/graph-matching-v0/` now validates finite matching
witness replay, invalid-overlap rejection, augmenting-path flip replay, and a
perfect-matching obstruction by exhaustive enumeration.
`artifacts/examples/math/graph-d-separation-v0/` now validates finite DAG
d-separation checks for chains, forks, colliders, and descendant-opened
colliders.
`artifacts/examples/math/graph-cut-v0/` now validates finite minimum edge-cut
and vertex-cut certificates, plus checked rejection of non-separating one-edge
and one-vertex cuts.
`artifacts/examples/math/finite-probability-v0/` now validates finite
probability mass tables, conditional probability, and Bayes posterior replay.
`artifacts/examples/math/descriptive-statistics-v0/` now validates exact
mean/variance identities, contingency-table margins, and a Simpson's paradox
count-table witness.
`artifacts/examples/math/least-squares-regression-v0/` now validates exact
least-squares normal equations, residual orthogonality, mean-baseline RSS
comparison, checked rejection of bad coefficients, and a regression-statistics
Lean-horizon row.
`artifacts/examples/math/linear-optimization-v0/` now validates LP feasibility
witnesses, objective-threshold replay, and a tiny checked Farkas certificate.
`artifacts/examples/math/convexity-rational-v0/` now validates exact rational
midpoint convexity, finite-grid second differences, affine monotonicity
threshold replay, checked rejection of a bad midpoint-convexity claim, and a
general convex-analysis Lean-horizon row.
`artifacts/examples/math/coordinate-geometry-v0/` now validates exact midpoint,
collinearity, and squared-distance coordinate checks.
`artifacts/examples/math/affine-geometry-v0/` now validates exact affine
point-image replay, midpoint preservation, collinearity preservation, checked
rejection of a false affine distance-preservation claim, and a general
affine-geometry Lean-horizon row.
`artifacts/examples/math/orientation-area-geometry-v0/` now validates exact
signed-area/orientation replay, affine area scaling by determinant,
barycentric point-inside replay, checked rejection of a false orientation
claim, and a general oriented-geometry Lean-horizon row.
`artifacts/examples/math/finite-topology-v0/` now validates finite topology
axioms, closure/interior computation, and exact finite metric-ball replay.
`artifacts/examples/math/metric-continuity-v0/` now validates finite
Lipschitz, epsilon-delta, and open-ball preimage checks with exact rational
metrics, plus checked rejection of an overlarge delta.
`artifacts/examples/math/finite-compactness-v0/` now validates finite
open-cover/subcover checks, minimal subcover enumeration,
finite-intersection-family replay, bad-cover rejection, and a compactness
Lean-horizon row.
`artifacts/examples/math/finite-connectedness-v0/` now validates finite
connectedness by clopen-subset enumeration, open-separation replay, checked
rejection of a false connectedness claim, and a connectedness Lean-horizon row.
`artifacts/examples/math/finite-continuous-maps-v0/` now validates finite
continuity by open-set preimage enumeration, finite homeomorphism replay,
checked rejection of false continuity and homeomorphism claims, and a
continuous-map Lean-horizon row.
`artifacts/examples/math/finite-simplicial-homology-v0/` now validates finite
simplicial-complex closure, oriented-boundary replay, the finite
`boundary^2 = 0` chain-complex identity, fixed Betti-rank replay over `Q`,
checked rejection of a bad boundary sign, and a general homology
Lean-horizon row.
`artifacts/examples/math/finite-measure-v0/` now validates finite
sigma-algebra axioms, exact finite additivity, and event/complement measure
replay.
`artifacts/examples/math/finite-integration-v0/` now validates exact finite
simple-function integrals, indicator integrals, integral linearity, checked
rejection of a false expectation, and a Lebesgue-integration Lean-horizon row.
`artifacts/examples/math/finite-product-measure-v0/` now validates exact
finite product-measure tables, rectangle probabilities, left and right
marginals, finite Fubini replay, checked rejection of a false product
probability, and a Fubini/Tonelli Lean-horizon row.
`artifacts/examples/math/finite-random-variables-v0/` now validates exact
finite random-variable pushforwards, expectation through pushforward
distributions, finite independence checks, checked rejection of a false
pushforward distribution, and a general random-variable/conditional-expectation
Lean-horizon row.
`artifacts/examples/math/finite-conditional-expectation-v0/` now validates
exact finite partition conditional expectations, the law of total expectation,
the finite tower property over nested partitions, checked rejection of a false
conditional-expectation table, and a general conditional-expectation/martingale
Lean-horizon row.
`artifacts/examples/math/finite-martingales-v0/` now validates exact finite
filtrations, adaptedness, martingale conditional-expectation equalities,
finite square-submartingale inequalities, bounded stopping-time replay, checked
rejection of a false martingale table, and a general martingale Lean-horizon
row.
`artifacts/examples/math/finite-stochastic-kernels-v0/` now validates exact
finite source-to-target probability kernels, pushforward distributions, joint
factorization/disintegration replay, kernel composition, checked rejection of a
malformed kernel row, and a regular-conditional-probability Lean-horizon row.
`artifacts/examples/math/finite-hitting-times-v0/` now validates exact finite
first-hit distributions, survival probabilities, absorption-probability
fixed-point equations, expected hitting-time equations, checked rejection of a
false expected-time table, and a recurrence/transience Lean-horizon row.
`artifacts/examples/math/finite-concentration-v0/` now validates exact finite
Markov, Chebyshev, and union-bound replays over rational atom tables, checked
rejection of a false tail bound, and a concentration/limit-theorem
Lean-horizon row.
`artifacts/examples/math/bounded-dynamics-v0/` now validates exact rational
recurrence traces, bounded invariant witnesses, and threshold reachability
replay.
`artifacts/examples/math/finite-euler-method-v0/` now validates exact finite
Euler-method traces, polynomial-solution error replay, invariant checks,
checked rejection of a bad Euler step, and an ODE-theory Lean-horizon row.
`artifacts/examples/math/finite-operator-v0/` now validates exact
finite-dimensional norm, matrix-operator, and Chebyshev recurrence checks.
`artifacts/examples/math/finite-chebyshev-systems-v0/` now validates exact
finite Vandermonde unisolvence, interpolation matrix replay, alternating
residual sign patterns, checked rejection of a duplicate-node grid, and a
general Chebyshev-system Lean-horizon row.
`artifacts/examples/math/complex-algebraic-v0/` now validates exact complex
arithmetic, conjugate/norm replay, and a fixed polynomial-root witness using
real-pair algebra.
`artifacts/examples/math/complex-plane-transforms-v0/` now validates exact
unit-root cycles, conjugation/product replay, rational Mobius-transform
replay, checked rejection of a false unit-square real-part claim, and a
complex-analysis Lean-horizon row.
`artifacts/examples/math/numerical-linear-algebra-v0/` now validates exact
residual bounds, rational solution boxes, Jacobi one-step contraction replay,
and checked rejection of a false residual bound.
`artifacts/examples/math/spectral-linear-algebra-v0/` now validates exact
finite eigenpair replay, orthogonal eigenbasis checks, Rayleigh quotients,
spectral decomposition replay, and checked rejection of a false eigenpair.
`artifacts/examples/math/matrix-invariants-v0/` now validates exact
trace/determinant characteristic-polynomial replay, characteristic roots,
Cayley-Hamilton replay, finite Gershgorin intervals, and checked rejection of a
false characteristic polynomial.
`artifacts/examples/math/random-matrix-finite-v0/` now validates exact finite
random-matrix moment replay, expected Gram matrices, rank probabilities, and
checked rejection of a false trace-square moment.
`artifacts/examples/math/finite-markov-chain-v0/` now validates exact
row-stochastic matrix replay, finite-horizon distribution evolution,
stationary-distribution replay, and checked rejection of a malformed transition
row.
`artifacts/examples/math/exact-statistical-tests-v0/` now validates exact
binomial tails, hypergeometric point probabilities, one-sided Fisher p-values,
and checked rejection of a false p-value.

Recommended order:

1. Graph resources landed: `graph-coloring-v0`, `graph-reachability-v0`,
   `graph-search-runtime-v0`, `graph-matching-v0`,
   `graph-d-separation-v0`, and `graph-cut-v0` validate SAT colorings,
   non-colorability, finite reachability, traversal traces, finite search
   cost counters, cut separation, matching witnesses, augmenting paths, finite
   DAG d-separation, and minimum cut certificates.
2. `finite-probability-v0`: probability mass, conditioning, Bayes rule.
3. `descriptive-statistics-v0` and `least-squares-regression-v0`:
   mean/variance identities, contingency tables, Simpson witness,
   least-squares normal equations, residual orthogonality, and bad-coefficient
   rejection.
4. `linear-optimization-v0`: LP feasibility, threshold cliffs, Farkas links.
5. `convexity-rational-v0`: midpoint convexity, finite second differences,
   monotonicity thresholds, and bad midpoint-convexity rejection.
6. `coordinate-geometry-v0`, `affine-geometry-v0`, and
   `orientation-area-geometry-v0`: collinearity, midpoint, distance
   constraints, affine maps, signed area/orientation, barycentric replay,
   finite incidence preservation, false distance-preservation rejection, and
   false orientation rejection.
7. `finite-topology-v0`: finite closure/interior and metric-ball examples.
8. `finite-measure-v0`: finite sigma-algebras and finite measure checks.
9. `bounded-dynamics-v0` and `finite-euler-method-v0`: recurrence systems,
   Euler step replay, finite error checks, and invariants.
10. `finite-operator-v0`: finite-dimensional norms/operators and Chebyshev
   polynomial examples.
11. `complex-algebraic-v0` and `complex-plane-transforms-v0`: complex
    arithmetic, unit-root cycles, conjugation/product replay, and rational
    Mobius transforms as real-pair algebra.
12. `numerical-linear-algebra-v0`: residual bounds, rational solution boxes,
    and exact iterative-method error replay.
13. `random-matrix-finite-v0`: finite matrix-valued probability tables,
    exact moments, Gram expectations, and rank distributions.
14. `finite-markov-chain-v0`: stochastic matrices, finite-horizon
    distribution replay, stationary distributions, and bad transition rows.
15. `exact-statistical-tests-v0`: exact binomial and hypergeometric p-values
    for finite statistical tests.
16. `spectral-linear-algebra-v0`: exact eigenpairs, orthogonal eigenbases,
    Rayleigh quotients, and finite spectral decomposition.
17. `matrix-invariants-v0`: trace/determinant characteristic polynomials,
    roots, Cayley-Hamilton replay, and finite eigenvalue intervals.
18. `metric-continuity-v0`: finite Lipschitz, epsilon-delta, open-ball
    preimage, and bad-delta checks over exact rational metric spaces.
19. `finite-compactness-v0`: finite open covers, minimal subcover
    enumeration, finite-intersection families, and bad-cover rejection.
20. `finite-connectedness-v0`: finite connected spaces, open separations,
    clopen-subset enumeration, and bad-connected-claim rejection.
21. `finite-continuous-maps-v0`: finite topological continuity, open-set
    preimages, homeomorphism replay, and bad-map rejection.
22. `finite-simplicial-homology-v0`: finite simplicial-complex closure,
    oriented-boundary replay, `boundary^2 = 0`, fixed Betti-rank replay, and
    bad-boundary rejection.
23. `finite-integration-v0`: finite simple-function integrals, indicator
    integrals, exact linearity, and bad-expectation rejection.
24. `finite-product-measure-v0`: finite product probability tables,
    rectangle probabilities, marginals, finite Fubini replay, and bad
    product-probability rejection.
25. `finite-random-variables-v0`: finite random-variable pushforwards,
    expectation through pushforward distributions, independence checks, and
    bad pushforward rejection.
26. `finite-conditional-expectation-v0`: finite partition conditional
    expectations, law of total expectation, tower property replay, and bad
    conditional-expectation rejection.
27. `finite-martingales-v0`: finite filtrations, adaptedness, martingale
    equalities, square submartingale inequalities, bounded stopping replay, and
    bad martingale rejection.
28. `finite-stochastic-kernels-v0`: finite source-to-target kernels,
    pushforward distributions, joint disintegration replay, kernel
    composition, and bad kernel-row rejection.
29. `finite-hitting-times-v0`: finite first-hit distributions, survival
    probabilities, absorption-probability equations, expected hitting-time
    equations, and bad expected-time rejection.
30. `finite-concentration-v0`: finite Markov, Chebyshev, and union-bound
    tail checks, plus rejection of a false concentration bound.
31. `finite-chebyshev-systems-v0`: finite Vandermonde unisolvence,
    interpolation replay, alternating residual signs, and duplicate-node
    rejection.

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
plain-shell fallback now regenerate the concept atlas, validate it, validate all
math example packs, regenerate dashboards, and fail if generated atlas or
dashboard files are stale; CI runs the same gate before docs link checking.

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

Status: initial decision landed in
[Foundational Resource Library Boundary Decision](LIBRARY-BOUNDARY-DECISION.md).
The resource lane stays in-repo for now. The stable boundary is the committed
JSON/schema/metadata contract plus generated dashboards, smoke-tested by
`scripts/consume-foundational-resources.py`; crates or repo splits are deferred
until external consumers, generated typed APIs, or shared encoders require them.

Possible boundaries:

- `axeyum-foundational-data`: generated JSON and schema consumers.
- `axeyum-math-examples`: reusable encoders for graph, finite algebra, matrix,
  and finite probability examples.
- Separate repository only if the resources gain an independent release cycle,
  large corpora, or users who do not need the Axeyum source tree.

Exit criteria:

- At least 40 validated concept rows.
  Status: 41 atlas rows validate.
- At least 12 validated example packs.
  Status: 72 non-template math example packs validate.
- At least 6 packs with checked proof/evidence routes.
  Status: 60 non-template packs have at least one `checked` expected-result row.
- At least one downstream consumer can read the data without repository-internal
  knowledge.
  Status: `scripts/consume-foundational-resources.py` reads the committed atlas
  and example-pack JSON files directly without importing generator or validator
  internals.

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
`finite-fields-v0`, `finite-algebra-homomorphisms-v0`,
`polynomial-identities-v0`, `counting-v0`, `gcd-bezout-v0`,
`number-theory-v0`, `integer-lia-v0`, `natural-arithmetic-v0`, and
`finite-cardinality-v0`, `cardinality-principles-v0`,
`induction-obligations-v0`, `induction-patterns-v0`, `logic-basics-v0`, and
`real-analysis-rational-v0`, `calculus-riemann-sum-v0`, Phase M4 graph-resource
group and items 4-31, and
the Phase M5 learner-path scaffold plus first encode/check walkthrough layer
have landed for the math seed. End-to-end lessons now exist for graph coloring,
graph reachability/traversal/search runtime/matching, finite DAG d-separation,
finite cut certificates, rational arithmetic, linear algebra/optimization,
probability/statistics, finite structures, and analysis/topology horizons.
Phase M6 now has cookbook links from all current non-template math example
packs, and `proof-methods-refutation-v0` has a checked finite CNF truth-table
route for its pigeonhole refutation. Phase M7 now has
generated pack-level proof-gap rows and a normal foundational-resource check
hook. `numerical-linear-algebra-v0` now adds the first exact residual/error-bound
numerical-analysis slice, and `random-matrix-finite-v0` adds the first exact
finite random-matrix bridge across linear algebra, probability, statistics, and
numerical analysis. `finite-markov-chain-v0` now adds the first exact finite
stochastic-process bridge across probability, linear algebra, statistics, and
dynamics. `exact-statistical-tests-v0` now adds the first exact finite
statistical-test slice for p-values as rational finite sums.
`proof-methods-patterns-v0` now deepens the proof-methods curriculum row with
finite direct proof, contrapositive, proof-by-cases, contradiction, invalid
converse counterexample, and natural-deduction Lean-horizon examples.
`induction-patterns-v0` now deepens the induction curriculum row with finite
weak induction, strong induction, loop-invariant replay, invalid-step
counterexamples, and full-schema Lean-horizon examples.
`cardinality-principles-v0` now deepens the cardinality curriculum row with
finite inclusion-exclusion, disjoint-union additivity, bipartite-edge double
counting, powerset enumeration, invalid additivity counterexamples, and
infinite-cardinality Lean-horizon examples.
`calculus-riemann-sum-v0` now deepens the calculus curriculum row with exact
finite Riemann sums, midpoint/trapezoid replay, antiderivative endpoint
replay, monotone lower/upper sums, false integral counterexamples, and
fundamental-theorem Lean-horizon examples.
`equivalence-classes-v0` now deepens the relations/functions curriculum row
with exact finite equivalence classes, quotient-map fibers, partition
round-trips, a checked non-transitive counterexample, and an explicit
QF_UF/Alethe proof-object gap.
`function-composition-v0` now deepens the relations/functions curriculum row
with finite composition, image/preimage, inverse-table, associativity,
non-injective inverse counterexample, and general function-law Lean-horizon
examples.
`convexity-rational-v0` now adds the first exact finite convexity bridge for
optimization learners: midpoint Jensen replay, finite second differences,
affine threshold monotonicity, and bad midpoint-convexity rejection.
`spectral-linear-algebra-v0` now adds the first exact finite
spectral-linear-algebra slice for eigenpair, Rayleigh quotient, and
decomposition replay. `matrix-invariants-v0` now adds the characteristic
polynomial, Cayley-Hamilton, and finite eigenvalue-interval step needed before
broader spectral claims. `metric-continuity-v0` now adds the finite
epsilon-delta and open-ball preimage bridge for analysis/topology learners.
`finite-compactness-v0` now adds the finite open-cover/subcover and
finite-intersection bridge to the compactness horizon.
`finite-connectedness-v0` now adds the finite clopen-subset/open-separation
bridge to the connectedness horizon. `finite-continuous-maps-v0` now adds the
finite preimage/homeomorphism bridge connecting continuity to compactness and
connectedness horizons. `finite-simplicial-homology-v0` now adds the exact
finite algebraic-topology bridge: simplicial closure, oriented boundaries,
`boundary^2 = 0`, fixed Betti-rank replay, bad-boundary rejection, and a
homology Lean-horizon row. `finite-integration-v0` now adds the exact finite
simple-function integral bridge between finite measure, probability, and
statistics. `finite-product-measure-v0` now adds the exact finite product
measure, marginalization, and Fubini bridge toward general measure/probability
theory. `finite-random-variables-v0` now adds the exact finite random-variable
pushforward, expectation, and independence bridge toward probability/statistics
and measure-theory semantics. `finite-conditional-expectation-v0` now adds the
finite partition conditional-expectation, total-expectation, and tower-property
bridge toward martingales and general conditional expectation.
`finite-martingales-v0` now adds the exact finite filtration, martingale,
submartingale, and bounded-stopping bridge toward stochastic-process theory.
`finite-stochastic-kernels-v0` now adds the finite conditional-distribution,
pushforward, disintegration, and composition bridge toward Markov kernels and
regular conditional probabilities. `finite-hitting-times-v0` now adds the
finite first-hit, survival, absorption-probability, and expected-hitting-time
bridge toward recurrence/transience and potential-theory horizons.
`finite-concentration-v0` now adds the finite Markov/Chebyshev/union-bound
tail-probability bridge toward concentration inequalities, limit theorems,
martingale concentration, and asymptotic statistics.
`finite-chebyshev-systems-v0` now adds the finite Vandermonde/interpolation
and alternation-sign bridge toward Chebyshev-system, Haar-space, minimax, and
approximation-theory horizons.
`affine-geometry-v0` now adds the exact finite affine-map bridge for geometry:
point-image replay, midpoint preservation, collinearity preservation, checked
rejection of false distance preservation, and an affine-geometry Lean-horizon
row.
`orientation-area-geometry-v0` now adds the exact finite orientation/area
bridge for geometry: signed-area replay, affine determinant area scaling,
barycentric point-inside replay, checked rejection of false orientation, and an
oriented-geometry Lean-horizon row.
`complex-plane-transforms-v0` now adds the next exact finite complex-analysis
bridge: unit-root cycles, conjugation/product replay, rational
Mobius-transform replay, checked rejection of a false unit-square real-part
claim, and a complex-analysis Lean-horizon row.
`least-squares-regression-v0` now adds the next exact finite statistics bridge:
least-squares normal equations, residual orthogonality, mean-baseline RSS
comparison, checked rejection of bad coefficients, and a regression-statistics
Lean-horizon row.
`generating-functions-v0` now adds the next exact finite discrete/polynomial
bridge: coefficient extraction, Cauchy product convolution, Fibonacci
generating-function prefix replay, checked rejection of a bad convolution
coefficient, and a generating-functions Lean-horizon row.
`finite-euler-method-v0` now adds the next exact finite dynamics/numerical
bridge: explicit Euler replay, polynomial-solution error replay, finite
invariant checks, checked rejection of a bad Euler step, and an ODE-theory
Lean-horizon row. `finite-algebra-homomorphisms-v0` now adds the next exact
finite algebra bridge after group/ring tables: homomorphism preservation,
kernel/image replay, quotient/induced-map replay, checked bad-homomorphism
rejection, and an isomorphism-theorem Lean-horizon row.
Continue by
adding the next curriculum-adjacent pack or by replacing finite enumeration
routes with emitted, checked proof objects where appropriate.

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
