# Math Curriculum Comprehensive Resource Plan

## Purpose

This is the owner-facing plan for building out all Axeyum foundational
resources from the formal math curriculum. It connects the current curriculum
DAG, the 18-field university taxonomy, the example packs, learner pages, proof
routes, solver-feedback hooks, rules/law transfer examples, and future library
boundaries into one operating program.

The invariant is the same everywhere:

```text
untrusted fast search, trusted small checking
```

The resources should not become a textbook clone, a benchmark dump, or a
formal-library mirror. Each increment should make one bounded, finite,
computable, or explicitly theorem-horizon claim easier to find, replay, check,
teach, or reuse.

## Source Grounding

Build from these sources in order:

1. [`docs/curriculum/curriculum.toml`](../curriculum/curriculum.toml): the
   authoritative 23-node prerequisite DAG.
2. [`MATH-FIELDS.md`](MATH-FIELDS.md): the 18-field university math taxonomy.
3. [`artifacts/examples/math/`](../../artifacts/examples/math/): current
   validating example packs.
4. [`artifacts/ontology/foundational-concepts.json`](../../artifacts/ontology/foundational-concepts.json):
   generated concept, field, bridge, and example-family rows.
5. [`docs/learn/math/`](../learn/math/): learner-facing end-to-end pages and
   field indexes.
6. [`PROOF-ROUTE-QUERY-MATRIX.md`](PROOF-ROUTE-QUERY-MATRIX.md) and
   [`PROOF-UPGRADE-FRONTIER.md`](PROOF-UPGRADE-FRONTIER.md): proof-route
   coverage and upgrade queues.
7. [`RULES-LAW-CROSSWALK.md`](RULES-LAW-CROSSWALK.md): downstream transfer
   into policy/rule reasoning.

Generated dashboards are evidence, not editable plans. If a dashboard disagrees
with prose, fix the JSON, metadata, generator, or prose source.

## Current Baseline

As of 2026-07-01, the public resource query reports:

- 120 concept rows: 23 curriculum nodes, 18 math fields, 74 bridge concepts, and
  5 example families.
- 108 non-template math packs.
- 648 expected checks: 336 `sat`, 241 `unsat`, and 71 `not-run`.
- 322 checked proof/evidence rows.
- 255 replay-only rows.
- 71 Lean-horizon rows.
- 108 promoted solver-reuse packs.
- 0 unclassified solver-reuse packs.
- 108 focused learner-linked packs, with no path-only, index-only, or missing
  learner buckets; see [Learner Coverage Audit](LEARNER-COVERAGE-AUDIT.md).

The seed phase is over. The next phase is not "add examples everywhere." The
next phase is to turn the current broad resource system into a coherent
curriculum product with reliable discovery, proof depth, solver feedback, and
downstream reuse.

## Resource Families

| Family | Primary Audience | Files / Boundary | Graduation Signal |
|---|---|---|---|
| Curriculum spine | learners, educators, planners | `docs/curriculum/curriculum.toml`, curriculum pages | every resource has a curriculum node or field owner |
| Field taxonomy | planners, consumers | `MATH-FIELDS.md`, concept rows | every math row validates against one or more field ids |
| Concept atlas | consumers, contributors | `foundational-concepts.schema.json`, `foundational-concepts.json` | validator passes and dashboards expose the row |
| Example packs | learners, solver/proof contributors | `artifacts/examples/math/<pack>/` | pack validator passes; rows have explicit result and proof status |
| Learner pages | learners, educators | `docs/learn/math/*.md` | link check passes; page names finite slice and theorem horizon |
| Proof artifacts | proof contributors, reviewers | `cnf/`, `smt2/`, route regressions, cookbook recipes | route-specific regression checks evidence or rejects tampering |
| Solver feedback | solver contributors | source artifacts, tests, fuzz seeds, corpus rows | pack metadata and regression link to each other |
| Rules/law transfer | application builders | `docs/rules-as-code/`, rules examples | rule pack reuses existing math proof shape and validates |
| Consumer boundary | downstream tools | schemas, generated JSON, query scripts | consumer smoke test passes without importing generators |
| Future libraries | external users | possible crate/repo split | repeated real consumers justify a boundary decision |

## Resource Unit Contract

Every new or upgraded resource must answer these questions before it lands:

| Question | Required Answer |
|---|---|
| Owner | Which curriculum node or field owns it? |
| Audience | Learner, educator, proof contributor, solver contributor, application builder, or consumer. |
| Claim shape | Finite claim, bounded shadow, computable witness, numerical check, or theorem horizon. |
| Encoding route | Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, QF_NRA/RCF, finite replay, or Lean horizon. |
| Evidence route | model replay, DRAT/LRAT, Farkas, Diophantine, Alethe, QF_BV DRAT, or explicit gap. |
| Trust boundary | What is searched/generated, and what is independently replayed or checked? |
| Graduation | Which command, regression, proof route, or theorem dependency moves it forward? |

Do not land a bare topic name. A resource needs a validated example, a planned
example with a validation rule, or a theorem-horizon dependency.

## Curriculum Spine Buildout

The buildout follows the 23-node curriculum DAG in four layers. A node is
"built out" only when it has concept rows, packs, learner material, evidence
status, solver-reuse disposition, and query visibility.

### Layer 0: Foundations

| Node | Build Target | Resource Work | Horizon Boundary |
|---|---|---|---|
| `propositional-logic` | smallest complete trust story | SAT witnesses, CNF refutations, proof-object anatomy, tamper rejection | proof-assistant natural deduction is separate from SAT evidence |
| `predicate-logic` | finite-domain quantifier replay | finite expansion, countermodel replay, equality-heavy QF_UF rows | arbitrary first-order validity remains theorem/proof horizon |
| `proof-methods` | proof patterns as solver queries | direct proof, contrapositive, cases, contradiction, refutation-as-query | general proof automation requires Lean reconstruction |
| `induction` | bounded obligations and schema boundary | finite base/step obligations, invalid-step counterexamples, loop invariants | universal induction schema is Lean horizon |
| `sets` | finite set algebra | membership, subset, Boolean algebra, finite topology set families | infinite set theory, choice, ordinals, cardinals stay horizon |
| `relations-and-functions` | finite structure maps | relations, functions, equivalence classes, quotients, image/preimage, inverse tables | arbitrary function/quotient theorems need Lean |
| `cardinality` | finite counting vs infinite theorem boundary | finite bijections, injection/surjection checks, inclusion-exclusion, double counting | Cantor/infinite-cardinality facts stay Lean horizon |

Priority work:

1. Keep the proof-object learner path short and auditable.
2. Promote one representative false finite set/relation/lattice claim per
   proof route.
3. Make finite countermodel and finite quantifier expansion reusable by
   rules/law packs.

### Layer 1: Number Systems

| Node | Build Target | Resource Work | Horizon Boundary |
|---|---|---|---|
| `naturals` | bounded arithmetic and totality conventions | Peano-shadow rows, bounded arithmetic, fixed-width contrasts | bounded prefixes do not prove unbounded arithmetic |
| `integers` | linear integer witnesses and obstructions | LIA witnesses, Diophantine conflicts, modular links | nonlinear and unbounded search needs theorem/solver depth |
| `rationals` | exact rational arithmetic | order, density, field laws, Farkas conflicts, exact-vs-floating boundary | no floating-point claim from rational replay |
| `reals` | bounded real and algebraic shadows | intervals, balls, epsilon-delta shadows, RCF/NRA examples, optimization steps | completeness, IVT/MVT/FTC, compactness, and convergence stay horizon |
| `complex` | real-pair algebra | conjugation, norms, products, roots, transforms as real constraints | holomorphic/analytic theory stays Lean horizon |

Priority work:

1. Keep exact rational rows as the canonical QF_LRA/Farkas teaching route.
2. Add real/complex rows only when they create reusable proof vocabulary or
   genuine NRA/RCF solver pressure.
3. Keep numerical-analysis language separate from exact arithmetic.

### Layer 2: Core Structures And Tools

| Node | Build Target | Resource Work | Horizon Boundary |
|---|---|---|---|
| `divisibility-and-euclid` | arithmetic certificates | gcd, Bezout, divisibility, quotient/remainder, gcd obstruction rows | unique factorization theorem is not a finite replay |
| `modular-arithmetic` | residues and CRT | inverses, nonunits, CRT compatibility, fixed-width BV rows | full CRT/field theorem reconstruction remains separate |
| `groups` | finite operation tables | Cayley replay, homomorphisms, kernels/images, quotients, actions | arbitrary group theory stays Lean horizon |
| `rings` | finite two-operation structures | distributivity, units/idempotents, ideals, quotient rings, modules | general ring/module theorems stay Lean horizon |
| `fields` | finite fields and vector-space base | prime-field tables, composite counterexamples, finite-field linear algebra | arbitrary-field results and algebraic closure stay horizon |
| `polynomials` | coefficient arithmetic and fixed-degree checks | identities, factorization replay, generating functions, root-finding shadows | general factorization, algebraic closure, and convergence stay horizon |
| `sequences-and-limits` | finite prefixes and bounded tails | recurrence prefixes, Cauchy-tail shadows, monotone-prefix rows | convergence theorems stay Lean horizon |
| `counting` | exact finite enumeration | permutations, combinations, pigeonhole, coefficients, orbit counts, tail counts | asymptotic enumeration stays horizon |

Priority work:

1. Use algebra-table packs to keep QF_UF/Alethe and QF_BV routes exercised.
2. Use divisibility/counting/torsion rows to keep QF_LIA/Diophantine evidence
   visible.
3. Maintain the landed bounded-family/asymptotic boundary bridge for graph
   search, recurrence prefixes, generating-function coefficient windows,
   bounded dynamics, and Euler rows; add narrower rows only if a new family
   creates distinct proof or solver pressure.

### Layer 3: Destinations

| Node | Build Target | Resource Work | Horizon Boundary |
|---|---|---|---|
| `number-theory` | bounded arithmetic families | residues, quadratic residues, sums of squares, bounded Diophantine rows | analytic/algebraic number theory stays horizon |
| `linear-algebra` | exact matrix computation | LU, rank/nullity, residuals, eigenpairs, characteristic polynomials, finite vector spaces, modules, tensors | spectral theorem, conditioning, and infinite-dimensional results stay horizon |
| `calculus` | algebraic and finite algorithm shadows | derivative identities, Riemann sums, Jacobian/Hessian replay, root finding, line search, projected/proximal steps | FTC, differentiability theory, and algorithm convergence stay horizon |

Priority work:

1. Keep the matrix-computation index as the main user entry point for linear
   algebra resources.
2. Treat calculus rows as exact finite shadows plus theorem boundaries, never
   as full analysis proof.
3. Promote solver regressions only after the pack and learner page explain the
   source mathematics.

## Field Extension Buildout

The 18-field taxonomy widens the 23-node DAG into a university-style curriculum.
Field resources should be built where the curriculum node is too coarse for
real use.

| Field | Build Out | Current Best Route | Next Practical Depth |
|---|---|---|---|
| `logic_and_proof` | proof object anatomy, refutation, finite proof patterns | Bool/CNF, QF_LIA, QF_UF, Lean horizon | compact certificate walkthroughs with corrupted-proof rejection |
| `set_theory_and_foundations` | finite sets, relations, functions, quotients, lattices, cardinality | finite replay, Bool/CNF, QF_UF/Alethe | stronger finite/infinite boundary rows and reusable quotient vocabulary |
| `discrete_math` | counting, graph resources, recurrences, finite actions | Bool/CNF, QF_LIA, finite replay | recurrence/asymptotic boundaries tied to graph search and generating functions |
| `graph_theory` | coloring, reachability, traversal cost, matching, cuts, d-separation | Bool/CNF, QF_BV, QF_LIA, replay | more CNF/LRAT rows where the graph is small and educational |
| `number_theory` | gcd, CRT, residues, bounded Diophantine rows | QF_LIA, QF_BV | grouped arithmetic-certificate cookbook examples |
| `linear_algebra` | matrices, vector spaces, modules, tensors, spectral rows | QF_LRA/Farkas, replay, QF_UF/Alethe | matrix-corpus boundary and source-linked regressions |
| `abstract_algebra` | finite groups/rings/fields, homomorphisms, ideals, modules, tensors | QF_UF/Alethe, QF_BV, replay | orbit/stabilizer, Burnside, quotient/module rows only when reused |
| `real_analysis` | rational analysis, metric continuity, compactness shadows, optimization shadows | QF_LRA/Farkas, QF_NRA/RCF, Lean horizon | delta-epsilon/metric-ball and convergence-boundary paths |
| `complex_analysis` | real-pair algebra, transforms, polynomial roots | LRA/NRA real-pair replay, Lean horizon | analytic-horizon rows, not analytic overclaims |
| `topology` | finite topologies, continuity, specialization, homology/cohomology shadows | Bool/CNF, QF_UF, QF_LIA, QF_BV, replay | quotient/cohomology-ring/invariance boundaries |
| `measure_theory` | finite measures, integration, product measures, random variables | QF_LRA/Farkas, replay, Lean horizon | countable-measure and convergence horizons without benchmark claims |
| `probability_theory` | PMFs, kernels, Markov chains, martingales, hitting times, concentration | QF_LRA/Farkas, QF_LIA, replay | exact discrete distribution variants plus limit-theorem horizons |
| `statistics` | descriptive statistics, exact tests, regression, contingency tables | QF_LIA, QF_LRA, replay | exact finite inference plus numerical/statistical-honesty metadata |
| `optimization_and_convexity` | LP/Farkas, convexity, KKT, SDP, descent, line search, projections, proximal steps | QF_LRA/Farkas, QF_NRA, Lean horizon | duality/working-set/strong-Wolfe variants only when distinct |
| `numerical_analysis` | residuals, Euler steps, interval/error recurrence, finite algorithms | QF_LRA/Farkas, replay, Lean horizon | pivoting/stability metadata and exact-vs-floating examples |
| `differential_equations_and_dynamical_systems` | recurrences, Euler traces, invariants, finite hitting times | QF_LRA/Farkas, replay, Lean horizon | transition/invariant variants with explicit continuous-theory boundary |
| `geometry` | coordinate, incidence, affine, rigid, circle, inversion, cyclic geometry | QF_LRA/Farkas, replay, QF_NRA horizon | nontrivial circle-line or polynomial-geometry rows with checked artifacts |
| `functional_analysis_and_operator_theory` | finite operators, inner products, projections, Chebyshev slices | QF_LRA/Farkas, replay, Lean horizon | finite approximation/alternation rows plus Banach/Hilbert horizons |

## Educational Content Plan

The learner surface should be a guided collection of runnable proof/checking
walkthroughs.

Required page pattern:

1. State the concept in ordinary mathematical language.
2. State the finite, bounded, or computable slice Axeyum can check.
3. Link the exact example pack and check rows.
4. Show the witness, counterexample, or certificate route.
5. State what remains theorem horizon.
6. Include a validation command.

Curriculum course modules:

| Module | Covers | Learner Pages |
|---|---|---|
| Foundations of checking | logic, predicates, proof methods, induction, sets | cluster page plus focused SAT/CNF, finite predicate, induction, finite set, relation/function pages |
| Number systems and arithmetic | naturals, integers, rationals, reals, complex | exact arithmetic, totality, Farkas, bounded real shadows, real-pair complex pages |
| Algebra and number theory | gcd, modular arithmetic, groups, rings, fields, polynomials | finite algebra tables, homomorphisms, ideals, modules, tensors, fixed-width BV rows |
| Analysis and topology | sequences, limits, metric spaces, compactness, connectedness, continuity | finite shadows plus theorem-horizon map |
| Linear algebra and optimization | matrices, vector spaces, numerical rows, LP/KKT/SDP/descent | matrix-computation index plus focused end-to-end pages |
| Graph and discrete reasoning | graph coloring, reachability, traversal, matching, cuts, counting | finite graph replay and CNF/LIA proof routes |
| Probability, statistics, measure | PMFs, integration, kernels, Markov chains, martingales, tests | exact finite table replay and Farkas/count certificates |
| Geometry and computation | coordinate, affine, rigid, circle, inversion, cyclic rows | exact rational geometry replay and theorem boundaries |
| Functional/numerical frontier | operators, Chebyshev systems, residuals, dynamics | finite-dimensional rows plus Banach/Hilbert/convergence horizons |
| Rules/law transfer | predicates, thresholds, precedence, reachability, temporal rules | rule examples that point back to math packs and proof routes |

The learner spine is complete when every non-template pack appears either in a
focused page or in a named combined page, and every page says `checked`,
`replay-only`, or `Lean horizon` honestly.

## Ontology And Taxonomy Plan

The concept atlas should stay small enough to be useful, not a duplicate of the
example-pack list.

Build rules:

- one row for every curriculum node;
- one row for every math field;
- bridge rows only for vocabulary reused across multiple packs or consumers;
- example-family rows only for repeated proof/solver shapes;
- every row must name proof routes, example packs, open gaps, and graduation.

Near-term bridge-row queues:

| Queue | Examples | Why |
|---|---|---|
| proof object anatomy | CNF/LRAT, Farkas, Alethe, QF_BV DRAT, Diophantine | makes checked UNSAT teachable |
| finite model replay | finite countermodels, table replay, exact witness recomputation | shared by almost every pack |
| quotient and structure maps | quotient maps, kernels/images, ideals, modules, tensors | spans algebra, topology, and rules |
| analysis theorem boundaries | metric balls, epsilon-delta, compactness, convergence, measure limits | prevents bounded-overclaiming |
| matrix computation | LU, rank, residuals, projections, eigenpairs, random moments | makes linear-algebra resources discoverable |
| probability/statistics tables | PMFs, pushforwards, conditionals, kernels, martingales, tail bounds | shared finite-table structure |
| rules/law patterns | eligibility, thresholds, precedence, temporal versions, reachability | downstream reuse without a new ontology too early |

Schema changes should be rare. Prefer adding rows and validator checks before
adding new schema fields.

## Example Pack Plan

Each pack is a small executable mathematical object.

Minimum pack contents:

- `README.md`: audience, scope, theorem boundary, related learner page.
- `metadata.json`: fields, curriculum nodes, concepts, proof routes,
  validation command, solver reuse metadata.
- `model.md`: finite object, symbols, assumptions, encoding sketch.
- `checks.md`: row-by-row trust story.
- `expected.json`: machine-readable expected results and proof status.
- optional `smt2/`, `cnf/`, `proof/`, or generated artifacts when stable.

Pack categories:

| Category | Build Pattern | Add New Pack When |
|---|---|---|
| finite structure | object table plus law checks | the object/law is materially different from existing packs |
| arithmetic certificate | integer/rational obstruction plus witness/certificate | it adds a reusable Diophantine, Farkas, or BV pattern |
| matrix computation | fixed exact matrix and replayed computation | it adds a new computation family or route |
| graph/discrete | fixed graph or finite family plus witness/refutation | it exercises a new finite graph property or proof route |
| analysis shadow | bounded finite/rational instance plus theorem horizon | it clarifies a common overclaim boundary |
| probability/statistics table | finite sample space/table plus exact replay | it adds a new table operation or certificate |
| rules/law example | finite policy/rule object plus proof fixture | it reuses an existing math shape with clear application value |

Prefer upgrading an existing pack when the proposed work is only another row in
the same object family and proof route.

## Proof And Certificate Plan

Checked evidence should become normal for representative negative rows.

| Route | Use For | Build Pattern | Exit Signal |
|---|---|---|---|
| finite replay | SAT witnesses and computed facts | recompute the source object independently | replay step is named in `checks.md` |
| Boolean CNF/LRAT | graph, counting, finite topology, set-family refutations | source object -> CNF -> DRAT/LRAT -> tamper regression | corrupted proof fails |
| QF_BV DRAT | fixed-width residues, finite rings/fields, bit encodings | source object -> BV -> CNF/DRAT -> original replay | width is part of the lesson |
| QF_LIA/Diophantine | gcd, counts, modular obstructions, torsion | exact integer relation plus divisibility certificate | regression checks certificate route |
| QF_LRA/Farkas | rational tables, LP, geometry, numerical/optimization steps | exact linear conflict plus Farkas certificate | source artifact and regression both link pack |
| QF_UF/Alethe | functions, quotients, homomorphisms, actions, modules | table replay plus congruence proof | Alethe proof checks the equality conflict |
| Lean horizon | induction, completeness, compactness, convergence, infinite-dimensional facts | theorem statement, prerequisites, missing reconstruction dependency | finite rows are not counted as theorem proof |

Route upgrades should land one checked negative row at a time unless the edit is
mechanical documentation.

## Solver Feedback Plan

Educational resources become solver assets only after the math is stable.

Promotion rule:

```text
stable source object
+ deterministic replay
+ named proof/certificate route
+ source artifact or regression back-link
= promoted solver-reuse row
```

Solver feedback categories:

| Category | Resource Sources | Solver Pressure |
|---|---|---|
| clause learning | graph coloring, pigeonhole, topology/set-family conflicts | Boolean CNF/LRAT |
| bit-blast lowering | fixed-width residues, finite fields/rings, bit-encoded graph rows | QF_BV/DRAT |
| integer obstruction | gcd, CRT, counts, torsion, exact statistical counts | QF_LIA/Diophantine |
| rational infeasibility | LP, residuals, geometry, probability/measure tables | QF_LRA/Farkas |
| congruence/equality | functions, quotients, homomorphisms, modules, actions | QF_UF/Alethe |
| algebraic real pressure | RCF shadows, polynomial roots, nonlinear geometry | QF_NRA/RCF |
| theorem reconstruction | induction, completeness, compactness, convergence, measure | Lean/Alethe-to-Lean |

Do not treat these rows as performance benchmarks until they have committed
corpus membership and measured numbers.

## Rules And Law Transfer Plan

Rules/law resources should reuse math-resource shapes instead of inventing a
separate trust model.

| Rule Pattern | Math Source | Example Resource Shape | Proof Route |
|---|---|---|---|
| eligibility predicates | finite predicates, sets, relations | applicant facts, finite rule conditions, counterexample witnesses | finite replay, Bool/CNF |
| arithmetic thresholds | integers, rationals, linear optimization | caps, phase-outs, benefits, tax brackets | QF_LIA, QF_LRA/Farkas |
| exceptions and precedence | logic, lattices, partial orders | rule priority graph and exception conditions | Bool/CNF, QF_UF |
| temporal effective dates | intervals, order, finite traces | versioned rule windows and date comparisons | QF_LIA, finite replay |
| authorization | relations/functions, graph reachability | users, roles, resources, paths | finite replay, Bool/CNF |
| allocation and constraints | LP, counting, finite probability | budgets, quotas, monotonicity, feasibility | QF_LRA/Farkas, QF_LIA |

Stop line: statutory interpretation, live legal citations, jurisdictional
conflicts, and natural-language parsing are outside the current trusted checker.

## Consumer And Library Plan

Keep the public boundary boring until usage proves otherwise.

Current public contract:

- concept atlas schema and generated JSON;
- example-pack schema, metadata, and expected-result JSON;
- generated Markdown dashboards;
- dependency-free consumer and query scripts;
- learner pages and route matrices.

Possible future splits:

| Boundary | Trigger | Contents |
|---|---|---|
| `axeyum-foundational-data` crate | three consumers duplicate typed parsing | generated Rust types and validated row readers |
| `axeyum-math-examples` crate | encoders are reused outside validators/tests | finite graph, matrix, algebra, topology, probability encoders |
| standalone resource repo | external course/site/corpus needs independent release cadence | lessons, packs, dashboards, larger artifacts |
| rules/law sibling repo | policy packs need domain schema and release cadence | rule schemas, rule examples, temporal/precedence graph |
| generated website | learner traffic and navigation exceed mdBook pages | searchable curriculum/resource site over committed JSON |

Do not split because the tree is large. Split only when repeated use proves the
boundary.

## Milestones

### Milestone 0: Preserve The Current Contract

Exit criteria:

- `./scripts/check-foundational-resources.sh` passes.
- `python3 scripts/query-foundational-resources.py summary` shows zero
  unclassified solver-reuse rows.
- Planning counts agree with generated dashboards.

### Milestone 1: Make Discovery Reliable

Exit criteria:

- users can query by curriculum node, field, concept, proof route, proof
  status, and solver-reuse status;
- `FIELD-READINESS-QUERY-MATRIX.md` and `PROOF-ROUTE-QUERY-MATRIX.md` cover
  all active fields/routes;
- broad learner cluster pages link to focused pages or named indexes.

### Milestone 2: Complete The Learner Spine

Exit criteria:

- every non-template pack appears in a focused learner page or named combined
  page;
- each page includes a validation command;
- each page states bounded slice versus theorem horizon.

### Milestone 3: Upgrade Representative Proof Evidence

Exit criteria:

- every active route has at least one end-to-end checked learner story;
- each route has at least one tamper/corruption rejection;
- replay-only rows are a deliberate queue, not hidden debt.

### Milestone 4: Add Missing Curriculum Depth

Exit criteria:

- new packs fill field holes, proof-route holes, or solver-pressure holes;
- no new pack duplicates an existing object/route without a stated reason;
- theorem horizons are represented as explicit rows, not omitted.

### Milestone 5: Turn Resources Into Solver Feedback

Exit criteria:

- promoted rows cite deterministic source artifacts or regressions;
- solver tests link back to packs and packs link to tests;
- benchmark claims require committed corpora and measured results.

### Milestone 6: Externalize Only Proven Boundaries

Exit criteria:

- consumer scripts show repeated access patterns;
- at least three consumers or one external release-cadence need justify a
  crate/repo split;
- boundary decisions cite actual usage.

## Commit-Sized Execution Queue

Prefer one row, page, route upgrade, or query surface per commit.

1. Keep this comprehensive plan linked from the foundational-resource index,
   mdBook summary, buildout plan, and live status.
2. Landed: [Learner Coverage Audit](LEARNER-COVERAGE-AUDIT.md) records that
   the current 108 non-template packs are all focused-lesson linked, with no
   path-only, index-only, or missing learner buckets, and defines the future
   combined-page-only policy.
3. Landed: [Proof Route Family Selection](PROOF-ROUTE-FAMILY-SELECTION.md)
   picks one representative replay-heavy family per active proof route,
   records the current checked-row representative, and defines when another
   compact negative row is worth promoting.
4. Landed: [Proof Route Learner Snippets](../learn/math/proof-route-learner-snippets.md)
   gives reusable trust-boundary snippets for Farkas, Alethe, Diophantine,
   CNF/LRAT, and QF_BV DRAT rows.
5. Landed: deepen probability rows with a distinct finite distribution-distance
   conflict, not another duplicate product-table check.
   `finite-probability-v0` now includes a total-variation witness over two
   three-atom distributions plus a source-linked checked bad total-variation
   row. Exact replay computes the absolute-difference table and `TV=1/6`;
   the QF_LRA/Farkas artifact rejects the malformed claim `TV=1/4`.
6. Landed: deepen graph resources by adding small CNF/LRAT examples where the source
   graph is learner-readable.
   `graph-d-separation-v0` now promotes the unconditioned collider blocker
   `a -> b <- c` with no conditioning through a source-linked DIMACS artifact.
   The Boolean route emits DRAT, elaborates to LRAT, and independently checks
   both proof objects, giving the graph lane a distinct collider-specific proof
   shape alongside the existing conditioned-chain blocker.
7. Landed: deepen linear algebra through source-linked matrix-corpus rows only
   after the pack/learner/regression triangle is explicit.
   The matrix-corpus regression pass now makes least-squares bad coefficients,
   numerical residual bounds, finite random-matrix trace-square moments,
   spectral bad eigenpairs, and matrix-invariant bad characteristic
   polynomials prove their committed SMT-LIB artifacts directly through the
   shared QF_LRA/Farkas route tests. The strict-inequality inner-product
   negative-norm row remains checked by its existing inline Farkas regression
   until the SMT-LIB parser/evidence path accepts that artifact shape.
8. Landed: deepen real analysis through theorem-boundary pages before adding
   more bounded examples.
   [`real-completeness-theorem-boundary.md`](../learn/math/real-completeness-theorem-boundary.md)
   now maps least-upper-bound completeness, Cauchy completeness, monotone
   convergence, RCF shadows, metric continuity, and compactness prerequisites
   to existing checked packs and copyable queries. It keeps finite rational
   rows as executable examples and names the missing no-`sorry` Lean theorem
   dependencies before any completeness claim can graduate.
9. Landed: deepen algebra by adding equality/certificate rows only when table
   replay and congruence proof tell different useful stories.
   [`algebra-equality-certificate-boundary.md`](../learn/math/algebra-equality-certificate-boundary.md)
   and `bridge_algebra_equality_certificate_boundary` now make that rule
   queryable: exact finite replay must identify the bad equality, closure,
   representative, preservation, identity-action, action-compatibility, or
   bilinearity obligation
   before a scoped QF_UF/Alethe row can claim checked certificate value.
10. Landed: add `bridge_polynomial_coefficient_factor_replay` for fixed
    polynomial coefficients, factor/division witnesses, coefficient windows,
    root-finding steps, derivative shadows, and polynomial geometry obligations;
    keep general factorization and algebraic closure as proof horizons.
11. Landed: add
    [`procurement-scoring-v0`](../rules-as-code/examples/procurement-scoring-v0/)
    as the next rules/law example, reusing finite predicate exclusions,
    bid-cap and deadline arithmetic, bonus-threshold replay, score
    monotonicity, and Bool/QF_LIA proof fixtures through the current JSON
    boundary.
12. Landed: add
    [`grant-allocation-v0`](../rules-as-code/examples/grant-allocation-v0/)
    as the rational-allocation rules/law example, reusing exact rational
    shares, budget balance, minimum-share floors, administrative caps, finite
    replay, and QF_LRA/Farkas checked fixtures through the current JSON
    boundary.
13. Landed: add
    [`RULES-LAW-QUERIES.md`](RULES-LAW-QUERIES.md) and
    `scripts/query-rules-as-code.py` so downstream consumers can query rule
    packs, checked obligations, generated query families, and bounded generated
    rows without parsing JSON by hand.
14. Landed: add
    [`RULES-LAW-PATTERN-MATRIX.md`](RULES-LAW-PATTERN-MATRIX.md) so the current
    rule-pattern surface maps back to math concept rows, proof routes, pack
    checks, generated query families, and copyable query commands.
14. Landed: add
    [`rules-law-trust-boundary.md`](../learn/rules-law-trust-boundary.md) so the
    current rules/law packs have a learner-facing source-rule, formal-model,
    replayed-witness, checked-obligation, and horizon walkthrough.
15. Add rules/law examples only by reusing existing math proof shapes and the
    current JSON boundary.
16. Add schema fields only after validators and query scripts show repeated
    awkwardness.
17. Revisit crate/repo boundaries after consumer scripts have at least three
    duplicated access patterns.

## Validation Protocol

For plan-only or navigation edits:

```sh
git diff --check
./scripts/check-links.sh
```

For generated-data, pack, metadata, or solver-reuse edits:

```sh
./scripts/check-foundational-resources.sh
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary
```

For proof-route promotions:

```sh
# plus the route-specific regression named by the pack metadata
cargo test -p axeyum-solver --test <route-test> <test-name>
```

## Anti-Patterns

- Do not add a bare concept row with no example, validator, or horizon
  dependency.
- Do not call a finite bounded check a theorem.
- Do not create a new pack when an existing pack needs a row, learner page, or
  proof upgrade.
- Do not promote a row into benchmark language without source replay and
  measured corpus results.
- Do not create a separate crate or repository because the documentation tree
  is large.
- Do not let rules/law examples invent a second trust model.
