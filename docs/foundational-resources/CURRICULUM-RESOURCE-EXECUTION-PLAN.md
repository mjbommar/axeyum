# Curriculum Resource Execution Plan

## Purpose

This is the forward execution plan for turning the
[formal mathematics curriculum](../curriculum/README.md) into a durable
resource ecosystem. The companion
[Math Curriculum Resource Buildout Plan](MATH-CURRICULUM-BUILDOUT.md) records
the phase contract and landed history; the
[Math Curriculum Implementation Matrix](MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md)
gives the per-node/per-field build matrix; the
[Math Curriculum Detailed Build Plan](MATH-CURRICULUM-DETAILED-BUILD-PLAN.md)
is the current execution ledger for the existing pack inventory, unclassified
solver-reuse rows, learner-path work, proof-route depth, and field-by-field
next steps; the
[Math Curriculum Resource Buildout Roadmap](RESOURCE-BUILDOUT-ROADMAP.md)
gives the detailed operating plan across resource families; this file says what
to build next and how to keep the work coherent.

The invariant is:

```text
curriculum node -> concept row -> example pack -> learner path -> proof route -> dashboard -> consumer/API boundary
```

Every resource should reinforce Axeyum's identity: untrusted fast search,
trusted small checking. Bounded examples are useful, but they must stay visibly
bounded until a proof route or Lean reconstruction upgrades the claim.

## Current Baseline

As of this plan, the math resource lane has:

- 23 curriculum nodes in the source DAG.
- 18 university-style field rows in [MATH-FIELDS.md](MATH-FIELDS.md).
- 94 atlas rows generated from curriculum, field data, 48 R1 bridge
  concepts for finite replay, counterexample proof, bounded theorem shadows,
  proof-method and finite-logic vocabulary, proof-object anatomy vocabulary,
  set/foundations vocabulary, analysis/topology boundary vocabulary,
  linear-algebra computation vocabulary, probability/statistics finite-table
  vocabulary, measure-theory additivity/product/integration vocabulary,
  optimization/convexity LP and finite-shadow vocabulary, algebra-map
  vocabulary, coordinate/incidence/rigid/oriented geometry replay, complex real-pair
  transform replay, finite inner-product/projection replay, finite
  operator/Chebyshev replay, and Lean horizons, plus five route-specific
  example families.
- 94 non-template math example packs, plus the validating template pack.
- generated coverage, curriculum-status audit, field, proof-gap,
  learner/proof-upgrade, and curriculum-pressure dashboards under
  [generated/](generated/).
- learner paths under [docs/learn/math](../learn/math/README.md).
- a stable in-repo data boundary through JSON schemas, validators, generated
  dashboards, and `scripts/consume-foundational-resources.py`.

That is broad enough that the next work is no longer "make examples exist."
The next work is to make the examples systematic, navigable, evidence-upgraded,
and reusable by downstream resource projects.

## Maturity Ladder

| Level | Artifact | Gate | Graduation Signal |
|---|---|---|---|
| L0 | curriculum node or field row | validates in `foundational-concepts.json` | node has field IDs, decidability, fragments, gaps, and pack targets |
| L1 | example pack | `validate-foundational-example-pack.py` passes | SAT witnesses replay and UNSAT/UNKNOWN rows state proof status |
| L2 | learner page | docs link check passes | page names what Axeyum checks, what it does not, and how to replay it |
| L3 | proof route | proof cookbook recipe linked | UNSAT rows have checked evidence or a named missing route |
| L4 | solver feedback | pack family maps to fragments | examples become fuzz, corpus, or regression inputs for solver work |
| L5 | consumer data | downstream smoke test passes | external code reads schemas/JSON without repo-internal assumptions |
| L6 | sibling boundary | ADR or boundary decision | crate or separate repo exists only after repeated consumer demand |

Do not skip levels silently. A pack may stay at L1 for a long time, but it
should not be described as a general theorem or a complete lesson until L2/L3
work has landed.

## Workstreams

### A. Canonical Status And Coverage

Goal: make the generated dashboards tell the truth without hand-maintained
interpretation.

Concrete work:

- Keep a generated status-audit view that separates source
  `curriculum_status` from generated `resource_status`.
- Review curriculum rows that still say `planned` after their resource packs
  validate, and decide whether the source row should become `covered` for a
  mature finite/computable slice or `lean-horizon` for the general theorem.
- Add a generated "needs learner page" and "needs proof upgrade" view instead
  of relying on manual scans.
- Add generated R0-R6 "gate" and "next gate" columns so solver-reuse and
  consumer-boundary candidates are visible without manual row audits.
- Add a generated curriculum-pressure-by-fragment view so solver/proof demand
  is grouped by Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, finite replay, and
  Lean horizon without hand-maintained scans.
- Keep consumer field-readiness smokes representative: probability/Farkas now
  covers finite table-probability resources, dynamics/Farkas covers
  recurrence, Euler, stochastic-kernel, and hitting-time resources, and
  measure/Farkas covers finite event-algebra, product-measure, integration,
  random-variable, conditional-expectation, and stochastic-process resources.
  Optimization/Farkas covers exact LP thresholds, finite convexity shadows,
  finite KKT stationarity replay, finite SDP objective/slack replay, finite
  gradient-descent step replay,
  least-squares normal equations, residual bounds, gradient/Hessian replay, and
  related matrix checks without promoting duality, KKT sufficiency, SDP strong
  duality, or convergence theorem claims.
- Keep all status changes generated from `curriculum.toml`,
  [MATH-CURRICULUM-BUILDOUT.md](MATH-CURRICULUM-BUILDOUT.md), and pack metadata.

Exit criteria:

- `scripts/check-foundational-resources.sh` regenerates identical dashboards on
  a clean checkout.
- Every `planned` curriculum row has a reason: missing pack, bounded-only
  shadow, proof-route gap, Lean horizon, or explicit source-status review in
  [generated/curriculum-status-audit.md](generated/curriculum-status-audit.md).

### B. Learner Path Completion

Goal: make every validated pack discoverable from a clear educational path.

Concrete work:

- Keep the nine cluster pages as the stable table of contents.
- Add or split focused end-to-end lessons when a pack has enough substance that
  a learner should not have to read a broad cluster page.
- Prefer combined lessons only when the concepts are naturally inseparable,
  such as coordinate/affine/oriented geometry or descriptive statistics plus
  least-squares regression.
- Add a short "Run It" command to every focused lesson and keep it aligned with
  pack metadata.

High-priority focused lessons still worth auditing or adding:

- finite probability, finite measure, and finite measure monotonicity as
  separate first-principles lessons;
- linear optimization as a standalone LP/Farkas bridge;
- finite topology as a standalone topology-axiom/closure/interior bridge;
- finite operators now have a standalone finite-dimensional
  norm/operator-bound bridge;
- bounded dynamics now has a standalone recurrence/invariant bridge;
- finite Euler now has a standalone numerical-step/error-table bridge.
- finite root finding now has a standalone exact bisection/Newton replay
  bridge.
- finite separation now has a standalone exact convex-hull and
  separating-hyperplane replay bridge.
- finite KKT now has a standalone constrained-quadratic stationarity and
  complementary-slackness replay bridge.
- finite SDP now has a standalone two-by-two PSD, objective, slack, and
  dual-gap replay bridge.
- finite gradient descent now has a standalone exact quadratic step, objective
  decrease, and descent-bound replay bridge.

Exit criteria:

- Every non-template pack appears in either a focused lesson or an explicitly
  named combined lesson.
- `docs/learn/math/README.md` remains the single learner index.

### C. Proof And Certificate Upgrades

Goal: move important packs from replay-only to checked evidence wherever the
solver stack already has or should soon have the certificate machinery.
The live route-by-route execution frontier is
[PROOF-UPGRADE-FRONTIER.md](PROOF-UPGRADE-FRONTIER.md); the generated queue it
interprets is
[generated/learner-proof-upgrade-dashboard.md](generated/learner-proof-upgrade-dashboard.md).

Priority proof upgrades:

| Route | Packs To Mine First | Reason |
|---|---|---|
| CNF/LRAT | graph coloring, pigeonhole, finite counting refutations | smallest trusted-small-checking story |
| QF_LRA/Farkas | rationals, LP, convexity, linear systems, finite concentration bounds | exact rational arithmetic with strong certificate story |
| QF_LIA/Diophantine | gcd, integer linear arithmetic, exact statistical tests, homology rank rows | common arithmetic obstruction pattern |
| QF_UF/Alethe | equivalence classes, functions, finite algebra homomorphisms, monoids, ideals | equality-heavy finite structure and quotient congruence checks |
| Lean horizon | induction, limits, compactness, measure, general algebra, Chebyshev spaces | general theorem layer beyond bounded replay |

Exit criteria:

- The proof-gap dashboard groups gaps by route, not only by pack.
- At least one lesson per major route shows the end-to-end trust boundary:
  untrusted search result, small replay/certificate check, and current Lean
  status.

### D. Concept Granularity Expansion

Goal: stop treating each curriculum node as a single concept once the first
pack has landed.

Add bridge-concept or example-family rows for repeated subtopics:

- logic: landed bridge rows for refutation-as-query, finite proof-pattern
  replay, finite quantifier expansion, and bounded induction obligations;
  general induction schemas remain Lean horizon;
- proof objects: landed bridge rows for Boolean CNF DRAT/LRAT anatomy,
  QF_LRA Farkas certificate anatomy, QF_UF Alethe certificate anatomy, and
  QF_BV bit-blast certificate anatomy;
- set theory: landed bridge rows for finite Boolean algebra, finite
  partition/relation roundtrips, finite image/preimage/inverse tables, finite
  bijection/cardinality, and cardinality theorem horizons;
- algebra: landed bridge rows for homomorphism preservation, kernel/image
  replay, quotient maps, ideal closure, module actions, tensor bilinearity,
  and finite group actions;
- analysis: landed bridge rows for metric balls, bounded epsilon-delta shadows,
  compactness shadows, connectedness shadows, and continuity-by-preimage, plus
  metric continuity with checked QF_LRA/Farkas bad-delta evidence, finite
  compactness with checked Bool/CNF bad-cover evidence, finite connectedness,
  and finite integration;
- linear algebra: landed bridge rows for LU replay, rank/nullity, residual
  bounds, eigenpair witnesses, characteristic-polynomial replay, and finite
  random-matrix moments, with dual spaces, inner products, tensor maps, and
  spectral decompositions still needing narrower rows when reuse demands them;
- probability/statistics: landed bridge rows for finite probability mass
  tables, pushforward distributions, stochastic kernels, conditional
  expectation, and tail/count obstructions, backed by finite probability,
  random-variable, kernel, martingale, hitting-time, concentration, and exact
  test packs;
- measure theory: landed bridge rows for finite event-algebra/additivity,
  complement, product-table, marginal, finite Fubini-style sum, and
  simple-function integral replay, backed by finite measure, product-measure,
  integration, random-variable, conditional-expectation, and martingale packs
  while leaving Lebesgue/convergence/almost-everywhere claims as Lean horizons;
- optimization/convexity: landed bridge rows for exact LP
  objective-threshold/Farkas replay and rational convexity/gradient shadows,
  backed by linear optimization, convexity, multivariable calculus,
  least-squares, residual, finite KKT, finite SDP, finite gradient descent, and
  real-algebra packs while leaving duality, KKT sufficiency, SDP strong
  duality, line-search, and convergence claims as Lean horizons;
- geometry/complex analysis: landed bridge rows for coordinate/incidence/
  rigid/oriented geometry replay and complex real-pair transform replay, backed by
  the coordinate, incidence, rigid-configuration, affine, orientation/area,
  complex algebraic, and complex-plane transform packs while leaving synthetic/differential geometry,
  projective configuration theorems, and analytic complex analysis as Lean
  horizons;
- functional analysis/operator theory: landed bridge rows for finite
  inner-product/projection replay and finite operator/Chebyshev replay, backed
  by inner-product, numerical-linear-algebra, least-squares, finite-operator,
  finite-Chebyshev, spectral, and matrix-invariant packs while leaving Banach,
  Hilbert, compact-operator, minimax, and infinite-dimensional approximation
  theorems as Lean horizons;
- proof-route families: landed example-family rows for finite algebra
  QF_UF/Alethe congruence, exact-rational QF_LRA/Farkas infeasibility, and
  finite Boolean CNF/LRAT refutations, plus integer/count QF_LIA Diophantine
  and arithmetic-DPLL obstructions, and fixed-width QF_BV/DRAT finite
  algebra/residue/one-bit graph obligations, each tied to a shared regression
  rather than repeated prose in every pack;
- topology: finite topologies, continuous maps, and simplicial homology.

Exit criteria:

- Concept rows describe reusable mathematical ideas, not only curriculum
  headings.
- Generated field dashboards show depth within fields, not just one row per
  field.

### E. Solver Feedback And Corpus Reuse

Goal: make educational resources useful to the core solver project.

Concrete work:

- Tag each pack with the solver fragments it exercises and the gap it can
  expose: Bool/SAT, QF_BV, QF_LIA, QF_LRA, QF_NRA, QF_UF, arrays, quantifiers,
  or replay-only computation.
- Use the structured `solver_reuse` metadata object to mark candidate packs;
  do not count a candidate as R5 until a regression, fuzz, benchmark, or
  explicit non-benchmark-horizon back-link exists.
- Promote representative rows into regression or fuzz corpora only after the
  mathematical witness replay is deterministic.
- Add negative examples deliberately: bad table, bad witness, false bound,
  malformed topology, non-homomorphism, non-stochastic row.
- Keep general theorem horizons out of solver benchmark scoring until a real
  proof route exists.

Exit criteria:

- A pack can answer "what solver capability does this pressure?" without a
  human reading all prose.
- Regression promotions cite the resource pack and preserve the learner-facing
  trust story.

### F. Consumer And Sibling Boundaries

Goal: keep the resources in-repo while they are still changing quickly, then
split only when the boundary is proven.

Near-term boundary:

- JSON schemas and dashboards are the public contract.
- `scripts/consume-foundational-resources.py` is the smoke test.
- `scripts/query-foundational-resources.py` plus
  [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) are the consumer-facing sample
  query layer for summary counts, pack discovery, field-plus-proof-route
  discovery, checked-row mining, solver-reuse candidates, atlas concept
  lookup, and field-level curriculum readiness.
- No Rust crate or separate repository until at least one real consumer needs
  typed APIs, release cadence, or large external corpora.

Likely future boundaries:

- `axeyum-foundational-data`: generated typed accessors for concept rows,
  packs, proof routes, and dashboards.
- `axeyum-math-examples`: reusable finite-model encoders for graph, algebra,
  matrix, topology, and probability packs.
- rules/law reasoning resources that reuse finite predicates, graph reachability,
  optimization, and proof-route vocabulary from this math spine.

Exit criteria:

- A boundary decision cites at least three duplicated call sites or one
  external consumer.
- The split does not weaken validation, replay, or dashboard regeneration.

## Curriculum Layer Plan

### Layer 0: Foundations

Curriculum nodes: propositional logic, predicate logic, proof methods,
induction, sets, relations/functions, cardinality.

Current resource families:

- Boolean truth tables, CNF refutation, proof patterns, finite predicate
  expansion, induction obligations, finite sets, relations, functions,
  equivalence classes, lattices, finite cardinality.

Next buildout:

- Upgrade the core refutation lessons with LRAT/DRAT-oriented proof-object
  examples.
- Use the generated bridge rows for "finite model replay", "proof by
  counterexample", "bounded theorem vs general theorem", and "Lean horizon" as
  shared status vocabulary.
- Keep induction and infinite cardinality clearly Lean-horizon.

### Layer 1: Number Systems

Curriculum nodes: naturals, integers, rationals, reals, complex numbers.

Current resource families:

- bounded natural arithmetic, integer LIA, rational LRA, algebraic real/RCF
  shadows, bounded real-analysis samples, exact complex real-pair replay.

Next buildout:

- Promote repeated arithmetic obstruction patterns into QF_LIA and QF_LRA proof
  recipes.
- Split "exact rational" from "real completeness" in learner pages so users see
  why Axeyum can check one and not the other.
- Add concept rows for totality conventions, underspecified operations, and
  exact-vs-floating arithmetic if they become repeated teaching points.

### Layer 2: Core Structures And Tools

Curriculum nodes: divisibility, modular arithmetic, groups, rings, fields,
polynomials, sequences/limits, counting.

Current resource families:

- gcd/Bezout, modular arithmetic, finite groups/rings/fields, monoids,
  permutation groups, group actions, ideals, modules, tensor products,
  polynomial identities/factorization, generating functions, counting.

Next buildout:

- Add granular concept rows for kernels/images, quotients, ideals,
  orbit-stabilizer, Burnside, tensor universal property shadows, and polynomial
  division/GCD.
- Upgrade equality-heavy finite algebra packs through the QF_UF/Alethe route
  when available.
- Keep general algebra, arbitrary-field factorization, and full limit theory as
  Lean-horizon until reconstruction lands.

### Layer 3: Destinations

Curriculum nodes: number theory, linear algebra, calculus.

Current resource families:

- bounded number theory, exact rational linear algebra, finite vector spaces,
  dual spaces, inner products, modules, tensor products, spectral and matrix
  invariant rows, calculus algebraic shadows, Riemann sums, multivariable
  calculus.

Next buildout:

- Treat number theory packs as arithmetic-certificate pressure tests.
- Treat linear algebra packs as the bridge from education to solver-friendly
  matrix and optimization corpora.
- Treat calculus packs as exact algebraic shadows plus explicit proof horizons
  for continuity, differentiability, integration, and convergence.

## Field Extension Plan

| Field | Build Next |
|---|---|
| `logic_and_proof` | proof-object lessons, Lean-horizon examples, status vocabulary |
| `set_theory_and_foundations` | quotient/lattice/cardinality concept rows and finite replay lessons |
| `discrete_math` | graph search, matching, cuts, generating functions, asymptotic horizons |
| `graph_theory` | focused lessons for non-coloring graph packs and proof routes for refutations |
| `number_theory` | arithmetic certificate recipes and bounded Diophantine families |
| `linear_algebra` | matrix corpus promotion, rank/spectral proof horizons, numerical residual lessons |
| `abstract_algebra` | QF_UF/Alethe upgrades for table and homomorphism packs |
| `real_analysis` | bounded-vs-general concept rows for limits, continuity, compactness, integration |
| `complex_analysis` | real-pair algebra lessons now; analytic theorem rows as Lean horizon |
| `topology` | standalone finite topology lesson landed; maintain granular compactness/connectedness/homology rows |
| `measure_theory` | standalone finite measure and monotonicity lessons landed; keep Lebesgue/convergence theorem rows Lean-horizon |
| `probability_theory` | standalone finite probability mass-table lesson landed; maintain stochastic-process path through kernels/Markov chains |
| `statistics` | exact finite tests, regression, concentration, and explicit numerical-honesty status |
| `optimization_and_convexity` | standalone LP/Farkas, finite KKT, finite SDP, and finite gradient-descent lessons landed; maintain convexity/gradient/Hessian bridge rows |
| `numerical_analysis` | residual/error-bound examples with exact rational shadows and numerical limits |
| `differential_equations_and_dynamical_systems` | bounded recurrence/Euler lessons plus invariant-counterexample rows |
| `geometry` | rigid-configuration lesson landed; keep combined coordinate/affine/orientation lesson and add only distinct isometry or polynomial-geometry rows later |
| `functional_analysis_and_operator_theory` | finite operator and Chebyshev-system lessons; keep Banach/Hilbert theorems Lean-horizon |

## Forward Increments From Here

1. Landed: add generated learner-coverage, proof-upgrade gap, and
   curriculum-pressure-by-fragment views.
2. Landed: add generated curriculum-status audit so `planned` source rows with
   validated resources are surfaced for review; generated `resource_status`
   now reflects resource maturity (`validated`, `proof-horizon`, or
   `planned`) rather than a historical seed marker.
3. Add focused graph lessons for reachability, search runtime, matching, cuts,
   and d-separation.
4. Landed: add standalone finite probability and finite measure lessons. The
   finite probability mass-table page now follows exact PMF normalization,
   conditional probability replay, Bayes posterior replay, checked QF_LRA/Farkas
   bad-normalization rejection, and checked bad-posterior rejection; the finite
   measure page follows finite sigma-algebra replay, exact finite additivity,
   event complements, and checked QF_LRA/Farkas bad-complement rejection.
   `docs/learn/math/finite-measure-monotonicity-end-to-end.md` now follows
   normalized finite measure-table replay, subset monotonicity, union
   subadditivity, checked QF_LRA/Farkas bad subset-measure rejection, and the
   convergence/countable-measure Lean horizon.
5. Landed: add standalone linear optimization and finite topology lessons. The
   finite topology page now follows topology axiom replay, closure/interior
   replay, exact metric-ball replay, and checked Bool/CNF missing-empty-set
   rejection; the linear optimization page now follows exact LP feasible-point
   replay, objective-threshold replay, checked QF_LRA/Farkas
   infeasible-threshold evidence, and tampered-certificate rejection.
6. Landed: add bridge-concept rows for finite model replay, proof by
   counterexample, bounded theorem shadows, metric balls, bounded epsilon-delta
   shadows, compactness shadows, connectedness shadows, continuity-by-preimage,
   and Lean horizons.
7. Landed: add bridge-concept rows for linear-algebra computation vocabulary:
   LU replay, rank/nullity replay, residual bounds, eigenpair witnesses,
   characteristic-polynomial replay, and finite random-matrix moments.
8. Landed: add bridge-concept rows for algebra-map vocabulary: homomorphism
   preservation, kernel/image replay, quotient maps, ideal closure, module
   actions, tensor bilinearity, and finite group actions.
9. Landed: add bridge-concept rows for probability/statistics finite-table
   vocabulary: finite probability mass tables, pushforward distributions,
   stochastic kernels, conditional expectation, and tail/count obstructions.
10. Landed: add bridge-concept rows for measure-theory finite-table and
   integration vocabulary: finite measure additivity and finite
   product-measure/integration replay, keeping Lebesgue measure, general
   product measures, convergence theorems, and almost-everywhere claims in the
   Lean-horizon lane.
11. Landed: add bridge-concept rows for proof-method and finite-logic
   vocabulary: refutation-as-query, finite proof-pattern replay, finite
   quantifier expansion, and bounded induction obligations.
12. Landed: add bridge-concept rows for proof-object anatomy vocabulary:
   Boolean CNF DRAT/LRAT anatomy, QF_LRA Farkas certificate anatomy, QF_UF
   Alethe certificate anatomy, and QF_BV bit-blast certificate anatomy.
13. Landed: add bridge-concept rows for set/foundations vocabulary: finite
   Boolean algebra, finite partition/relation roundtrips, finite
   image/preimage/inverse tables, finite bijection/cardinality, and
   cardinality theorem horizons.
14. Landed: add "math example using this route" sections to the six active proof
   cookbook recipes so proof-route docs point back to concrete packs.
15. Add QF_LRA/Farkas upgrade rows for rational, LP, convexity, concentration,
   linear-system, and probability/statistics table examples.
   Status: `family_exact_rational_farkas` now groups the recurring checked
   exact-rational infeasibility rows and ties them to the shared
   `math_resource_lra_routes` regression; finite concentration, finite
   conditional expectation, finite hitting times, finite Euler method, and
   finite stochastic kernels now add source-linked probability/statistics and
   dynamics/numerics seeds to that route.
15. Add QF_UF/Alethe upgrade rows for equivalence, function, and finite algebra
   examples.
   Status: the first high-use learner-page route-note pass now names these
   routes and their trust boundaries; `family_finite_algebra_alethe` now groups
   the recurring checked finite-algebra EUF/Alethe conflicts, including the
   finite-ideals quotient representative congruence row through the shared
   `math_resource_uf_routes` regression.
   Dashboard status: generated R0-R6 gate and next-gate columns now make
   R4-to-R5 solver-reuse candidates visible in the coverage, field, proof-gap,
   and learner/proof-upgrade dashboards. The curriculum-status audit now shows
   where source `planned` rows have validated resources and need a source DAG
   decision. The curriculum-pressure view now groups the 94 non-template packs
   into overlapping Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, finite-replay, and
   Lean-horizon buckets for fragment-level planning.
   Candidate status: the first `solver_reuse` batch is now fully promoted:
   `logic-basics-v0`,
   `finite-cardinality-v0`, `graph-matching-v0`, `graph-reachability-v0`,
   `graph-cut-v0`, `graph-d-separation-v0`, and
   `graph-search-runtime-v0`, `integer-lia-v0`, and
   `natural-arithmetic-v0`, plus `number-theory-v0`, have moved from
   candidate to promoted for their source-linked regression artifacts.
12. Landed: add consumer-facing sample queries over the JSON data contract.
   `scripts/query-foundational-resources.py` now supports summary, pack, check,
   concept, and field-readiness queries including field-plus-proof-route
   discovery, and `check-foundational-resources.sh` runs a small query smoke
   set. The smoke set now also covers measure-theory Farkas field readiness,
   measure bridge concept lookup, and checked measure-theory Farkas rows,
   tying finite measure, product-measure, integration, random-variable,
   conditional-expectation, finite measure monotonicity, martingale, kernel,
   hitting-time, and concentration packs to the public JSON consumer boundary.
   It now also covers
   optimization/convexity Farkas field readiness, LP-objective and convexity
   bridge lookups, and checked optimization Farkas rows, tying LP thresholds,
   convexity shadows, finite KKT stationarity, finite SDP objective/slack
   replay, finite gradient-descent replay, least-squares, gradients, residual
   bounds, and matrix witnesses to the same boundary.
13. Landed: add negative fixtures for the foundational example-pack schema.
   `scripts/check-foundational-negative-fixtures.py` now asserts that invalid
   packs with unknown fields, metadata/check id drift, and missing witness
   references fail with expected diagnostics; `check-foundational-resources.sh`
   runs the negative-fixture check.
14. Landed: add route-specific tamper/rejection regressions for the active
   proof-certificate routes. Boolean CNF/LRAT, QF_BV DRAT, QF_LRA/Farkas,
   QF_LIA/Diophantine, and QF_UF/Alethe now each mutate an emitted resource
   certificate and require independent checker rejection.
15. Landed: promote `finite-group-actions-v0` through a source-linked
   QF_UF/Alethe regression for the `bad-action-rejected` identity-action
   conflict:
   `artifacts/examples/math/finite-group-actions-v0/smt2/bad-identity-action-alethe-conflict.smt2`
   is checked by
   `cargo test -p axeyum-solver --test math_resource_uf_routes finite_group_actions_bad_identity_emits_checked_alethe`.
16. Landed: promote `finite-continuous-maps-v0` through a source-linked
   QF_UF/Alethe regression for the `bad-continuous-map-rejected`
   preimage-membership conflict:
   `artifacts/examples/math/finite-continuous-maps-v0/smt2/bad-preimage-membership-alethe-conflict.smt2`
   is checked by
   `cargo test -p axeyum-solver --test math_resource_uf_routes finite_continuous_maps_bad_preimage_emits_checked_alethe`.
17. Promote selected packs into solver regression/fuzz corpora with back-links
   to the resource pack.
   Status: first promotions landed for `logic-basics-v0` via
   `artifacts/examples/math/logic-basics-v0/cnf/tiny-cnf-refutation.cnf` and
   `finite-cardinality-v0` via
   `artifacts/examples/math/finite-cardinality-v0/cnf/no-injection-four-to-three.cnf`;
   `graph-matching-v0` now adds
   `artifacts/examples/math/graph-matching-v0/cnf/triangle-no-perfect-matching.cnf`.
   `graph-reachability-v0` now adds
   `artifacts/examples/math/graph-reachability-v0/cnf/disconnected-no-path.cnf`.
   `graph-cut-v0` now adds
   `artifacts/examples/math/graph-cut-v0/cnf/one-edge-cut-rejected.cnf`.
   `graph-d-separation-v0` now adds
   `artifacts/examples/math/graph-d-separation-v0/cnf/chain-conditioned-blocks.cnf`.
   All Boolean rows are checked from
   `crates/axeyum-cnf/tests/math_resource_boolean_routes.rs`.
   `graph-search-runtime-v0` now adds
   `artifacts/examples/math/graph-search-runtime-v0/smt2/bad-dfs-cost-bound-lia-conflict.smt2`,
   checked from
   `crates/axeyum-solver/tests/math_resource_lia_routes.rs`.
   `integer-lia-v0` now adds
   `artifacts/examples/math/integer-lia-v0/smt2/diophantine-gcd-obstruction-conflict.smt2`,
   checked from the same LIA resource regression.
   `natural-arithmetic-v0` now adds
   `artifacts/examples/math/natural-arithmetic-v0/smt2/bounded-natural-negative-lia-conflict.smt2`,
   checked from the same LIA resource regression.
   `number-theory-v0` now adds
   `artifacts/examples/math/number-theory-v0/smt2/quadratic-nonresidue-mod7-bitblast-conflict.smt2`,
   checked from `crates/axeyum-solver/tests/math_resource_bv_routes.rs`.
   `finite-connectedness-v0` now adds
   `artifacts/examples/math/finite-connectedness-v0/cnf/bad-connected-claim-rejected.cnf`,
   checked from `crates/axeyum-cnf/tests/math_resource_boolean_routes.rs`.
   `finite-chebyshev-systems-v0` now adds
   `artifacts/examples/math/finite-chebyshev-systems-v0/smt2/bad-duplicate-node-grid-farkas-conflict.smt2`,
   checked from `crates/axeyum-solver/tests/math_resource_lra_routes.rs`.
   `finite-ideals-v0` now adds
   `artifacts/examples/math/finite-ideals-v0/smt2/quotient-ring-representative-congruence-conflict.smt2`,
   checked from `crates/axeyum-solver/tests/math_resource_uf_routes.rs`.
11. Landed: add
    [RULES-LAW-CROSSWALK.md](RULES-LAW-CROSSWALK.md), a rules/law reasoning
    resource plan that explicitly reuses finite predicates, arithmetic
    thresholds, graph reachability, precedence, optimization, and proof-route
    vocabulary. Source-linked Bool/QF_LIA fixtures now check
    `benefit-eligibility-v0` consistency, coverage, fixed no-exception
    monotonicity, and active-threshold implementation equivalence through
    `crates/axeyum-solver/tests/rules_as_code_examples.rs`. The second
    rules/law pack, `authorization-policy-v0`, now reuses finite
    tenant/resource relations, precedence, bounded version deltas, and checked
    Bool/QF_LIA fixtures for tenant isolation, explicit deny precedence, admin
    tenant guarding, and implementation equivalence. Next work is generated
    multi-row queries or the tax-benefit arithmetic pack.
12. Add generated typed-consumer sketches only after at least one downstream
    user needs them.
13. Current boundary review: promoted solver-reuse rows are now readable through
    the dependency-free query consumer, but that still does not justify a Rust
    crate or separate repository. Revisit again once a non-repo consumer,
    repeated typed access call sites, or reusable encoders make in-repo
    docs/scripts insufficient.

Each increment should be small, validate independently, update
[STATUS.md](../../STATUS.md), and commit with enough context that another agent
can continue without reconstructing the plan from git history.

## Validation

Before committing a resource-plan or pack increment, run the narrowest useful
gate plus the generated-resource gate:

```sh
git diff --check
./scripts/check-links.sh
./scripts/check-foundational-resources.sh
python3 scripts/check-foundational-negative-fixtures.py
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>
```

For plan-only edits with no pack change, the focused pack validator can be
omitted. For generated dashboards, inspect `git diff` afterward and commit the
generated files only when the source metadata changed intentionally.
