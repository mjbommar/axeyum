# Curriculum Resource Execution Plan

## Purpose

This is the forward execution plan for turning the
[formal mathematics curriculum](../curriculum/README.md) into a durable
resource ecosystem. The companion
[Math Curriculum Resource Buildout Plan](MATH-CURRICULUM-BUILDOUT.md) records
the phase contract and landed history; the
[Math Curriculum Implementation Matrix](MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md)
gives the per-node/per-field build matrix; the
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
- 65 atlas rows generated from curriculum, field data, twenty-two R1 bridge
  concepts for finite replay, counterexample proof, bounded theorem shadows,
  analysis/topology boundary vocabulary, linear-algebra computation vocabulary,
  algebra-map vocabulary, and Lean horizons, plus the finite-algebra
  QF_UF/Alethe and exact-rational QF_LRA/Farkas example families.
- 84 non-template math example packs, plus the validating template pack.
- generated coverage, field, proof-gap, learner/proof-upgrade, and
  curriculum-pressure dashboards under [generated/](generated/).
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

- Audit `curriculum_status`, `resource_status`, and proof-route statuses for
  curriculum rows whose packs have already landed.
- Decide which rows should remain `planned` because they are bounded shadows
  of broader theory, even when the first pack validates.
- Add a generated "needs learner page" and "needs proof upgrade" view instead
  of relying on manual scans.
- Add generated R0-R6 "gate" and "next gate" columns so solver-reuse and
  consumer-boundary candidates are visible without manual row audits.
- Add a generated curriculum-pressure-by-fragment view so solver/proof demand
  is grouped by Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, finite replay, and
  Lean horizon without hand-maintained scans.
- Keep all status changes generated from `curriculum.toml`,
  [MATH-CURRICULUM-BUILDOUT.md](MATH-CURRICULUM-BUILDOUT.md), and pack metadata.

Exit criteria:

- `scripts/check-foundational-resources.sh` regenerates identical dashboards on
  a clean checkout.
- Every `planned` curriculum row has a reason: missing pack, bounded-only
  shadow, proof-route gap, or Lean horizon.

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

- finite probability and finite measure as separate first-principles lessons;
- linear optimization as a standalone LP/Farkas bridge;
- finite topology as a standalone topology-axiom/closure/interior bridge;
- bounded dynamics and finite operators as separate dynamics/operator bridges
  if the broad analysis/dynamics lesson becomes too dense.

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
| QF_UF/Alethe | equivalence classes, functions, finite algebra homomorphisms, monoids | equality-heavy finite structure checks |
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

- logic: refutation, proof by cases, finite quantifier expansion, induction
  obligations, induction schemas;
- set theory: equivalence classes, quotients, lattices, finite cardinal
  inequalities;
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
- probability/statistics: finite kernels, conditional expectation,
  martingales, hitting times, concentration, exact tests;
- topology/geometry: finite topologies, continuous maps, simplicial homology,
  affine maps, orientation/area.

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
  query layer for summary counts, pack discovery, checked-row mining,
  solver-reuse candidates, and atlas concept lookup.
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
| `topology` | standalone finite topology lesson and granular compactness/connectedness/homology rows |
| `measure_theory` | standalone finite measure lesson; keep Lebesgue/convergence theorem rows Lean-horizon |
| `probability_theory` | standalone finite probability lesson and stochastic-process path through kernels/Markov chains |
| `statistics` | exact finite tests, regression, concentration, and explicit numerical-honesty status |
| `optimization_and_convexity` | standalone LP/Farkas lesson and convexity/gradient/Hessian bridge rows |
| `numerical_analysis` | residual/error-bound examples with exact rational shadows and numerical limits |
| `differential_equations_and_dynamical_systems` | bounded recurrence/Euler lessons plus invariant-counterexample rows |
| `geometry` | keep combined coordinate/affine/orientation lesson; add incidence/rigidity rows later |
| `functional_analysis_and_operator_theory` | finite operator and Chebyshev-system lessons; keep Banach/Hilbert theorems Lean-horizon |

## Forward Increments From Here

1. Landed: add generated learner-coverage, proof-upgrade gap, and
   curriculum-pressure-by-fragment views.
2. Normalize concept-atlas statuses so `planned` means a real remaining gap.
3. Add focused graph lessons for reachability, search runtime, matching, cuts,
   and d-separation.
4. Add standalone finite probability and finite measure lessons.
5. Add standalone linear optimization and finite topology lessons.
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
9. Landed: add "math example using this route" sections to the six active proof
   cookbook recipes so proof-route docs point back to concrete packs.
10. Add QF_LRA/Farkas upgrade rows for rational, LP, convexity, concentration,
   and linear-system examples.
   Status: `family_exact_rational_farkas` now groups the recurring checked
   exact-rational infeasibility rows and ties them to the shared
   `math_resource_lra_routes` regression.
11. Add QF_UF/Alethe upgrade rows for equivalence, function, and finite algebra
   examples.
   Status: the first high-use learner-page route-note pass now names these
   routes and their trust boundaries; `family_finite_algebra_alethe` now groups
   the recurring checked finite-algebra EUF/Alethe conflicts.
   Dashboard status: generated R0-R6 gate and next-gate columns now make
   R4-to-R5 solver-reuse candidates visible in the coverage, field, proof-gap,
   and learner/proof-upgrade dashboards. The curriculum-pressure view now
   groups the 84 non-template packs into overlapping Bool/CNF, QF_BV, QF_LIA,
   QF_LRA, QF_UF, finite-replay, and Lean-horizon buckets for fragment-level
   planning.
   Candidate status: the first `solver_reuse` batch is now fully promoted:
   `logic-basics-v0`,
   `finite-cardinality-v0`, `graph-matching-v0`, `graph-reachability-v0`,
   `graph-cut-v0`, `graph-d-separation-v0`, and
   `graph-search-runtime-v0`, `integer-lia-v0`, and
   `natural-arithmetic-v0`, plus `number-theory-v0`, have moved from
   candidate to promoted for their source-linked regression artifacts.
12. Landed: add consumer-facing sample queries over the JSON data contract.
   `scripts/query-foundational-resources.py` now supports summary, pack, check,
   and concept queries, and `check-foundational-resources.sh` runs a small
   query smoke set.
13. Promote selected packs into solver regression/fuzz corpora with back-links
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
11. Add a rules/law reasoning resource plan that explicitly reuses finite
    predicates, graph reachability, optimization, and proof-route vocabulary.
12. Add generated typed-consumer sketches only after at least one downstream
    user needs them.
13. Revisit the library boundary decision once consumers or repeated encoders
    make in-repo docs/scripts insufficient.

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
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>
```

For plan-only edits with no pack change, the focused pack validator can be
omitted. For generated dashboards, inspect `git diff` afterward and commit the
generated files only when the source metadata changed intentionally.
