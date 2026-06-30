# Math Curriculum Resource Master Plan

## Purpose

This is the top-down plan for building the full Axeyum foundational-resource
system from the formal math curriculum. It sits above the current execution
ledger and answers the operational question:

```text
given the curriculum DAG, what resources do we build, in what order,
with what validation and graduation criteria?
```

The core invariant is unchanged:

```text
untrusted fast search, trusted small checking
```

Every artifact should either make a bounded/computable claim checkable or mark
the corresponding theorem as a Lean/proof horizon. A finite witness is useful
education and solver pressure; it is not a proof of an unbounded theorem.

## Source Grounding

Build from these sources in this order:

1. [`docs/curriculum/curriculum.toml`](../curriculum/curriculum.toml): the
   authoritative 23-node prerequisite DAG.
2. [`MATH-FIELDS.md`](MATH-FIELDS.md): the 18-field university math taxonomy.
3. Existing validated packs under [`artifacts/examples/math/`](../../artifacts/examples/math/).
4. Generated dashboards under [`generated/`](generated/), especially field
   coverage, proof gaps, curriculum pressure, and solver-reuse disposition.
5. External sanity checks, not local taste:
   [MSC2020](https://mathscinet.ams.org/mathscinet/msc/msc2020.html) for broad
   research-field coverage and [MIT Course 18](https://catalog.mit.edu/subjects/18/)
   for undergraduate/graduate curriculum coverage.

The external sources are not schemas. They are checks that our 18-field taxonomy
does not miss major university or research branches.

## Current Baseline

As of 2026-06-30, the committed resource query reports:

- 23 curriculum-node concept rows.
- 18 math-field concept rows.
- 48 bridge-concept rows.
- 5 example-family rows.
- 102 non-template math packs.
- 516 expected checks.
- 222 checked proof/evidence rows.
- 229 replay-only rows.
- 65 Lean-horizon rows.
- 102 promoted solver-reuse packs.
- 0 unclassified solver-reuse packs.

This means the seed phase is over. The next work is systematic depth:

- make the resources navigable by curriculum layer, field, proof route, and
  solver pressure;
- upgrade representative replay-only rows to checked evidence;
- add missing learner pages and trust-boundary notes;
- add new packs only when they fill a real curriculum/field hole;
- keep JSON schemas and query scripts as the public boundary until multiple
  consumers prove a library split is necessary.

## Resource Shape

Every resource increment should land one coherent unit:

| Layer | Artifact | Required Contents | Required Check |
|---|---|---|---|
| R0 | curriculum or field anchor | node/field, prerequisites, decidability, horizon | local link to curriculum or field row |
| R1 | concept row | fragments, proof routes, example packs, open gaps | `python3 scripts/validate-foundational-concepts.py` |
| R2 | example pack | metadata, model, checks, expected rows, validator | `python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>` |
| R3 | learner page | finite slice, model/proof story, limitation, run command | `./scripts/check-links.sh` |
| R4 | proof route | replay, DRAT/LRAT, Farkas, Diophantine, Alethe, BV proof, or Lean horizon | route-specific cargo regression |
| R5 | solver reuse | source artifact, solver pressure, regression/fuzz/corpus link | `python3 scripts/query-foundational-resources.py summary` shows no unclassified drift |
| R6 | consumer boundary | schema, query, generated dashboard, or typed accessor | `python3 scripts/consume-foundational-resources.py` |

Do not skip the trust story. For each SAT row, say what is replayed. For each
UNSAT row, say what certificate route is checked or why the row remains a gap.
For each `not-run` row, say what proof horizon blocks graduation.

## Build Waves

### Wave A: Preserve The Contract

Goal: make the current 102 packs a stable, queryable data product.

Work:

- Keep all packs classified as `promoted`, `non-benchmark-horizon`, or explicitly
  unclassified with a reason.
- Keep generated dashboards reproducible from metadata and generators.
- Add field-readiness smoke queries when a field gains a meaningful route.
- Keep link, schema, and query checks as mandatory plan/edit gates.

Exit:

- `./scripts/check-foundational-resources.sh` passes.
- `python3 scripts/query-foundational-resources.py summary` has zero
  unclassified solver-reuse rows.
- A consumer can answer "what do we have for field X plus proof route Y?"
  without reading prose.

### Wave B: Complete The Learner Spine

Goal: every curriculum node and every substantial field has at least one
learner path that explains what Axeyum checks.

Work:

- Keep cluster pages for broad navigation.
- Add focused end-to-end pages when a pack has a complete model/proof loop.
- Add route notes to high-use cluster pages so proof objects are not hidden in
  metadata.
- Audit each page for bounded-vs-theorem overclaiming.

Exit:

- Every non-template pack appears in a focused page or a named combined page.
- Every learner page has a validation command.
- The generated learner/proof-upgrade dashboard has no accidental path-only
  omissions.

### Wave C: Upgrade Proof Evidence

Goal: make representative UNSAT rows independently checked.

Work by route:

- Bool/CNF: promote small graph, counting, topology, and proof-method
  refutations through DRAT/LRAT.
- QF_BV: promote fixed-width residue and finite-algebra conflicts only when
  bit width is part of the concept.
- QF_LIA/Diophantine: promote gcd, divisibility, count, homology, and finite
  statistical obstruction rows.
- QF_LRA/Farkas: promote exact rational rows from matrices, LP/optimization,
  probability tables, measure tables, geometry, numerical steps, and dynamics.
- QF_UF/Alethe: promote equality-heavy finite function, quotient, algebra,
  module, ideal, tensor, and action rows.
- Lean horizon: record theorem shape, prerequisites, and missing reconstruction
  dependency for induction, completeness, compactness, measure convergence,
  asymptotics, and infinite-dimensional analysis.

Exit:

- Each active certificate route has at least one learner page showing successful
  checking and tamper rejection.
- The proof frontier is a route-specific work queue, not a generic wish list.

### Wave D: Add Missing Curriculum Depth

Goal: add new resources only where the field/curriculum map shows a genuine
hole or a useful new proof/solver pattern.

Selection rule:

```text
new pack = distinct mathematical object + distinct replay/proof route
           + clear curriculum/field anchor + validation command
```

Prefer an upgrade to an existing pack when the proposed work is only another
instance of the same object and proof route.

Exit:

- New packs increase field coverage, proof-route coverage, or solver pressure.
- Existing dashboards expose the new pack without special prose.

### Wave E: Consumer And Library Boundaries

Goal: make the resources reusable outside the docs without prematurely splitting
the project.

Work:

- Keep JSON schemas, generated JSON, generated Markdown, and query scripts as
  the public contract.
- Add typed accessors only after scripts duplicate parsing logic in multiple
  places.
- Split a crate or separate repo only after at least three real consumers or one
  external release-cadence need.
- Keep rules/law resources as downstream reuse of the same patterns: finite
  predicates, thresholds, graph reachability, precedence, arithmetic
  constraints, and checked proof routes.

Exit:

- A downstream project can consume concept rows and example-pack metadata without
  depending on private scripts.
- Boundary decisions cite real repeated usage.

## Curriculum-Layer Plan

### Layer 0: Foundations

Nodes: `propositional-logic`, `predicate-logic`, `proof-methods`, `induction`,
`sets`, `relations-and-functions`, `cardinality`.

Build plan:

- Keep Boolean SAT, CNF, finite predicate, finite set, finite function, finite
  lattice, finite quotient, and finite cardinality packs as the first proof
  story.
- Upgrade small false finite claims through Bool/CNF or QF_UF/Alethe when the
  source object is fixed and learner-readable.
- Add or maintain bridge rows for refutation, finite countermodel replay,
  finite quantifier expansion, bounded induction obligations, quotient maps,
  image/preimage, inverse tables, and finite/infinite cardinality boundaries.
- Keep full first-order validity, full induction, choice, ordinal/cardinal
  arithmetic, and infinite cardinality as Lean-horizon.

Next useful increments:

- a compact finite proof-pattern proof-object walkthrough;
- a richer finite countermodel query page for predicate logic;
- one checked false lattice/set-family row if it adds a distinct proof route.

### Layer 1: Number Systems

Nodes: `naturals`, `integers`, `rationals`, `reals`, `complex`.

Build plan:

- Keep natural and integer arithmetic split between bounded replay, QF_LIA, and
  fixed-width QF_BV.
- Keep rationals as exact QF_LRA/Farkas examples; never use floating-point
  language for exact rational rows.
- Keep reals split into algebraic shadows, bounded rational analysis, finite
  optimization/numerical steps, and theorem horizons for completeness and
  convergence.
- Keep complex numbers as real-pair algebra until analytic proof support
  exists.

Next useful increments:

- exact-vs-floating arithmetic notes for learners and consumers;
- additional algebraic-real/RCF shadows only when they create reusable NRA/RCF
  pressure;
- complex-polynomial root and Mobius-transform rows only when distinct from the
  existing real-pair transform pack.

### Layer 2: Core Structures And Tools

Nodes: `divisibility-and-euclid`, `modular-arithmetic`, `groups`, `rings`,
`fields`, `polynomials`, `sequences-and-limits`, `counting`.

Build plan:

- Treat divisibility and modular arithmetic as arithmetic-certificate pressure.
- Treat finite algebra as table replay plus equality/certificate pressure:
  homomorphisms, kernels/images, quotients, ideals, modules, tensors, monoids,
  permutations, and actions.
- Treat polynomials as coefficient arithmetic, factorization replay, generating
  functions, root-finding shadows, and finite polynomial geometry.
- Treat sequences and counting as finite-prefix evidence plus explicit
  asymptotic/convergence horizons.

Next useful increments:

- orbit-stabilizer and Burnside refinements only if they serve multiple packs;
- polynomial-resultant/discriminant rows if they produce real NRA/RCF pressure;
- recurrence/asymptotic bridge rows tied to graph-search and generating-function
  examples.

### Layer 3: Destinations

Nodes: `number-theory`, `linear-algebra`, `calculus`.

Build plan:

- Number theory: bounded residue, CRT, quadratic residue, sum-of-squares, and
  Diophantine rows with precise proof-route labels.
- Linear algebra: matrix computation families that are both educational and
  solver-useful: LU, rank/nullity, residual bounds, eigenpairs, characteristic
  polynomials, finite-field linear algebra, tensor maps, projections, and
  random-matrix moments.
- Calculus: exact algebraic derivatives, finite Riemann sums, Jacobian/Hessian
  replay, root-finding, finite optimization steps, line-search/projection/prox
  rows, and explicit theorem horizons for FTC, differentiability, and
  convergence.

Next useful increments:

- landed matrix-corpus note that separates education examples, solver
  regressions, benchmark-corpus rows, and theorem-horizon claims;
- landed calculus theorem-horizon map from finite shadows to Lean reconstruction;
- finite algorithm-step variants only when they add solver pressure, not just
  another numeric example.

## Field-By-Field Plan

| Field | Current Surface | Build Next | Proof / Solver Route | Graduation |
|---|---|---|---|---|
| `logic_and_proof` | SAT, finite predicates, refutation, proof patterns, induction bounds | proof-object walkthroughs, finite countermodel patterns, bounded induction warnings | Bool/CNF DRAT/LRAT, QF_LIA, QF_UF, Lean horizon | corrupted proof/certificate rejection appears in learner material |
| `set_theory_and_foundations` | finite sets, functions, quotients, lattices, cardinality, topology/measure finite sets | stronger finite/infinite boundary rows and reusable quotient/image/preimage vocabulary | finite replay, Bool/CNF, QF_UF/Alethe, Lean horizon | infinite claims are never benchmarked as finite checks |
| `discrete_math` | counting, generating functions, graph resources, finite actions | double-counting, recurrence/asymptotic boundary, reusable finite enumeration rows | Bool/CNF, QF_LIA, finite replay | each row names universe size and theorem horizon |
| `graph_theory` | coloring, reachability, search runtime, matching, cuts, d-separation | one representative proof regression per graph family; pathologies with explicit cost counters | Bool/CNF, QF_BV, QF_LIA, finite replay | graph resources query by route and source artifact |
| `number_theory` | gcd, modular arithmetic, residues, finite fields, bounded Diophantine rows | recurring divisibility/CRT/residue obstructions and fixed-width contrasts | QF_LIA/Diophantine, QF_BV | bounded search and theorem claims are visibly separated |
| `linear_algebra` | rational matrices, finite vector/dual/module/tensor, spectral, invariant, optimization/numerical rows | matrix-computation index plus matrix-corpus boundary by LU/rank/nullity/projection/residual/eigen/characteristic/random-moment | QF_LRA/Farkas, finite replay, QF_UF/Alethe | solver regressions cite source pack and pack cites regression before benchmark claims |
| `abstract_algebra` | finite groups, rings, fields, monoids, actions, homomorphisms, ideals, modules, tensors | narrower rows only for reused concepts: orbit/stabilizer, Burnside, units/idempotents, representation horizons | QF_UF/Alethe, QF_BV, finite replay, Lean horizon | table replay remains distinct from structure-theorem proof |
| `real_analysis` | rational intervals, metric continuity, sequences, compactness/connectedness, root-finding, optimization shadows | bounded-vs-theorem bridge rows, theorem-horizon map for completeness and convergence | QF_LRA/Farkas, QF_NRA/RCF shadows, Lean horizon | every lesson states finite/bounded shadow vs theorem |
| `complex_analysis` | real-pair algebra and transforms | polynomial-root, conjugation/norm, Mobius rows only if distinct; analytic horizon rows | real-pair LRA/NRA, finite replay, Lean horizon | no algebraic row is described as analytic coverage |
| `topology` | finite topologies, compactness, connectedness, continuous maps, homology | closure/interior, homeomorphism, chain-complex, homology-rank refinements | Bool/CNF, QF_UF/Alethe, QF_LIA, finite replay, Lean horizon | dashboards distinguish finite set-family replay from topology theorems |
| `measure_theory` | finite measure, monotonicity, product measure, integration, random variables, conditioning, martingales | only distinct table/convergence vocabulary; keep countable/Lebesgue material horizon | QF_LRA/Farkas, finite replay, Lean horizon | finite universe and sigma-algebra are explicit |
| `probability_theory` | finite PMFs, kernels, Markov chains, martingales, hitting times, concentration | exact discrete distributions, independence/conditioning variants, limit-theorem horizons | QF_LRA/Farkas, QF_LIA, finite replay | probability rows can be audited as exact rational tables |
| `statistics` | descriptive stats, exact tests, regression, finite count tables | exact finite inference examples and numerical-honesty metadata | QF_LIA, QF_LRA/Farkas, replay | inference claims distinguish exact finite tests from statistical modeling |
| `optimization_and_convexity` | LP, convexity, least squares, root finding, KKT, active-set QP, SDP, gradient/line-search/projected/proximal rows | duality, degenerate active sets, working-set pivots, strong-Wolfe, box-plus-L1, stochastic/convergence horizons | QF_LRA/Farkas, QF_NRA, Lean horizon | finite KKT/duality/algorithm rows do not claim general sufficiency/convergence |
| `numerical_analysis` | residuals, Euler steps, root-finding, finite optimization iterations, operator bounds | error recurrences, interval boxes, pivoting/stability notes, reproducible numerical metadata | QF_LRA/Farkas, replay, Lean horizon | exact replay is separate from floating-point experiment claims |
| `differential_equations_and_dynamical_systems` | bounded recurrences, Euler traces, finite invariants, stochastic kernels/hitting times | transition/invariant/reachability variants and finite-error pressure | QF_LRA/Farkas, finite replay, Lean horizon | continuous existence/uniqueness and PDE claims stay horizon |
| `geometry` | coordinate, incidence, rigid, affine, oriented area, circle, inversion, cyclic quadrilaterals | circle-line correspondence, angle rows beyond the square witness, Ptolemy shadows, higher-degree polynomial geometry | QF_LRA/Farkas, finite replay, QF_NRA horizon | synthetic/global geometry claims stay Lean horizon |
| `functional_analysis_and_operator_theory` | finite operators, inner products, projections, Chebyshev slices, finite duals | norm variants, finite approximation/interpolation, operator-spectrum rows | QF_LRA/Farkas, finite replay, Lean horizon | Banach/Hilbert and infinite-dimensional claims are not finite checks |

## Near-Term Commit Queue

Use one row per commit unless the change is purely navigational.

1. Add this master plan and link it from the planning index files.
2. Audit the generated learner/proof dashboard for packs whose focused lesson is
   stale after recent geometry and optimization additions.
3. Landed: add the next distinct geometry resource,
   `finite-cyclic-geometry-v0`, as cyclic/angle pressure rather than another
   coordinate-distance variant.
4. Landed: add a matrix-computation index page that groups LU, rank/nullity,
   residual, eigenpair, characteristic-polynomial, random-matrix, projection,
   chain-complex, operator, and tensor/module rows by proof route.
5. Landed: add
   [`analysis-calculus-theorem-horizon-map.md`](../learn/math/analysis-calculus-theorem-horizon-map.md),
   mapping completeness, IVT/MVT/FTC, compactness, sequence convergence,
   recurrence/asymptotics, root-finding convergence, optimization convergence,
   measure/probability convergence, functional analysis, and dynamics from
   finite shadows to missing Lean/theorem reconstruction routes.
6. Landed: add
   [`matrix-corpus-benchmark-boundary.md`](../learn/math/matrix-corpus-benchmark-boundary.md),
   separating educational matrix rows, solver regressions, benchmark-corpus
   rows, and theorem-horizon claims before any performance or parity language.
7. Promote one replay-heavy family per route only when a compact source artifact
   exists and a route-specific regression can check it.
8. Landed: add the
   [`tax-benefit-arithmetic-v0`](../rules-as-code/examples/tax-benefit-arithmetic-v0/)
   rules/law pack by reusing integer threshold, cap, phase-out monotonicity,
   effective-date, finite replay, and Bool/QF_LIA proof-route patterns.
9. Landed: add the generated
   [`rules-query-dashboard.md`](../rules-as-code/generated/rules-query-dashboard.md)
   so the three rule packs expose bounded sample rows and generated-query
   families before new law-specific schema fields are created.
10. Landed: add functional-analysis/operator consumer-query coverage through
   [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
   `scripts/check-foundational-resources.sh`, making finite operator bounds,
   inner-product positivity, Chebyshev grids, spectral/eigenpair witnesses, and
   operator bridge rows visible through the public JSON contract.
11. Add future rules/law crosswalk examples only by reusing existing
   math-resource patterns; do not create a separate rule ontology until the
   current JSON boundary is exercised by more consumers.

## Anti-Patterns

- Do not add a bare concept row with no example, validator, or horizon
  dependency.
- Do not create a new pack for a duplicate instance of an already-covered proof
  route unless it adds a field hole or solver pressure.
- Do not call a finite bounded check "the theorem."
- Do not promote source artifacts into benchmarks until replay is deterministic
  and the pack links the regression.
- Do not split a crate or repo because the documentation tree is large.

## Required Validation

For this plan or navigation-only edits:

```sh
git diff --check
./scripts/check-links.sh
```

For any generated-resource, pack, metadata, or solver-reuse edit:

```sh
./scripts/check-foundational-resources.sh
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary
```

For a proof-route promotion, also run the route-specific cargo regression named
in the pack metadata and proof-upgrade frontier.
