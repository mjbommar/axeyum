# Math Curriculum Detailed Resource Build Plan

## Purpose

This is the execution ledger for building the full math-resource ecosystem from
the curriculum spine. It sits below the broad roadmap and above individual
pack edits:

```text
curriculum node -> concept row -> example pack -> learner page
-> proof route -> solver reuse -> consumer boundary
```

Use this file when choosing the next commit-sized work item. Use
[MATH-CURRICULUM-BUILDOUT.md](MATH-CURRICULUM-BUILDOUT.md) for phase history,
[MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md](MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md)
for the owner-facing plan across all curriculum-based resource families,
[MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md](MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md)
for the top-down curriculum-wide buildout plan,
[MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md](MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md)
for the practical staged build sequence across education, ontology, examples,
proofs, solver feedback, rules/law transfer, and consumer boundaries,
[MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md](MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md)
for per-node gates, [RESOURCE-BUILDOUT-ROADMAP.md](RESOURCE-BUILDOUT-ROADMAP.md)
for the broader resource-family plan, and
[PROOF-UPGRADE-FRONTIER.md](PROOF-UPGRADE-FRONTIER.md) for route-specific proof
upgrades. Use
[PROOF-ROUTE-FAMILY-SELECTION.md](PROOF-ROUTE-FAMILY-SELECTION.md) to choose the
representative replay-heavy family per active proof route before adding another
compact checked row.

The invariant stays simple:

```text
untrusted fast search, trusted small checking
```

Every resource should make one bounded/computable claim checkable, or clearly
state the Lean/theorem horizon when a bounded check is not a theorem.

## Current Baseline

The committed resource query currently reports:

- 23 curriculum-node concept rows.
- 18 field rows.
- 74 bridge-concept rows.
- 5 example-family rows.
- 108 non-template math packs.
- 660 expected checks.
- 322 checked proof/evidence rows.
- 267 replay-only rows.
- 71 Lean-horizon rows.
- 108 promoted solver-reuse packs.
- 0 non-benchmark-horizon solver-reuse packs.
- 0 unclassified solver-reuse packs.
- 108 focused learner-linked packs, with no path-only, index-only, or missing
  learner buckets; see [Learner Coverage Audit](LEARNER-COVERAGE-AUDIT.md).

The next phase is therefore a depth phase, not a seed phase. New packs are
allowed only when they fill a clear curriculum/field hole that cannot be served
by upgrading an existing pack.

## Resource Unit Contract

Every new or upgraded resource must answer these questions before it lands:

| Question | Required Answer |
|---|---|
| Audience | learner, educator, proof contributor, solver contributor, consumer, or several |
| Curriculum anchor | one `curriculum.toml` node or one field extension from `MATH-FIELDS.md` |
| Mathematical claim | finite claim, bounded shadow, computable witness, numerical check, or theorem horizon |
| Encoding route | Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, QF_NRA/RCF, finite replay, or Lean horizon |
| Evidence route | model replay, DRAT/LRAT, Farkas, Diophantine, Alethe, QF_BV DRAT, or explicit gap |
| Trust boundary | what is generated/searched versus what is independently replayed or checked |
| Graduation | exact command, regression, proof route, or horizon dependency needed for the next gate |

Do not land a resource that only says a topic name. A useful row has either a
validated example, a planned example with a validation rule, or a named
theorem-horizon dependency.

## Gate Model

| Gate | Meaning | Required Check |
|---|---|---|
| R0 source | curriculum node or field taxonomy row exists | local link to `curriculum.toml` or `MATH-FIELDS.md` |
| R1 concept | atlas row exists with fragments, proof routes, and gaps | `python3 scripts/validate-foundational-concepts.py` |
| R2 pack | pack files validate and expected rows are machine-readable | `python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>` |
| R3 learner | a learner page exposes the check and limitation | `./scripts/check-links.sh` |
| R4 evidence | checked replay/certificate or explicit Lean horizon | route-specific cargo test plus pack validator |
| R5 solver reuse | regression, fuzz seed, corpus slice, or non-benchmark horizon is linked | query helper shows non-unclassified `solver_reuse` |
| R6 consumer | JSON/query consumer is enough, or a boundary decision proves more | `python3 scripts/consume-foundational-resources.py` |

No row should be described beyond its gate. A bounded finite example can be a
good R2/R3 lesson while still not being a theorem.

## Build Waves

### Wave 1: Stabilize The Current 108 Packs

Goal: every current non-template pack has a deliberate R5 disposition:
`promoted`, `non-benchmark-horizon`, or a clear reason to remain unclassified.

Current unclassified queue: empty.

Current non-benchmark queue: empty.

Last row closed:

| Pack | Upgrade Trigger |
|---|---|
| bounded-family/asymptotic bridge | generated `bridge_bounded_family_asymptotic_boundary`, making finite graph-runtime, recurrence-prefix, coefficient-window, bounded-dynamics, and Euler-step rows queryable while preserving asymptotic and convergence claims as Lean horizons |

Exit criteria:

- `python3 scripts/query-foundational-resources.py summary` shows no accidental
  candidate drift.
- Every still-unclassified pack has a short reason in the proof frontier or this
  file's next revision.
- `PROOF-UPGRADE-FRONTIER.md` names the first checked route for every promoted
  pack family.

### Wave 2: Complete The Curriculum-Layer Learner Spine

Goal: each curriculum node has a learner-facing path that separates checkable
slices from theorem horizons.

| Layer | Curriculum Nodes | Learner Work |
|---|---|---|
| Foundations | propositional logic, predicate logic, proof methods, induction, sets, relations/functions, cardinality | proof object anatomy, finite countermodels, quotient/partition replay, bounded induction warnings |
| Number systems | naturals, integers, rationals, reals, complex | exact arithmetic versus real completeness, real-pair complex algebra, total operation conventions |
| Core structures | divisibility, modular arithmetic, groups, rings, fields, polynomials, sequences/limits, counting | table replay, quotient maps, coefficient arithmetic, bounded sequence shadows, pigeonhole/counting proofs |
| Destinations | number theory, linear algebra, calculus | arithmetic certificates, matrix corpora, exact calculus shadows, FTC/convergence horizons |

Exit criteria:

- Every pack appears in a focused lesson or an explicitly named combined
  lesson.
- Every lesson has a run/check command or a link to pack validation.
- No lesson implies a finite bounded check proves an unbounded theorem.

Current audit: [Learner Coverage Audit](LEARNER-COVERAGE-AUDIT.md) records that
all 108 current non-template packs satisfy the focused-lesson side of this
gate. Keep this true as new packs land.

### Wave 3: Proof-Route Depth

Goal: make checked evidence normal for representative UNSAT rows.

Selection aid: [Proof Route Family Selection](PROOF-ROUTE-FAMILY-SELECTION.md)
records the current representative family for Boolean CNF/LRAT, QF_BV,
QF_LIA/Diophantine, QF_LRA/Farkas, QF_UF/Alethe, and Lean-horizon resources,
and states when another compact negative row is worth promoting.
[Proof Route Learner Snippets](../learn/math/proof-route-learner-snippets.md)
gives the reusable learner-facing trust-boundary wording for those checked
routes.

| Route | Curriculum Pressure | Build Pattern | Stop Condition |
|---|---|---|---|
| Bool/CNF DRAT/LRAT | logic, sets, graphs, counting, finite topology | commit small DIMACS artifact, emit DRAT, elaborate/check LRAT, add tamper regression | one representative row per source family is promoted |
| QF_BV DRAT | finite fields/rings, residue arithmetic, bit encodings | add fixed-width SMT-LIB artifact and DRAT-backed bit-blast regression | width is educationally meaningful, not incidental |
| QF_LIA/Diophantine | integer equations, gcd, counts, homology coefficients | encode minimal obstruction and check integer certificate | recurring obstruction has a cookbook example |
| QF_LRA/Farkas | rationals, matrices, LP, probability tables, geometry, circle/inversion/cyclic geometry, dynamics, root finding, separation, KKT, active-set QP, SDP, gradient descent | express exact rational conflict, emit/recheck Farkas certificate | source pack links artifact and learner page names trust boundary |
| QF_UF/Alethe | finite functions, quotients, algebra maps, actions, modules | encode congruence/equality conflict and check Alethe | table replay and equality proof are distinct in docs |
| Lean horizon | induction, completeness, compactness, measure, asymptotics, Hilbert/Banach facts | state theorem shape, prerequisites, and missing reconstruction dependency | finite rows are not counted as theorem proof |

Exit criteria:

- `PROOF-UPGRADE-FRONTIER.md` can be read as a work queue, not as a stale wish
  list.
- Each active route has at least one end-to-end learner page that shows a
  successful certificate and a rejected tampered certificate.

### Wave 4: Solver Feedback And Benchmark Hygiene

Goal: educational examples become useful solver assets without distorting the
education layer into a benchmark suite.

Build rules:

- Promote a row only after its mathematical source object is stable and replayed.
- Keep source-level artifacts under the pack folder.
- Name the solver pressure in `solver_reuse`: clause learning, BV lowering,
  integer obstruction, Farkas certificate, EUF congruence, array extensionality,
  finite expansion, or Lean reconstruction.
- Keep general theorem horizons out of performance scoring.
- Use example-family rows for recurring proof/solver shapes rather than
  repeating prose across packs.

Exit criteria:

- A solver contributor can query by field plus route and find source-linked
  artifacts.
- Regression tests cite the pack, and the pack cites the regression.
- No resource-backed benchmark claim exists without a committed corpus and
  measured result.

### Wave 5: Consumer, Rules/Law, And Library Boundaries

Goal: make the resource system useful outside docs while keeping the boundary
boring until real demand exists.

Build order:

1. Keep JSON schemas, validators, generated dashboards, and query helper as the
   public contract.
2. Add rules/law examples only when they reuse existing math-resource patterns:
   finite predicates, thresholds, reachability, precedence, optimization, and
   proof routes. Status: `benefit-eligibility-v0` and
   `authorization-policy-v0` now exercise the eligibility and access-control
   slices with replayed witnesses plus checked Bool/QF_LIA proof fixtures, and
   `tax-benefit-arithmetic-v0` now exercises the threshold/cap/phase-out slice
   with replayed witnesses plus checked Bool/QF_LIA proof fixtures.
3. Add typed accessors only after repeated scripts duplicate parsing logic.
4. Split a crate or separate repo only after a boundary decision cites at least
   three duplicated consumers or one external release-cadence need.

Exit criteria:

- `scripts/consume-foundational-resources.py` and
  `scripts/query-foundational-resources.py` cover the common consumer questions,
  including field-level curriculum readiness.
- A boundary decision can point at real usage, not project size alone.

## Field Build Ledger

| Field | Current Role | Next Resource Work | Evidence Route |
|---|---|---|---|
| `logic_and_proof` | SAT, refutation, finite proof patterns, induction bounds | maintain proof-object anatomy bridge rows and PHP CNF promotions | Bool/CNF DRAT/LRAT, QF_LIA, Lean horizon |
| `set_theory_and_foundations` | finite sets, relations, functions, quotients, lattices, cardinality | maintain landed finite Boolean algebra, partition/relation, image/preimage/inverse, finite cardinality, and cardinality-horizon bridge rows | finite replay, Bool/CNF, QF_UF/Alethe, Lean horizon |
| `discrete_math` | counting, generating functions, graph resources, finite actions | maintain landed finite-counting replay and bounded-family/asymptotic-boundary bridges; add new rows only for distinct counting, recurrence, or family-boundary pressure | Bool/CNF, QF_LIA, QF_LRA/Farkas, finite replay |
| `graph_theory` | coloring, reachability, search runtime, matching, cuts, d-separation | maintain landed finite graph replay/obstruction and bounded-family/asymptotic-boundary bridges; add theorem/asymptotic horizons only as proof targets | Bool/CNF, QF_BV, QF_LIA, finite replay |
| `number_theory` | gcd, modular arithmetic, residues, bounded Diophantine checks | group recurring divisibility and residue obstructions; modular Fermat-unit search now has a fixed-width QF_BV/DRAT row | QF_LIA/Diophantine, QF_BV |
| `linear_algebra` | exact matrices, vector spaces, duals, modules, tensors, spectral rows, active-set QP rows, SDP rows, descent-step rows, line-search rows, Wolfe line-search rows, projected-gradient rows, proximal-gradient rows | maintain matrix rows queryable by computation type and solver route; five matrix/statistics bad rows now prove committed SMT-LIB artifacts directly through QF_LRA/Farkas regressions | QF_LRA/Farkas, finite replay, QF_UF/Alethe |
| `abstract_algebra` | finite groups/rings/fields, homomorphisms, ideals, modules, tensors | add narrower rows only when multiple packs reuse them | QF_UF/Alethe, QF_BV, finite replay |
| `real_analysis` | bounded rational intervals, metric continuity, RCF shadows, calculus shadows, root-finding shadows, separation/KKT/active-set/SDP/gradient-descent/line-search/Wolfe/projected-gradient/proximal-gradient shadows | keep bounded shadows distinct from completeness/convergence/separation/KKT/active-set/SDP/descent/line-search/Wolfe/projected/proximal-gradient theorems; metric continuity now has source-linked bad-delta and bad open-ball preimage rows, finite KKT now has source-linked bad stationarity and bad complementarity rows, finite SDP now has source-linked bad objective, bad duality-gap, and bad slack-entry rows, finite gradient descent now has source-linked bad decrease, bad step-coordinate, and bad descent-bound rows, finite line search has source-linked bad Armijo, bad descent-direction, and bad accepted-candidate rows, finite Wolfe line search has source-linked bad minimizer, bad sufficient-decrease, and bad curvature rows, and finite proximal gradient has source-linked bad proximal-point, bad composite-decrease, and bad box-proximal-point rows | QF_LRA/Farkas, QF_NRA/RCF, Lean horizon |
| `complex_analysis` | real-pair algebra and transformations | complex algebra now has checked bad product-coordinate and bad norm-squared rows; add only distinct real-pair arithmetic, polynomial-root, or algebraic-identity pressure | real-pair LRA/NRA, finite replay, Lean horizon |
| `topology` | finite topologies, quotient topologies, compactness, connectedness, continuous maps, specialization orders, homology, torsion homology, cohomology, cup products | maintain landed topology-shadow, finite topology-operator/homeomorphism with checked continuous-map preimage membership, finite quotient-topology with checked representative/open conflicts, finite specialization-order, finite boundary-operator, finite chain-complex/homology, finite torsion-homology, finite cohomology, and finite cup-product bridge rows; add only distinct cohomology-ring quotienting or theorem-invariance pressure | Bool/CNF, QF_UF/Alethe, QF_LIA, QF_BV, Lean horizon |
| `measure_theory` | finite measures, monotonicity/subadditivity, product measure, integration, random variables | finite measure/additivity, monotonicity/subadditivity, and finite product/integration bridge rows landed; monotonicity now checks both subset and union-subadditivity conflicts, and product-measure checks both product atom and marginal conflicts; promote only distinct convergence-horizon, countable-measure, or new measure-table pressure next | QF_LRA/Farkas, finite replay, Lean horizon |
| `probability_theory` | finite probability, kernels, Markov chains, martingales, hitting times, concentration | standalone finite probability mass-table lesson landed; keep table rows exact and route bad rows through LRA/LIA | QF_LRA/Farkas, QF_LIA, finite replay |
| `statistics` | descriptive stats, exact tests, regression, finite count tables | distinguish exact finite tests from numerical/statistical inference | QF_LIA, QF_LRA/Farkas, replay |
| `optimization_and_convexity` | LP/Farkas, convexity, least squares, Hessians, root-finding steps, separation rows, KKT rows, active-set QP rows, SDP rows, gradient-descent rows, line-search rows, Wolfe line-search rows, projected-gradient rows, proximal-gradient rows | LP objective/Farkas, rational convexity/gradient bridge rows with checked bad midpoint and affine-threshold evidence, finite root-finding step and bisection-width replay, finite hyperplane-separation replay, finite KKT replay with checked bad stationarity and complementarity evidence, finite active-set QP face/slack replay with checked bad free-gradient, bad inactive-slack, and bad degenerate-multiplier rows, finite degenerate active-bound replay, finite SDP primal/dual replay with checked bad objective, bad duality-gap, and bad slack-entry rows, finite gradient-descent replay with checked bad decrease, bad step-coordinate, and bad descent-bound rows, finite Armijo line-search replay with checked bad Armijo, bad descent-direction, and bad accepted-candidate rows, finite Wolfe line-search replay with checked bad minimizer, bad sufficient-decrease, and bad curvature rows, finite projected-gradient interval/decrease replay with checked bad projection and bad projected-decrease rows, finite proximal soft-threshold/composite-decrease replay, and finite box-plus-L1 proximal replay landed with checked bad proximal-point, bad composite-decrease, and bad box-proximal-point rows; add only distinct duality, working-set pivots, higher-dimensional SDP, strong-Wolfe/nonconvex line-search, group-lasso, active-set proximal, or stochastic/convergence pressure next | QF_LRA/Farkas, QF_NRA shadows |
| `numerical_analysis` | residuals, Euler steps, exact error recurrences, matrix algorithms, root-finding, active-set QP, gradient-descent, Armijo/Wolfe line-search, projected-gradient, and proximal-gradient iterations | maintain landed finite dynamics/Euler bridge and keep numerical-honesty rows distinct from promoted exact residual/error certificates; bounded dynamics now checks false transition-step, threshold-step, and invariant-bound arithmetic, finite line-search and finite Wolfe now check descent-direction, accepted-candidate, exact-minimizer, sufficient-decrease, and curvature arithmetic conflicts, and finite proximal-gradient now checks false composite-decrease arithmetic | QF_LRA/Farkas, replay, Lean horizon |
| `differential_equations_and_dynamical_systems` | bounded recurrences and Euler traces | maintain landed finite dynamics/Euler and bounded-family/asymptotic-boundary bridges; bounded dynamics now has checked bad transition-step, bad threshold-step, and bad invariant-bound rows; add only distinct transition, reachability, invariant, stochastic, finite-error, or theorem-boundary pressure | QF_LRA/Farkas, replay, Lean horizon |
| `geometry` | coordinate, incidence, rigid-configuration, affine, orientation/area, circle, inversion, and cyclic rational geometry | maintain landed coordinate/oriented replay and finite circle/inversion/cyclic replay bridge rows; add only distinct nontrivial affine-coordinate, circle-line correspondence, higher-degree polynomial-geometry, or theorem-reconstruction pressure beyond the current midpoint-coordinate, affine collinearity-determinant, area-scaling, circle-line, square angle-dot, and Ptolemy rows | QF_LRA/Farkas, finite replay |
| `functional_analysis_and_operator_theory` | finite operators, inner products, Chebyshev systems | finite-operator now has checked bad `l1` norm, bad operator-bound, and bad Chebyshev-prefix rows, inner-product now has checked bad negative-norm and projection-orthogonality rows, and finite-Chebyshev now has checked duplicate-node, bad-interpolation, and bad-alternation rows; add only distinct norm, projection, recurrence, alternation variants, or finite-dimensional operator pressure | QF_LRA/Farkas, replay, Lean horizon |

## Curriculum Node Build Ledger

| Node | Build Priority | Practical Work |
|---|---|---|
| `propositional-logic` | maintain | keep tiny CNF and tamper tests as the smallest trust story |
| `predicate-logic` | maintain | finite expansion now has a Bool/CNF proof-route regression; keep arbitrary-domain validity horizon explicit |
| `proof-methods` | promote | PHP/refutation CNF artifact and proof-object lesson |
| `induction` | deepen | bounded step-count row now has a source-linked QF_LIA arithmetic-DPLL regression; keep the universal schema Lean-horizon |
| `sets` | maintain | keep finite set/lattice false claims checked and linked |
| `relations-and-functions` | maintain | add image/preimage rows only when reused by several packs |
| `cardinality` | deepen | cardinality-principles overlap-additivity now has source-linked QF_LIA/Diophantine evidence; keep infinite cardinality Lean-horizon |
| `naturals` | maintain | keep bounded prefix and LIA/BV width limits explicit |
| `integers` | maintain | group common Diophantine obstructions |
| `rationals` | maintain | exact rational order and Farkas conflicts are already the model |
| `reals` | deepen | RCF shadow now has a source-linked QF_LRA/Farkas negative-discriminant row, root-finding has source-linked bad-iterate and bad bisection-width rows, separation has source-linked bad convex-combination and bad-separator rows, KKT has source-linked bad-stationarity and bad-complementarity rows, active-set QP has source-linked bad-free-gradient, bad inactive-slack, and bad degenerate-multiplier rows, SDP has source-linked bad-objective and bad duality-gap rows, gradient descent has source-linked bad-decrease, bad step-coordinate, and bad descent-bound rows, finite line search has source-linked bad Armijo, bad descent-direction, and bad accepted-candidate rows, finite Wolfe line search has source-linked bad minimizer, bad sufficient-decrease, and bad curvature rows, finite projected-gradient has source-linked bad-projection and bad projected-decrease rows, finite proximal-gradient has source-linked bad-proximal-point, bad composite-decrease, and bad box-proximal-point rows, finite circle geometry has source-linked bad-radius and bad line-intersection rows, finite inversion geometry has source-linked bad inverse-coordinate and inverse-distance-product rows, and finite cyclic geometry has source-linked bad diagonal-intersection, bad opposite-angle, and bad Ptolemy rows; keep completeness, convergence, separation, KKT sufficiency, active-set method theory, SDP duality, descent-rate, general circle/inversion/cyclic geometry, and broad CAD/SOS/RCF claims horizon |
| `complex` | deepen | complex-plane bad conjugation-product imaginary-part and bad unit-square real-part rows now have source-linked QF_LRA/Farkas regressions; keep analytic theorems Lean-horizon |
| `divisibility-and-euclid` | maintain | use gcd/Bezout rows as arithmetic-certificate examples |
| `modular-arithmetic` | maintain | keep LIA nonunit/CRT and BV fixed-width nonunit-inverse/Fermat-unit residue routes distinct |
| `groups` | maintain | table replay plus Alethe equality conflicts |
| `rings` | maintain | BV fixed finite rings only when width is conceptually relevant |
| `fields` | maintain | finite fields plus linear-algebra links; arbitrary-field facts horizon |
| `polynomials` | deepen | generated `bridge_polynomial_coefficient_factor_replay` now groups fixed identities, factor/division witnesses, finite coefficient windows, root-finding steps, derivative shadows, and rational polynomial-geometry obligations; polynomial identities have a QF_LIA false-root regression, factorization has a QF_LRA/Farkas discriminant regression, and root-finding has exact polynomial evaluation plus QF_LRA/Farkas bad-step and bad-width regressions |
| `sequences-and-limits` | deepen | bounded Cauchy-tail, bad reciprocal-tail, and bounded monotone-prefix bad-bound rows now have QF_LRA/Farkas regressions; convergence theorems stay Lean horizon |
| `counting` | maintain | finite-counting replay bridge now groups pigeonhole CNF/LRAT, coefficient-count, double-counting, finite orbit-count, and exact tail-count rows |
| `number-theory` | maintain | bounded residue and Diophantine families |
| `linear-algebra` | deepen | matrix corpus notes, dot-product/separator/KKT/active-set-QP/SDP/gradient-step/line-search/Wolfe/projected-gradient/proximal-gradient/circle-tangent/inversion rows, and route-specific regression back-links |
| `calculus` | deepen | one-variable false derivative, Riemann-sum false integral, multivariable bad-gradient, finite root-finding bad-step and bad-width, finite KKT bad-stationarity and bad-complementarity, finite active-set QP bad-free-gradient, bad inactive-slack, and bad-degenerate-multiplier, finite gradient-descent bad-decrease, bad step-coordinate, and bad-descent-bound, finite line-search bad-Armijo, bad descent-direction, and bad accepted-candidate, finite Wolfe bad-minimizer, bad sufficient-decrease, and bad-curvature, finite projected-gradient bad-projection and bad projected-decrease, and finite proximal-gradient bad-proximal-point, bad composite-decrease, and bad box-proximal-point rows now have QF_LRA/Farkas regressions |

## Commit-Sized Queue

Pick one row per commit unless the change is purely navigational.

1. Landed: promote the `proof-methods-refutation-v0` and `counting-v0`
   `PHP(3,2)` rows through source-linked DIMACS plus DRAT/LRAT regression.
2. Landed: classify `bounded-dynamics-v0`, `complex-algebraic-v0`,
   `coordinate-geometry-v0`, `finite-measure-v0`, `finite-operator-v0`, and
   initially `finite-topology-v0` as explicit non-benchmark educational rows
   until they gain negative, certificate-bearing examples. Finite topology has
   since been promoted by item 20.
3. Landed: promote `generating-functions-v0` through a source-linked finite
   Cauchy-product coefficient QF_LIA/Diophantine artifact and route regression.
4. Landed: promote `polynomial-identities-v0` through a source-linked false
   rational-root QF_LIA/Diophantine artifact and route regression.
5. Landed: promote `finite-predicate-v0` through a source-linked finite
   quantifier-expansion Bool/CNF artifact and DRAT/LRAT route regression.
6. Landed: promote `calculus-riemann-sum-v0` through a source-linked false
   integral QF_LRA/Farkas artifact and route regression.
7. Landed: promote `sequence-limit-shadow-v0` through source-linked bounded
   Cauchy-tail and bad reciprocal-tail bound QF_LRA/Farkas artifacts and route
   regressions.
8. Landed: add `bounded-monotone-sequence-v0` with finite monotone-prefix,
   finite supremum, finite tail-gap replay, a checked bad upper-bound
   QF_LRA/Farkas artifact, and a monotone-convergence Lean-horizon row.
9. Landed: add `finite-recurrence-prefix-v0` with Fibonacci prefix replay,
   affine recurrence replay, companion-matrix state replay, checked bad
   finite-value and bad affine-step QF_LRA/Farkas artifacts, and a
   recurrence-theory Lean-horizon row.
10. Landed: promote `multivariable-calculus-rational-v0` through a source-linked
   bad-gradient QF_LRA/Farkas artifact and route regression.
11. Landed: promote `calculus-algebraic-shadow-v0` through a source-linked
   false-derivative QF_LRA/Farkas artifact and route regression.
12. Landed: promote `complex-plane-transforms-v0` through source-linked
   bad unit-square real-part and bad conjugation-product imaginary-part
   QF_LRA/Farkas artifacts and route regressions.
13. Landed: promote `induction-obligations-v0` through a source-linked bounded
   bad-step count QF_LIA arithmetic-DPLL artifact and route regression.
14. Landed: promote `cardinality-principles-v0` through a source-linked
   overlap-additivity count QF_LIA/Diophantine artifact and route regression.
15. Landed: promote `polynomial-factorization-rational-v0` through a
   source-linked irreducible-quadratic discriminant QF_LRA/Farkas artifact and
   route regression.
16. Landed: promote `reals-rcf-shadow-v0` through a source-linked
   negative-discriminant QF_LRA/Farkas artifact and route regression, closing
   the current unclassified solver-reuse queue.
17. Landed: promote `finite-measure-v0` through a source-linked bad complement
   QF_LRA/Farkas artifact and route regression.
18. Landed: add `finite-measure-monotonicity-v0` with normalized finite
   measure-table replay, subset monotonicity, union subadditivity, a checked
   QF_LRA/Farkas bad subset-measure artifact, a checked bad
   union-subadditivity artifact, and a Lean-horizon row for
   countable/convergence measure theory.
19. Promote or classify any newly added unclassified packs, starting with compact
   source-level conflicts where the route is clear.
20. Landed: promote `finite-topology-v0` through a source-linked
   missing-empty-set Bool/CNF DIMACS artifact and DRAT/LRAT route regression.
21. Landed: promote `coordinate-geometry-v0` through a source-linked bad
   squared-distance QF_LRA/Farkas artifact and route regression.
22. Landed: promote `finite-operator-v0` through a source-linked bad
   operator-bound QF_LRA/Farkas artifact and route regression.
23. Landed: promote `complex-algebraic-v0` through a source-linked bad
   norm-squared QF_LRA/Farkas artifact and route regression.
24. Landed: promote `bounded-dynamics-v0` through a source-linked bad
   invariant-bound QF_LRA/Farkas artifact and route regression, closing the
   explicit non-benchmark-horizon queue.
25. Landed: add `proof-object-anatomy-end-to-end.md`, following
   `proof-methods-refutation-v0` from the PHP(3,2) source claim through
   committed CNF, emitted DRAT/LRAT proof objects, and same-artifact
   corrupted-proof rejection.
26. Landed: add `farkas-certificate-anatomy-end-to-end.md`, following
   `linear-optimization-v0` from the exact LP threshold conflict through source
   SMT-LIB, emitted `UnsatFarkas` evidence, and same-artifact multiplier tamper
   rejection.
27. Landed: add `alethe-certificate-anatomy-end-to-end.md`, following
   `equivalence-classes-v0` from the quotient-map congruence conflict through
   source SMT-LIB, emitted zero-trust `UnsatAletheProof` evidence, and
   same-artifact truncated-proof rejection.
28. Landed: add `diophantine-certificate-anatomy-end-to-end.md`, following
   `modular-arithmetic-v0` from the nonunit modular-inverse obstruction through
   source SMT-LIB, emitted `UnsatDiophantine` evidence, and same-artifact
   contradiction-row tamper rejection.
29. Landed: add `qf-bv-bitblast-certificate-anatomy-end-to-end.md`, following
   `finite-fields-v0` from the fixed-width composite-modulus no-inverse row
   through source SMT-LIB, generated DIMACS/DRAT evidence, and same-artifact
   truncated-DRAT rejection.
27. Landed: add
   `generated/solver-reuse-disposition-audit.md`, regenerated from pack
   metadata and freshness-checked by `check-foundational-resources`, so the
   promoted/non-benchmark-horizon/unclassified solver-reuse disposition counts
   stay machine-visible.
28. Revisit the library boundary after unclassified packs are resolved and at
   least one non-doc consumer repeats resource parsing logic.
29. Landed: add generated probability/statistics bridge rows for finite
   probability mass tables, pushforward distributions, stochastic kernels,
   conditional expectation, and tail/count obstructions, keeping the finite
   table and theorem-horizon vocabulary shared across existing packs.
30. Landed: add generated proof/logic bridge rows for refutation-as-query,
   finite proof-pattern replay, finite quantifier expansion, and bounded
   induction obligations, keeping proof-method and finite-logic vocabulary
   shared across existing packs.
31. Landed: add generated proof-object anatomy bridge rows for Boolean
   CNF DRAT/LRAT, QF_LRA Farkas, QF_UF Alethe, and QF_BV bit-blast
   certificates, making the existing certificate lessons and route regressions
   queryable as first-class atlas vocabulary.
32. Landed: add generated set/foundations bridge rows for finite Boolean
   algebra, finite partition/relation roundtrips, finite
   image/preimage/inverse tables, finite bijection/cardinality, and
   cardinality theorem horizons, making the finite/infinite set-theory boundary
   queryable as first-class atlas vocabulary.
33. Landed: add standalone finite topology and finite measure learner pages,
   splitting first-principles topology axiom replay and finite
   sigma-algebra/measure replay out of the combined topology/measure bridge
   lesson.
34. Landed: add standalone linear optimization learner page, splitting exact
   LP feasible-point replay, objective-threshold replay, checked
   QF_LRA/Farkas infeasible-threshold evidence, and tamper rejection out of the
   combined linear-system/LP bridge lesson.
35. Landed: add standalone finite probability mass-table learner page,
   splitting exact PMF normalization, conditional probability replay, Bayes
   posterior replay, checked QF_LRA/Farkas bad-normalization rejection, checked
   bad-conditional-probability rejection, checked bad-posterior rejection,
   finite independence replay, and checked bad-independence rejection
   out of the broad finite-probability process
   bridge lesson.
36. Landed: add standalone finite-operator learner page, splitting exact
   finite-dimensional `l1` norm replay, row-sum operator-bound replay,
   Chebyshev recurrence replay, and checked QF_LRA/Farkas bad norm/bound/
   prefix evidence out of the broad bounded-dynamics/operator bridge lesson.
37. Landed: add standalone bounded-dynamics learner page, splitting exact
   recurrence trace replay, finite invariant checking, threshold reachability,
   and checked QF_LRA/Farkas bad transition-step, bad threshold-step, and bad invariant-bound
   evidence out of the combined finite dynamics/Euler bridge lesson.
38. Landed: add standalone finite-Euler learner page, splitting exact
   explicit-Euler transition replay, finite polynomial-solution error tables,
   monotone invariant checking, checked QF_LRA/Farkas bad max-error plus
   bad terminal-error and bad-step evidence, and the ODE/numerical-analysis Lean horizon out of the combined finite
   dynamics/Euler bridge lesson.
39. Landed: add dynamics field-readiness consumer query coverage, extending
   [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
   `scripts/check-foundational-resources.sh` with a
   `differential_equations_and_dynamical_systems` plus Farkas field summary so
   the recent bounded-dynamics, finite-Euler, stochastic-kernel, and
   hitting-time resources are discoverable from the public JSON contract.
40. Landed: add generated geometry and complex-analysis bridge-concept rows.
   `bridge_coordinate_orientation_geometry` makes coordinate, affine, and
   oriented-area finite rational replay queryable as a shared geometry concept;
   `bridge_complex_real_pair_transform` makes complex arithmetic and
   rational-transform real-pair replay queryable as a shared complex-analysis
   concept. The atlas now validates 42 bridge rows while keeping synthetic,
   differential, global, and analytic theorem coverage in the Lean-horizon
   lane.
41. Landed: add generated functional-analysis bridge-concept rows.
   `bridge_inner_product_projection` makes finite rational Gram, projection,
   residual, and Gram-Schmidt replay queryable as a shared functional-analysis
   concept; `bridge_finite_operator_chebyshev` makes finite-dimensional
   operator bounds, Chebyshev recurrence, interpolation matrices, and
   alternating residual rows queryable as a shared operator-theory concept. The
   increment raised the atlas to 44 bridge rows while keeping Banach, Hilbert,
   compact-operator, minimax, and infinite-dimensional approximation theorem
   coverage in the Lean-horizon lane.
42. Landed: add generated measure-theory bridge-concept rows.
   `bridge_finite_measure_additivity` makes finite event-algebra/additivity,
   complement, monotonicity, and exact atom-sum replay queryable as a shared
   measure concept; `bridge_finite_product_integration` makes finite product
   tables, marginals, finite Fubini-style sums, simple-function integrals, and
   expectation replay queryable as a shared measure/probability concept. The
   atlas now validates 46 bridge rows while keeping Lebesgue measure,
   product-measure existence, convergence theorems, and almost-everywhere
   coverage in the Lean-horizon lane.
43. Landed: add measure-theory field-readiness consumer query coverage.
   `CONSUMER-QUERIES.md` and `check-foundational-resources.sh` now exercise
   measure/Farkas field readiness, measure bridge concept lookup, and checked
   measure-theory Farkas rows, making finite measure, product-measure,
   integration, random-variable, conditional-expectation, martingale, kernel,
   hitting-time, and concentration resources discoverable from the committed
   JSON contract.
44. Landed: add generated optimization/convexity bridge-concept rows.
   `bridge_lp_objective_farkas` makes exact LP feasibility, objective-threshold
   witnesses, and checked Farkas conflicts queryable as a shared optimization
   concept; `bridge_rational_convexity_shadow` makes finite midpoint/Jensen
   shadows, affine monotonicity, gradient replay, Hessian-minor witnesses, and
   least-squares normal-equation replay queryable as a shared convexity
   concept. The atlas now validates 48 bridge rows while keeping duality, KKT
   sufficiency, SDP, and convergence theorem coverage in the Lean-horizon lane.
45. Landed: add optimization/convexity field-readiness consumer query
   coverage. `CONSUMER-QUERIES.md` and
   `check-foundational-resources.sh` now exercise optimization/Farkas field
   readiness, LP-objective bridge lookup, convexity bridge lookup, and checked
   optimization/convexity Farkas rows, making LP thresholds, finite convexity
   shadows, least-squares, gradient/Hessian replay, residual bounds, eigenpair,
   and related matrix witnesses discoverable from the committed JSON contract.
46. Landed: add `incidence-geometry-v0` as the next curriculum-adjacent
   geometry pack. The pack validates exact line-equation replay, non-parallel
   line intersection, point-on-line replay, checked QF_LRA/Farkas rejection of
   false intersection-coordinate and incidence claims, a focused learner page,
   and a bridge-row update so geometry queries expose incidence as a
   first-class promoted pack.
47. Landed: add `rigid-configuration-geometry-v0` as the next distinct
   geometry pack. The pack validates exact triangle distance-table replay,
   translation isometry replay, congruent-triangle distance replay, checked
   QF_LRA/Farkas rejection of a false distance-table claim, a focused learner
   page, and a bridge-row update so geometry queries now expose five promoted
   packs.
48. Landed: add `finite-root-finding-v0` as the next numerical-analysis and
   real-analysis pack. The pack validates exact bisection/Newton replay,
   residual-decrease checking, checked QF_LRA/Farkas rejection of a false
   Newton iterate, a focused learner page, and concept links under reals,
   polynomials, calculus, numerical analysis, real analysis, optimization, and
   the bounded-theorem-shadow bridge.
49. Landed: add `finite-separation-v0` as the next optimization/convexity and
   real-analysis pack. The pack validates exact convex-combination replay,
   separating-hyperplane score replay, supporting-face checking, checked
   QF_LRA/Farkas rejection of a false separator, a focused learner page, and
   concept links under reals, linear algebra, optimization/convexity, and the
   rational-convexity bridge.
50. Landed: add `finite-kkt-v0` as the next distinct optimization/convexity
   pack. The pack validates exact constrained-quadratic grid replay,
   stationarity replay, complementary-slackness replay, checked QF_LRA/Farkas
   rejection of a false stationarity multiplier, a focused learner page, and
   concept links under reals, calculus, linear algebra, optimization/convexity,
   and the rational-convexity bridge.
51. Landed: add `finite-sdp-v0` as the next distinct optimization/convexity
   and linear-algebra pack. The pack validates exact two-by-two PSD replay,
   trace/objective arithmetic, dual-slack matrix replay, zero duality-gap
   checking, checked QF_LRA/Farkas rejection of a false objective claim, a
   focused learner page, and concept links under reals, linear algebra,
   optimization/convexity, LP objective/Farkas, and the rational-convexity
   bridge.
52. Landed: add `finite-gradient-descent-v0` as the next distinct
   optimization/convexity and numerical-analysis pack. The pack validates
   exact quadratic gradient replay, one gradient-descent step, objective
   decrease and descent-bound replay, checked QF_LRA/Farkas rejection of a
   false decrease claim, a focused learner page, and concept links under
   reals, calculus, linear algebra, numerical analysis, optimization/convexity,
   and the rational-convexity bridge. Later rows now also reject false
   step-coordinate and false descent-bound claims through the same checked
   QF_LRA/Farkas route.
53. Landed: add `finite-line-search-v0` as the next distinct
   optimization/convexity and numerical-analysis pack. The pack validates
   exact descent-direction replay, one rejected Armijo trial step, one accepted
   backtracked step, checked QF_LRA/Farkas rejection of a false Armijo
   acceptance claim, a focused learner page, and concept links under reals,
   calculus, numerical analysis, optimization/convexity, and the
   rational-convexity bridge.
54. Landed: add `finite-projected-gradient-v0` as the next distinct
   optimization/convexity and numerical-analysis pack. The pack validates exact
   gradient replay, one unconstrained trial step, interval projection,
   projected objective decrease, checked QF_LRA/Farkas rejection of false
   projected-point and projected-decrease claims, a focused learner page, and
   concept links under reals,
   calculus, numerical analysis, optimization/convexity, and the
   rational-convexity bridge.
55. Landed: add `finite-proximal-gradient-v0` as the next distinct
   optimization/convexity and numerical-analysis pack. The pack validates exact
   smooth-gradient replay, one ordinary trial step, L1 soft-threshold proximal
   replay, composite objective decrease, checked QF_LRA/Farkas rejection of a
   false proximal point, a focused learner page, and concept links under reals,
   calculus, numerical analysis, optimization/convexity, and the
   rational-convexity bridge.
56. Landed: add `finite-wolfe-line-search-v0` as the next distinct line-search
   pressure after Armijo backtracking. The pack validates exact
   descent-direction replay, exact one-dimensional minimizer replay, Wolfe
   sufficient-decrease and curvature replay, checked QF_LRA/Farkas rejection of
   a false curvature claim, a focused learner page, and concept links under
   reals, calculus, numerical analysis, optimization/convexity, and the
   rational-convexity bridge.
57. Landed: add `finite-active-set-qp-v0` as the next distinct active-set
    optimization pack. The pack validates exact unconstrained-minimizer replay,
    active-face candidate replay, KKT stationarity/complementarity, inactive
    slack, checked QF_LRA/Farkas rejection of a false free-gradient claim, a
    focused learner page, and concept links under reals, calculus, linear
    algebra, numerical analysis, optimization/convexity, and the
    rational-convexity bridge.
58. Landed: add `finite-circle-geometry-v0` as the next distinct geometry
    pack. The pack validates exact point-on-circle replay, tangent-line/radius
    perpendicularity, chord-midpoint perpendicularity, circle-line intersection
    replay, checked QF_LRA/Farkas rejection of false radius and
    line-intersection claims, a focused learner page, and concept links under
    reals, polynomials, linear algebra, and the shared coordinate-geometry
    bridge.
59. Landed: add `finite-inversion-geometry-v0` as the next distinct inversion
    geometry pack. The pack validates exact unit-circle inversion replay,
    inverse-distance product replay, collinearity replay, checked QF_LRA/Farkas
    rejection of a false inverse-coordinate claim, a focused learner page, and
    concept links under reals, polynomials, linear algebra, and the shared
    coordinate-geometry bridge.
60. Landed: add
    [MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md](MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md)
    as the top-down plan for building the 23-node curriculum and 18-field
    taxonomy into resource waves, acceptance gates, field-by-field priorities,
    proof routes, solver reuse, consumer boundaries, and the next commit-sized
    queue. This is a plan-only increment; the next pack should be chosen by the
    distinct-object/distinct-route rule in that plan.
61. Landed: add `finite-cyclic-geometry-v0` as the next distinct cyclic
    geometry pack. The pack validates exact cyclic quadrilateral replay,
    diagonal-intersection and diagonal-perpendicularity replay, opposite-angle
    dot-product replay, rational Ptolemy replay, checked QF_LRA/Farkas
    rejection of false diagonal-intersection, opposite-angle, and Ptolemy
    claims, a focused learner page, and concept links under reals,
    polynomials, linear algebra, and the shared coordinate-geometry bridge.
62. Landed: add
    [`matrix-computation-index.md`](../learn/math/matrix-computation-index.md)
    as the route-oriented learner index for LU, rank/nullity, residual,
    projection, eigenpair, characteristic-polynomial, checked trace-invariant,
    finite random-matrix, chain-complex, operator, module, and tensor rows.
    The index groups existing validated packs by replay, QF_LRA/Farkas,
    QF_UF/Alethe, QF_LIA/Diophantine, Lean-horizon, and numerical-honesty
    boundaries.
63. Landed: add
    [`analysis-calculus-theorem-horizon-map.md`](../learn/math/analysis-calculus-theorem-horizon-map.md)
    as the theorem-horizon map for analysis/calculus-adjacent resources. The
    page groups completeness, IVT/MVT/FTC, compactness, sequence convergence,
    recurrence/asymptotics, root-finding convergence, optimization convergence,
    measure/probability convergence, functional analysis/operator theory, and
    dynamics by current finite shadow, checked evidence route, missing Lean
    dependency, and next build artifact.
64. Landed: add
    [`matrix-corpus-benchmark-boundary.md`](../learn/math/matrix-corpus-benchmark-boundary.md)
    as the matrix-resource boundary note. The page separates educational
    matrix rows, solver regressions, benchmark-corpus rows, and theorem-horizon
    claims; lists the current matrix families; and records the promotion
    checklist needed before solver-reuse or performance language is used.
65. Landed: add
    [`tax-benefit-arithmetic-v0`](../rules-as-code/examples/tax-benefit-arithmetic-v0/)
    as the third rules/law pack. The pack reuses integer thresholds,
    household-size adjustments, caps, active phase-out monotonicity,
    effective-date witnesses, and checked Bool/QF_LIA proof fixtures while the
    rules validator replays the full piecewise finite sample.
66. Landed: add the generated
    [`rules-query-dashboard.md`](../rules-as-code/generated/rules-query-dashboard.md)
    plus deterministic generated query-row JSON under
    [`../rules-as-code/generated/queries/`](../rules-as-code/generated/queries/)
    as the first rules/law generated-query surface. The dashboard reads the
    committed rule-pack JSON and reports bounded sample rows, generated row
    counts, and coverage, equivalence, threshold, cap, version-delta, and
    monotonicity query-family counts.
67. Landed: add
    [`procurement-scoring-v0`](../rules-as-code/examples/procurement-scoring-v0/)
    as the fourth rules/law pack. The pack reuses finite predicate exclusions,
    bid-cap and encoded-deadline arithmetic, bonus-threshold witnesses,
    score-monotonicity rows, and checked Bool/QF_LIA proof fixtures while the
    rules validator replays the bounded procurement sample and generated query
    rows.
68. Landed: add
    [`grant-allocation-v0`](../rules-as-code/examples/grant-allocation-v0/)
    as the rational-allocation rules/law pack. The pack reuses exact shares,
    budget balance, minimum-share floors, administrative caps, bounded
    rational replay, and checked QF_LRA/Farkas proof fixtures while the rules
    validator replays bounded allocation and balanced-budget generated rows.
69. Landed: add
    [`RULES-LAW-QUERIES.md`](RULES-LAW-QUERIES.md) plus
    `scripts/query-rules-as-code.py` as the rules/law consumer-query surface.
    The standard `just rules-as-code` gate now smoke-checks summary counts,
    procurement pack lookup, checked obligation lookup, generated
    quality-score family lookup, and bounded late-submission generated rows.
70. Landed: add
    [`RULES-LAW-PATTERN-MATRIX.md`](RULES-LAW-PATTERN-MATRIX.md) as the
    rules/law pattern matrix. The matrix maps finite predicates, exclusions,
    role/tenant relations, thresholds, caps, deadlines, monotonicity, version
    transitions, precedence, and bounded implementation-equivalence patterns
    back to math concept rows, proof routes, current rule packs, generated
    query families, and smoke-checked query commands without adding a premature
    rule ontology.
71. Landed: add
    [`rules-law-trust-boundary.md`](../learn/rules-law-trust-boundary.md) as
    the learner-facing trust-boundary walkthrough for rules/law resources. The
    page explains how to read current packs from source rule to formal model,
    replayed witness, checked obligation, and legal/theorem horizon, while
    preserving the no-legal-advice and no-benchmark boundary.
69. Landed: add functional-analysis/operator field-readiness consumer query
    coverage. `CONSUMER-QUERIES.md` and
    `check-foundational-resources.sh` now exercise the
    `functional_analysis_and_operator_theory` Farkas field summary, the
    operator bridge concept lookup, and checked finite-operator,
    inner-product, Chebyshev, and spectral Farkas rows, making that field's
    finite-dimensional resources visible through the committed JSON contract.
68. Landed: add topology field-readiness consumer query coverage.
    `CONSUMER-QUERIES.md` and `check-foundational-resources.sh` now exercise
    the topology Boolean field summary, compactness and preimage bridge
    concept lookups, and checked topology Boolean/Alethe rows, making finite
    topology, compactness, connectedness, continuous-map, homology, metric, and
    bounded epsilon-delta resources visible through the committed JSON
    contract.
69. Landed: add statistics field-readiness consumer query coverage.
    `CONSUMER-QUERIES.md` and `check-foundational-resources.sh` now exercise
    the statistics Farkas field summary, finite-table and tail-count bridge
    lookups, checked exact-rational statistics rows, including the bad
    variance Farkas row, and checked Diophantine
    count rows, making exact finite tests, contingency tables, regression,
    random-matrix, finite probability, process-table, and concentration
    resources visible through the committed JSON contract.
70. Landed: add linear-algebra field-readiness consumer query coverage.
    `CONSUMER-QUERIES.md` and `check-foundational-resources.sh` now exercise
    linear-algebra Farkas and Alethe field summaries, rank and projection
    bridge concept lookups, checked exact-rational matrix rows, and checked
    equality-heavy finite vector-space, dual-space, module, and tensor rows,
    making the matrix/algebraic linear-algebra lane visible through the
    committed JSON contract.
71. Landed: add core algebra/number/graph field-readiness consumer query
    coverage. `CONSUMER-QUERIES.md` and `check-foundational-resources.sh` now
    exercise abstract-algebra Alethe field readiness, homomorphism/ideal bridge
    concept lookups, checked Alethe and fixed-width QF_BV finite-algebra rows,
    number-theory Diophantine field readiness, finite-family lookups, checked
    integer-arithmetic rows, graph-theory Boolean field readiness,
    graph-family lookups, and checked finite coloring, reachability, matching,
    cut, and d-separation rows, making those core lanes visible through the
    committed JSON contract without promoting theorem-horizon claims.
72. Landed: add analysis/numerical/complex field-readiness consumer query
    coverage. `CONSUMER-QUERIES.md` and `check-foundational-resources.sh` now
    exercise real-analysis Farkas field readiness, epsilon/gradient bridge
    concept lookups, checked bounded-analysis rows, numerical-analysis Farkas
    field readiness, residual/operator bridge concept lookups, checked exact
    numerical rows, complex-analysis Farkas field readiness, real-pair bridge
    lookup, and checked algebraic complex rows, making those analysis lanes
    visible through the committed JSON contract without promoting
    completeness, convergence, floating-point stability, holomorphic,
    analytic-continuation, or theorem-level calculus claims.
73. Landed: add foundations/discrete/probability field-readiness consumer query
    coverage. `CONSUMER-QUERIES.md` and `check-foundational-resources.sh` now
    exercise logic/proof Boolean field readiness, proof-vocabulary lookups,
    checked proof-pattern/CNF rows, set-theory/foundations Alethe field
    readiness, partition bridge lookups, checked finite
    relation/function/quotient rows, discrete-math Diophantine field
    readiness, finite-family lookups, checked counting/coefficient/tail-count
    rows, probability-theory Farkas field readiness, probability-table
    lookups, and checked finite probability/process rows, making those early
    curriculum and probability lanes visible through the committed JSON
    contract without promoting theorem-horizon claims.
74. Landed: add the all-field readiness query matrix.
    [FIELD-READINESS-QUERY-MATRIX.md](FIELD-READINESS-QUERY-MATRIX.md) now
    gives downstream consumers a compact 18-field table of pack/check counts,
    primary readiness routes, bridge lookup terms, checked-row drilldowns, and
    theorem-horizon boundaries, while preserving the JSON-first R6 boundary and
    avoiding a premature typed API, crate, or repo split.
75. Landed: make matrix rows queryable by bridge concept plus proof route.
    [MATRIX-COMPUTATION-QUERIES.md](MATRIX-COMPUTATION-QUERIES.md) documents
    the new `packs --concept ... --route ...` and
    `checks --concept ... --route ... --proof-status checked` flow for LU,
    residual, rank/nullity, eigenpair, random-matrix, tensor/module, operator,
    and Chebyshev resources; `check-foundational-resources.sh` now smoke-checks
    representative matrix concept queries.
76. Landed: add proof-route summary queries.
    [PROOF-ROUTE-QUERY-MATRIX.md](PROOF-ROUTE-QUERY-MATRIX.md) documents the
    `routes --route ... [--field ...]` flow over proof-cookbook recipe links,
    covering finite replay, Boolean CNF/LRAT, QF_BV, QF_LIA/Diophantine,
    QF_LRA/Farkas, QF_UF/Alethe, and Lean-horizon routes with explicit
    boundaries; `check-foundational-resources.sh` smoke-checks representative
    route summaries.
77. Landed: add number-system semantic-boundary bridge rows.
    `bridge_exact_vs_floating_arithmetic` makes exact rational replay,
    QF_LRA/Farkas rows, numerical shadows, and floating-point/numerical-honesty
    boundaries queryable across real analysis, linear algebra, numerical
    analysis, statistics, and optimization. `bridge_totality_conventions`
    makes SMT totality, explicit side conditions, and frontend
    trapping/UB boundaries queryable across number theory, foundations, real
    analysis, and numerical resources. That increment raised the atlas to 50
    bridge rows.
78. Landed: add the gcd/divisibility witness bridge row.
    `bridge_gcd_divisibility_witness` makes gcd/common-divisor replay, Bezout
    coefficient replay, quotient witnesses, modular nonunit obstructions, and
    checked gcd non-divisibility certificates queryable from the atlas. The
    number-theory consumer smoke now includes gcd concept lookup, and that
    increment raised the atlas to 51 bridge rows.
79. Landed: add the modular CRT/inverse witness bridge row.
    `bridge_modular_crt_inverse_witness` makes concrete CRT congruence
    witnesses, modular inverse witnesses, fixed residue searches, finite-field
    unit/nonunit contrasts, quotient-ring-adjacent vocabulary, and the checked
    nonunit Diophantine and fixed-width QF_BV certificates queryable from the atlas. The
    number-theory consumer smoke now includes CRT concept lookup, and that
    increment raised the atlas to 52 bridge rows.
80. Landed: add the finite-counting replay bridge row.
    `bridge_finite_counting_replay` makes permutation/Pascal rows, pigeonhole
    proof routes, double-counting tables, coefficient extraction, finite
    orbit-count replay, and exact finite tail-count contradictions queryable
    from the atlas. The discrete-math consumer smoke now includes counting
    concept lookup and concept-scoped Boolean/Diophantine route queries, and
    that increment raised the atlas to 53 bridge rows.
81. Landed: add the finite graph replay/obstruction bridge row.
    `bridge_finite_graph_replay_obstruction` makes finite coloring,
    reachability/traversal, matching, cut, and d-separation packs queryable
    from the atlas while preserving the boundary around graph theorems,
    causal claims, and asymptotic traversal complexity. The graph-theory
    consumer smoke now includes reachability lookup and concept-scoped Boolean
    route queries, and that increment raised the atlas to 54 bridge rows.
82. Landed: add the finite dynamics/Euler replay bridge row.
    `bridge_finite_dynamics_euler_replay` makes finite recurrence-prefix,
    bounded-dynamics, and explicit-Euler packs queryable from the atlas while
    preserving the boundary around ODE theory, stability, convergence rates,
    stiffness, chaos, and PDE claims. The dynamics consumer smoke now includes
    Euler lookup and concept-scoped Farkas route queries, and that increment
    raised the atlas to 55 bridge rows.
83. Landed: add the finite circle/inversion/cyclic replay bridge row.
    `bridge_finite_circle_inversion_cyclic_replay` makes finite circle,
    inversion, and cyclic-configuration packs queryable from the atlas while
    preserving the boundary around general circle, inversion,
    cyclic-quadrilateral, angle, Ptolemy, and synthetic geometry theorems. The
    geometry consumer smoke now includes circle lookup and concept-scoped
    Farkas route queries, and that increment raised the atlas to 56 bridge
    rows.
84. Landed: add the finite chain-complex/homology replay bridge row.
    `bridge_finite_chain_homology_replay` makes finite simplicial-complex
    closure, oriented-boundary replay, boundary-squared-zero, Betti-rank
    replay, checked bad-boundary coefficient evidence, and checked
    boundary-square cancellation evidence queryable from the
    atlas while preserving the boundary around homology invariance, exact
    sequences, homotopy equivalence, cohomology-operation laws, and general
    algebraic topology. The topology consumer smoke now includes homology lookup and
    concept-scoped Diophantine route queries, and the atlas now validates 57
    bridge rows.
85. Landed: add the finite topology-operator/homeomorphism bridge row.
    `bridge_finite_topology_operator_homeomorphism` makes finite topology
    axioms, closure/interior replay, continuity by open preimage,
    homeomorphism replay, checked malformed-topology Bool/CNF rows, and checked
    malformed-preimage QF_UF/Alethe rows queryable from one shared atlas
    concept while keeping Kuratowski closure axioms, arbitrary-space
    homeomorphism invariance, compactness/connectedness preservation, homology
    invariance, and general topology theorems in the Lean-horizon lane. The
    topology consumer smoke now includes closure/homeomorphism lookup and
    concept-scoped Alethe route queries, and the atlas now validates 58 bridge
    rows.
86. Landed: add the finite boundary-operator replay bridge row.
    `bridge_finite_boundary_operator_replay` makes oriented boundary
    coefficients, boundary-of-boundary cancellation, boundary-matrix shape, and
    checked bad-boundary coefficient plus boundary-square cancellation evidence
    queryable from one shared atlas
    concept while keeping functoriality, exactness, homology invariance,
    cohomology-operation laws, and general algebraic topology in the Lean-horizon lane. The
    topology consumer smoke now includes boundary lookup and concept-scoped
    Diophantine route queries, and the atlas now validates 59 bridge rows.
87. Landed: add the finite specialization-order replay bridge row.
    `bridge_finite_specialization_order_replay` makes finite topology to
    preorder replay, singleton-closure characterization, finite `T0`
    antisymmetry replay, and checked bad `T0` QF_UF/Alethe evidence queryable
    from one shared atlas concept while keeping T0 quotients, sobriety,
    Alexandroff-space/domain-theory results, and arbitrary-space
    specialization-order theorems in the Lean-horizon lane. The topology
    consumer smoke now includes specialization lookup and concept-scoped
    Alethe route queries, and the atlas now validates 60 bridge rows.
88. Landed: add the finite cohomology replay bridge row.
    `bridge_finite_cohomology_replay` makes finite F2 cochain coboundary
    replay, `delta^2 = 0`, F2 cohomology-rank replay, non-coboundary cocycle
    checking, and checked bad coboundary-value QF_UF/Alethe evidence queryable
    from one shared atlas concept while keeping cohomology functoriality,
    cohomology-operation laws, universal coefficients, de Rham comparison,
    sheaf cohomology, duality, and invariance in the Lean-horizon lane. The topology consumer
    smoke now includes cohomology lookup and concept-scoped Alethe route
    queries, and the atlas now validates 61 bridge rows.
89. Landed: add `finite-simplicial-cup-products-v0` and the finite
    cup-product replay bridge row. `bridge_finite_cup_product_replay` makes
    ordered F2 cup-product replay, one finite coboundary-Leibniz row, and
    checked bad cup-product QF_BV/DRAT evidence queryable from one shared atlas
    concept while keeping associativity, graded commutativity, naturality,
    cohomology-ring quotienting, universal coefficients, and invariance in the
    Lean-horizon lane. The topology consumer smoke now includes cup lookup and
    concept-scoped QF_BV route queries, and the atlas now validates 62 bridge
    rows.
90. Landed: add `finite-chain-complex-torsion-v0` and the finite
    torsion-homology replay bridge row. `bridge_finite_torsion_homology_replay`
    makes a two-term integer chain complex, one-entry Smith diagonal replay,
    `H0 = Z/2`, and checked bad torsion-generator QF_LIA/Diophantine evidence
    queryable from one shared atlas concept while keeping general Smith normal
    form, universal coefficients, Ext/Tor functor laws, exact sequences, and
    homology invariance in the Lean-horizon lane. The topology consumer smoke
    now includes torsion lookup and concept-scoped Diophantine route queries,
    and the atlas now validates 63 bridge rows.
91. Landed: add `finite-universal-coefficient-shadow-v0` and the finite
    universal-coefficient shadow bridge row.
    `bridge_finite_universal_coefficient_shadow` makes one integer dual
    cochain complex, `H^1 = Z/2`, degree-one Hom/Ext bookkeeping, and checked
    bad `H^1 = 0` QF_UF/Alethe evidence queryable from one shared atlas
    concept while keeping the universal coefficient theorem, naturality,
    splitting choices, Ext/Tor laws, exact sequences, and invariance in the
    Lean-horizon lane. The topology consumer smoke now includes universal
    lookup and concept-scoped Alethe route queries, and the atlas now validates
    64 bridge rows.
92. Landed: add `finite-quotient-topology-v0` and
    `bridge_finite_quotient_topology_replay`.
    The new bridge makes quotient-map fibers, same-fiber equivalence pairs,
    quotient topology by preimage-open enumeration, saturated-open image
    replay, and checked bad representative/open QF_UF/Alethe evidence queryable from
    one shared atlas concept while keeping quotient topology universal
    properties, quotient-map theorem schemas, and arbitrary preservation or
    invariance theorems in the Lean-horizon lane. The topology consumer smoke
    now includes quotient lookup and concept-scoped Alethe route queries, and
    the atlas now validates 65 bridge rows.
93. Landed: add `metric-ball-epsilon-delta-index.md` as the cross-pack learner
    path for bounded real-analysis, finite metric continuity, sequence-tail
    shadows, finite compactness, finite connectedness, and finite
    continuity/open-preimage replay. The bridge source refs and consumer smoke
    now make `bridge_metric_ball` and
    `bridge_bounded_epsilon_delta_shadow` discoverable through topology and
    real-analysis queries while keeping quantified continuity, compactness,
    connectedness, convergence, and arbitrary-space theorem claims in the
    Lean-horizon lane.
94. Landed: add `graph-traversal-runtime-index.md` as the cross-pack learner
    path for finite reachability, deterministic BFS/DFS traces,
    shortcut-tail visited-node counters, checked QF_LIA cost refutations, and
    asymptotic graph-search theorem horizons. The graph consumer smoke now
    exposes `bridge_finite_graph_replay_obstruction` through LIA route queries
    alongside the existing Boolean graph rows.
95. Landed: add `chebyshev-operator-index.md` as the cross-pack learner path
    for finite-dimensional operator bounds, Chebyshev recurrence values,
    Vandermonde interpolation matrices, alternating residuals, checked
    QF_LRA/Farkas bad-grid, bad-norm, and bad-bound rows, spectral rows, and
    characteristic-polynomial arithmetic. The functional-analysis/operator
    consumer smoke now exposes `bridge_finite_operator_chebyshev` through
    concept-scoped Farkas route queries while keeping Banach/Hilbert-space,
    compact-operator, Haar-space, minimax, alternation-theorem, and
    infinite-dimensional approximation claims in the Lean-horizon lane.
96. Landed: add `random-matrix-moment-index.md` as the cross-pack learner path
    for finite matrix-valued probability tables, exact trace/determinant
    moments, expected Gram matrices, rank-mixture probabilities, checked
    QF_LRA/Farkas bad trace-square and expected-rank evidence, and adjacent
    finite probability/statistics table patterns. The probability/statistics
    consumer smoke now exposes `bridge_random_matrix_finite_moment` through
    concept-scoped Farkas route queries while keeping asymptotic spectral laws,
    universality, concentration theorems, simulation quality, and
    high-dimensional random-matrix claims in the theorem/numerical-honesty
    lanes.
97. Landed: promote the concrete `finite-algebra-homomorphisms-v0`
    bad group-homomorphism row through QF_UF/Alethe. Finite table replay
    identifies the failing pair `1+1`: the malformed map has `phi(2)=1`,
    while the codomain table gives `phi(1)+phi(1)=0`; the new source-linked
    SMT-LIB artifact checks that isolated equality conflict with
    `prove_qf_uf_unsat_alethe` and `Evidence::check`. The abstract-algebra
    consumer smoke now includes concept-scoped
    `bridge_homomorphism_preservation` Alethe checked-row queries while
    keeping general isomorphism, quotient, categorical, and infinite-algebra
    theorems in the Lean-horizon lane.
98. Landed: promote the `finite-order-lattices-v0` bad top-element
    set-family row through Bool/CNF DRAT/LRAT. Finite relation replay checks
    the Boolean lattice order and identifies `B !<= A`; the bad claim that
    `A` is top requires `B <= A`. The new one-variable DIMACS artifact,
    `bad-top-element-rejected.cnf`, is now checked by
    `math_resource_boolean_routes`, and the consumer smoke includes
    concept-scoped `bridge_finite_boolean_algebra` Boolean checked-row
    queries. Complete-lattice fixed-point theorems, Boolean representation
    theorems, domain theory, Galois connections, and infinite order theory
    remain Lean-horizon.
99. Landed: extend `finite-rings-v0` with a second fixed-width
    QF_BV/DRAT route for a bad multiplicative identity row. Finite table
    replay checks the XOR additive group and associative zero multiplication,
    then isolates `1*1=0` while the claimed identity law requires `1`; the
    source SMT-LIB artifact and `math_resource_bv_routes` regression check the
    resulting one-bit contradiction without promoting general ring theory.
100. Landed: extend `finite-fields-v0` with a bad prime-field inverse-candidate
     row. Finite replay computes `3*4 mod 7 = 5` while the false inverse claim
     requires `1`; the new fixed-width SMT-LIB artifact is checked by
     `math_resource_bv_routes`, and the learner pages now distinguish this
     bad-candidate pressure from the existing composite no-inverse row.
101. Landed: extend `finite-cyclic-geometry-v0` with a checked bad
     opposite-angle dot-product row. Exact replay computes
     `(A-B) . (C-B) = 0` at vertex `B` in the inscribed square, while the
     malformed source SMT-LIB artifact claims `1`; the shared QF_LRA/Farkas
     route now checks both the diagonal-intersection and angle-dot cyclic
     conflicts without claiming general cyclic-geometry theorem coverage.
102. Landed: extend `finite-circle-geometry-v0` with a horizontal
     circle-line intersection witness and checked bad line-intersection row.
     Exact replay checks the diameter line `y=0`, endpoints `(-1,0)` and
     `(1,0)`, midpoint `(0,0)`, and right intersection `(1,0)`, while the
     malformed source SMT-LIB artifact claims right-intersection
     x-coordinate `2`; the shared QF_LRA/Farkas route now checks both the
     radius and line-intersection circle conflicts without claiming general
     circle-line theorem coverage.
103. Landed: extend `finite-cyclic-geometry-v0` with a rational Ptolemy
     rectangle witness and checked bad Ptolemy row. Exact replay checks the
     origin-centered `4 x 3` rectangle, side lengths `4,3,4,3`, diagonal
     lengths `5,5`, and Ptolemy equality `5*5 = 4*4 + 3*3 = 25`, while the
     malformed source SMT-LIB artifact claims the replayed right-hand side is
     `24`; the shared QF_LRA/Farkas route now checks diagonal-intersection,
     opposite-angle, and Ptolemy cyclic conflicts without claiming the general
     Ptolemy theorem.
104. Landed: extend `finite-operator-v0` with a checked bad `l1` sum-norm
     row. Exact replay checks `u=(1,2)`, `v=(3,-1)`, `u+v=(4,1)`,
     `||u||_1=3`, `||v||_1=4`, and `||u+v||_1=5`, while the malformed source
     SMT-LIB artifact claims `||u+v||_1 <= 4`; the shared QF_LRA/Farkas route
     now checks both finite-operator norm and operator-bound conflicts without
     claiming general normed-space theorem coverage.
105. Landed: extend `inner-product-spaces-rational-v0` with a checked bad
     projection-orthogonality row. Exact replay checks the projection of
     `[2,3]` onto `span([1,1])`, residual `[-1/2,1/2]`, and
     `<residual,[1,1]> = 0`, while the malformed source SMT-LIB artifact
     claims the same residual inner product is `1`; the shared QF_LRA/Farkas
     route now checks both the bad negative-norm and bad
     projection-orthogonality conflicts without claiming general Hilbert-space
     projection theorem coverage.
106. Landed: extend `spectral-linear-algebra-v0` with a checked bad Rayleigh
     quotient row. Exact replay checks `v^T*A*v = 6`, `v^T*v = 2`, and
     quotient `3` for `v=[1,1]` under `A=[[2,1],[1,2]]`, while the malformed
     source SMT-LIB artifact claims quotient `4`; the shared QF_LRA/Farkas
     route now checks both the bad Rayleigh-quotient and bad eigenpair
     conflicts without claiming the spectral theorem or Rayleigh-Ritz
     optimization coverage.
107. Landed: extend `linear-algebra-rational-v0` with a checked bad LU
     product-entry row. Exact replay computes `(L*U)[1,1] = 3` for the listed
     rational factors, while the malformed source SMT-LIB artifact claims the
     same product entry is `4`; the shared QF_LRA/Farkas route now checks this
     decomposition arithmetic conflict alongside the existing singular-system
     conflict without claiming pivoting, existence, or numerical-stability
     coverage.
108. Landed: extend `matrix-invariants-v0` with a checked bad trace-invariant
     row. Exact replay computes `trace([[2,1],[1,2]]) = 4`, while the malformed
     source SMT-LIB artifact claims the same trace is `5`; the shared
     QF_LRA/Farkas route now checks both trace arithmetic and characteristic
     polynomial conflicts without claiming general spectral-invariant theorem
     coverage.
109. Landed: extend `bounded-dynamics-v0` with a checked bad transition-step
     row. Exact recurrence replay computes the plus-two transition after state
     `2` as `4`, while the malformed source SMT-LIB artifact claims the same
     next state is `5`; the shared QF_LRA/Farkas route now checks both local
     transition arithmetic and invariant-bound conflicts without claiming
     continuous-time dynamics, ODE existence/uniqueness, stability, chaos, or
     PDE coverage.
110. Landed: extend `finite-euler-method-v0` with a checked bad max-error-bound
     row. Exact finite error-table replay computes maximum error `3/4` for the
     quadratic-forcing Euler trace, while the malformed source SMT-LIB artifact
     claims `max_error <= 1/2`; the shared QF_LRA/Farkas route now checks both
     finite error-bound and fixed-step conflicts without claiming convergence,
     stability, floating-point accuracy, or continuous-time ODE theory.
111. Landed: extend `orientation-area-geometry-v0` with a checked bad
     affine-area-scaling row. Exact affine replay computes source signed double
     area `12`, determinant `5`, and image signed double area `60`, while the
     malformed source SMT-LIB artifact claims the image area equals the source
     area; the shared QF_LRA/Farkas route now checks both area-scaling and
     fixed-orientation conflicts without claiming general affine-volume,
     projective, differential, or synthetic geometry theorems.
112. Landed: extend `complex-algebraic-v0` with a checked bad product-real-part
     row. Exact real-pair replay computes `(1 + 2i) * (3 - i) = 5 + 5i`,
     while the malformed source SMT-LIB artifact claims product real part `4`;
     the shared QF_LRA/Farkas route now checks both product-coordinate and
     norm-squared conflicts without claiming holomorphy, contour integration,
     residues, analytic continuation, or algebraic-closure theorems.
113. Landed: extend `affine-geometry-v0` with a checked bad
     midpoint-coordinate row. Exact affine replay computes midpoint
     `M = (2,1)` for the segment `(0,0)` to `(4,2)` and `T(M) = (6,4)`, while
     the malformed source SMT-LIB artifact claims image y-coordinate `5`; the
     shared QF_LRA/Farkas route now checks midpoint-coordinate,
     collinearity-determinant, and distance-preservation conflicts without
     claiming general affine-space, projective, differential, or synthetic
     geometry theorems.
114. Landed: extend `incidence-geometry-v0` with a checked bad
     intersection-coordinate row. Exact line-intersection replay checks
     `(2,1)` for `x + y - 3 = 0` and `x - y - 1 = 0`, while the malformed
     source SMT-LIB artifact claims intersection x-coordinate `3`; the shared
     QF_LRA/Farkas route now checks both intersection-coordinate and
     point-on-line conflicts without claiming projective, synthetic, or
     configuration geometry theorems.
115. Landed: extend `rigid-configuration-geometry-v0` with a checked bad
     translation-image row. Exact translation replay computes
     `(3,0) + (1,-2) = (4,-2)`, while the malformed source SMT-LIB artifact
     claims translated x-coordinate `5`; the shared QF_LRA/Farkas route now
     checks both translation-image and distance-table conflicts without
     claiming graph rigidity, rigid-motion classification, or synthetic
     geometry theorems.
116. Landed: extend `coordinate-geometry-v0` with a checked bad
     midpoint-coordinate row. Exact midpoint replay computes `(2,1)` for the
     segment `(0,0)` to `(4,2)`, while the malformed source SMT-LIB artifact
     claims midpoint x-coordinate `3`; the shared QF_LRA/Farkas route now
     checks both midpoint-coordinate and squared-distance conflicts without
     claiming synthetic, projective, differential, or global geometry
     theorems.
117. Landed: extend `finite-inversion-geometry-v0` with a checked bad
     inverse-distance-product row. Exact unit-circle inversion replay computes
     `|p|^2 = 5`, `|I(p)|^2 = 1/5`, and squared-radius product `1` for
     `p = (2,1)`, while the malformed source SMT-LIB artifact claims product
     `2`; the shared QF_LRA/Farkas route now checks both inverse-coordinate
     and inverse-distance-product conflicts without claiming angle
     preservation, circle-line inversion correspondences, power-of-a-point, or
     general inversion geometry.
118. Landed: extend `finite-product-measure-v0` with a checked bad marginal
     row. Exact finite product-table replay recomputes the `heads` marginal as
     `1/6 + 1/6 + 1/6 = 1/2`, while the malformed source SMT-LIB artifact
     claims `2/3`; the shared QF_LRA/Farkas route now checks both product
     atom and marginal conflicts without claiming general product-measure
     construction, Fubini/Tonelli, kernels, or almost-everywhere theory.
119. Landed: extend `descriptive-statistics-v0` with a checked bad variance
     row. Exact finite-sample replay computes mean `5/2`, second moment
     `15/2`, `mean^2 = 25/4`, and population variance `5/4`, while the
     malformed source SMT-LIB artifact claims `3/2`; the shared QF_LRA/Farkas
     route now checks exact-rational statistic contradictions alongside the
     existing QF_LIA/Diophantine contingency-total row without claiming
     inference, estimation, or asymptotic statistics. A later split makes this
     proof-object row explicit as `qf-lra-bad-variance`.
120. Landed: extend `exact-statistical-tests-v0` with a checked bad Fisher
     left-tail row. Exact fixed-margin replay computes the one-sided Fisher
     left tail as `(1 + 16) / 70 = 17/70`, while the malformed source SMT-LIB
     artifact claims `1/4`; the shared QF_LRA/Farkas route now checks the
     final exact-rational p-value contradiction alongside the existing
     QF_LIA/Diophantine binomial tail-count row without claiming asymptotic
     tests, floating-point statistical libraries, or full test-family
     coverage.
121. Landed: extend `exact-statistical-tests-v0` with a probability-ordered
     two-sided Fisher replay row and checked bad two-sided p-value row. Exact
     fixed-margin replay includes top-left counts `0`, `1`, `3`, and `4`,
     computing `(1 + 16 + 16 + 1) / 70 = 17/35`, while the malformed source
     SMT-LIB artifact claims `1/2`; the shared QF_LRA/Farkas route now checks
     both one-sided and probability-ordered two-sided Fisher p-value
     contradictions while keeping other two-sided conventions, exact
     multinomial tests, asymptotics, and floating-point library behavior
     outside the claim.
122. Landed: extend `exact-statistical-tests-v0` with a probability-ordered
     exact multinomial replay row and checked bad multinomial p-value row.
     Exact finite enumeration over three uniform categories with `n = 3`
     includes `[3,0,0]`, `[0,3,0]`, and `[0,0,3]`, computing
     `3 * (1/27) = 1/9`, while the malformed source SMT-LIB artifact claims
     `1/6`; the shared QF_LRA/Farkas route now checks exact multinomial
     p-value contradictions while keeping asymptotic tests, floating-point
     library behavior, and broad exact-test-family coverage outside the
     claim.
123. Landed: extend `numerical-linear-algebra-v0` with a checked bad Jacobi
     first-step error-bound row. Exact rational iteration replay recomputes
     the fixed Jacobi step `[1/4, 2/3]`, exact solution `[1/11, 7/11]`, and
     `||x1 - x*||_inf = 7/44`, while the malformed source SMT-LIB artifact
     claims `||x1 - x*||_inf <= 1/8`; the shared QF_LRA/Farkas route now
     checks both residual-bound and iteration-error contradictions without
     claiming floating-point accuracy, conditioning, backward stability, or
     general Jacobi convergence.
124. Landed: extend `finite-markov-chain-v0` with a checked bad stationary
     distribution row. Exact row-vector transition replay computes
     `[1/2,1/2] * P = [3/8,5/8]` for the fixed two-state chain, while the
     malformed source SMT-LIB artifact claims the first next-coordinate is
     `1/2`; the shared QF_LRA/Farkas route now checks both malformed
     stochastic-row and false stationary-distribution contradictions without
     claiming countably infinite chains, mixing times, convergence theorems,
     recurrence/transience, or stochastic-process limit laws.
125. Landed: extend `finite-concentration-v0` with a checked bad union-bound
     row. Exact finite event replay computes `P(A union B)=3/4` while the
     malformed source SMT-LIB artifact claims `P(A union B) <= 1/2`; the
     shared QF_LRA/Farkas route now checks both tail and union finite
     concentration contradictions without claiming Chernoff/Hoeffding/LLN/CLT,
     martingale concentration, asymptotics, or general limit theorems.
126. Landed: extend `finite-stochastic-kernels-v0` with a checked bad
     composition-entry row. Exact two-step kernel replay computes
     `(K;L)(rainy, early)=22/75`, while the malformed source SMT-LIB artifact
     claims `1/3`; the shared QF_LRA/Farkas route now checks both kernel-row
     normalization and kernel-composition contradictions without claiming
     regular conditional probabilities, general disintegration, Markov kernels
     on arbitrary measurable spaces, or stochastic-process convergence.
127. Landed: extend `finite-hitting-times-v0` with a checked bad survival-mass
     row. Exact finite first-hit replay computes `P(T > 4)=5/16`, while the
     malformed source SMT-LIB artifact claims `1/4`; the shared QF_LRA/Farkas
     route now checks both finite-horizon survival-mass and expected-time
     contradictions without claiming recurrence/transience, optional stopping,
     mixing bounds, Markov-chain potential theory, or infinite-horizon
     convergence.
128. Landed: split `finite-martingales-v0` so exact bounded-stopping and bad
     martingale rows remain replay-only, while `qf-lra-bad-stopped-expectation`
     and `qf-lra-bad-martingale` own the checked Farkas proof-object
     contradictions. Exact bounded stopping replay recomputes stopped values
     `1, 1, 0, -2` and `E[M_tau]=0`, and the bad martingale replay recomputes
     the up-block conditional expectation as `3/2`; the shared QF_LRA/Farkas
     route checks the isolated false claims `1/2` and `1` without claiming
     general optional stopping, martingale convergence, Doob inequalities,
     stochastic integration, or continuous-time martingales.
129. Landed: extend `finite-measure-monotonicity-v0` with a checked bad
     union-subadditivity row. Exact inclusion-exclusion replay recomputes
     `mu(A union B)=1` and `mu(A)+mu(B)=4/3`, while the malformed source
     SMT-LIB artifact claims `mu(A union B)=3/2` under the finite
     subadditivity obligation; the shared QF_LRA/Farkas route now checks both
     subset-monotonicity and union-subadditivity contradictions without
     claiming countable subadditivity, monotone/dominated convergence,
     arbitrary measure spaces, or almost-everywhere reasoning.
130. Landed: extend `finite-probability-v0` with a replayed finite
     independence witness and a checked bad-independence row. Exact atom-table
     replay recomputes `P(heads)=1/2`, `P(red)=1/2`, and
     `P(heads and red)=1/4`, while the malformed source SMT-LIB artifact
     claims `P(heads and red)=1/3` under the finite independence equation; the
     shared QF_LRA/Farkas route now checks normalization, conditioning, Bayes,
     and independence contradictions without claiming continuous
     distributions, sampling guarantees, or asymptotic probability theory.
131. Landed: extend `finite-conditional-expectation-v0` with a checked bad
     total-expectation row. Exact finite partition replay recomputes
     `E[X]=7/2` and `E[E[X|G]]=7/2`, while the malformed source SMT-LIB
     artifact claims `E[E[X|G]]=4` under the law-of-total-expectation
     equality; the shared QF_LRA/Farkas route now checks bad high-block,
     total-expectation, tower-property, and variance-decomposition
     contradictions without claiming Radon-Nikodym construction, regular
     conditional probabilities, optional stopping, or general
     measure-theoretic conditional expectation.
132. Landed: extend `random-matrix-finite-v0` with a checked bad
     expected-rank row. Exact rational row-reduction replay computes rank
     probabilities `P(rank=0)=P(rank=1)=P(rank=2)=1/3` and `E[rank]=1`,
     while the malformed source SMT-LIB artifact claims `E[rank]=2`; the
     shared QF_LRA/Farkas route now checks both bad trace-square and bad
     expected-rank contradictions without claiming asymptotic spectral laws,
     universality, concentration theorems, simulation quality, or numerical
     eigensolver behavior.
133. Landed: extend `finite-operator-v0` with a checked bad Chebyshev-prefix
     row. Exact recurrence replay at `x=1/2` computes `T3=-1`, while the
     malformed source SMT-LIB artifact claims the shifted value
     `T3+1=1/2`; the shared QF_LRA/Farkas route now checks the recurrence
     value conflict without promoting Haar-space, minimax, Banach/Hilbert, or
     infinite-dimensional approximation theorems.
134. Landed: extend `least-squares-regression-v0` with a checked bad
     RSS-improvement row. Exact mean-baseline replay computes baseline RSS
     `14/3`, model RSS `1/6`, and improvement `9/2`, while the malformed
     source SMT-LIB artifact claims improvement `4`; the shared QF_LRA/Farkas
     route now checks both normal-equation coefficient and RSS-improvement
     contradictions without claiming Gauss-Markov, inference, asymptotic, or
     floating-point regression coverage.
135. Landed: extend `finite-gradient-descent-v0` with a checked bad
     step-coordinate row. Exact quadratic step replay computes
     `next_x = 1 - (1/4)*2 = 1/2`, while the malformed source SMT-LIB artifact
     claims `next_x = 3/4`; the shared QF_LRA/Farkas route now checks both
     descent-value and step-coordinate contradictions without claiming
     convergence rates, stochastic variants, line-search theory, or
     floating-point optimization coverage.
136. Landed: extend `finite-line-search-v0` with a checked bad
     accepted-candidate row. Exact Armijo backtracking replay computes
     `accepted_x = 1 + (1/2)*(-2) = 0`, while the malformed source SMT-LIB
     artifact claims `accepted_x = 1/4`; the shared QF_LRA/Farkas route now
     checks both rejected-step Armijo violation and accepted-candidate
     arithmetic without claiming line-search termination, Wolfe conditions,
     convergence, stochastic variants, or floating-point stability.
137. Landed: extend `finite-wolfe-line-search-v0` with a checked bad
     line-minimizer row. Exact one-dimensional replay computes
     `alpha = 1/2` and `x = 0`, while the malformed source SMT-LIB artifact
     claims `alpha = 1`; the shared QF_LRA/Farkas route now checks both
     exact-minimizer and curvature contradictions without claiming Wolfe
     existence, strong-Wolfe variants, convergence, stochastic line search, or
     floating-point stability.
138. Landed: add
     [`GEOMETRY-RESOURCE-QUERIES.md`](GEOMETRY-RESOURCE-QUERIES.md) as the
     finite-geometry consumer query guide. The guide and resource smoke now
     exercise concept-scoped Farkas pack/check queries for
     `bridge_coordinate_orientation_geometry` and
     `bridge_finite_circle_inversion_cyclic_replay`, making
     coordinate/incidence/rigid/affine/orientation rows and
     circle/inversion/cyclic rows discoverable without claiming synthetic,
     projective, differential, global, or higher-degree geometry theorems.
139. Landed: add
     [`ALGEBRA-STRUCTURE-QUERIES.md`](ALGEBRA-STRUCTURE-QUERIES.md) as the
     finite-algebra consumer query guide. The guide and resource smoke now
     exercise concept-scoped Alethe/QF_BV checks for
     `bridge_homomorphism_preservation`, `bridge_group_action`,
     `bridge_module_action`, `bridge_ideal_closure`, and
     `bridge_modular_crt_inverse_witness`, making finite algebra rows
     discoverable without claiming arbitrary group/ring/module/category,
     classification, isomorphism, or infinite-algebra theorems.
140. Landed: add
     [`GRAPH-DISCRETE-QUERIES.md`](GRAPH-DISCRETE-QUERIES.md) as the
     graph/discrete consumer query guide. The guide and resource smoke now
     exercise concept-scoped Boolean, QF_BV, and LIA checks for
     `bridge_finite_graph_replay_obstruction`, making finite coloring,
     reachability, matching, cut, d-separation, fixed-width coloring, and
     BFS/DFS runtime rows discoverable without claiming general graph
     theorems, asymptotic algorithms, graph-family lower bounds, or
     average-case traversal guarantees.
141. Landed: add
     [`NUMBER-ARITHMETIC-QUERIES.md`](NUMBER-ARITHMETIC-QUERIES.md) as the
     number/arithmetic consumer query guide. The guide and resource smoke now
     exercise concept-scoped Diophantine, QF_BV, totality, and
     exact-vs-floating checks for gcd/divisibility, modular CRT/inverse,
     fixed-width residue, quotient/ideal, and semantic-boundary rows without
     claiming analytic number theory, algebraic number theory, unbounded
     induction, or floating-point guarantees.
142. Landed: add
     [`PROBABILITY-STATISTICS-QUERIES.md`](PROBABILITY-STATISTICS-QUERIES.md)
     as the probability/statistics consumer query guide. The guide and resource
     smoke now exercise concept-scoped Farkas checks for probability-mass,
     finite-measure, product/integration, pushforward, conditional-expectation,
     stochastic-kernel, tail-count, and random-matrix moment rows without
     claiming continuous probability, asymptotic statistics, stochastic-process
     limits, simulation quality, or floating-point inference guarantees.
143. Landed: add
     [`TOPOLOGY-HOMOLOGY-QUERIES.md`](TOPOLOGY-HOMOLOGY-QUERIES.md) as the
     topology/homology consumer query guide. The guide and resource smoke now
     exercise concept-scoped Boolean, Farkas, Alethe, Diophantine, and QF_BV
     checks for metric shadows, compactness, connectedness, quotient topology,
     specialization order, finite homology, torsion, cohomology, UCT shadows,
     and cup-product rows without claiming general topology, invariance,
     exact-sequence, UCT naturality, or cohomology-ring theorems.
144. Landed: extend `finite-kkt-v0` with a source-linked checked
     bad-complementarity row. The pack now validates exact KKT stationarity,
     complementary-slackness replay, checked bad-stationarity evidence, and
     checked bad-complementarity evidence while keeping KKT sufficiency,
     constraint qualifications, duality, and convergence in the Lean-horizon
     lane.
145. Landed: extend `finite-projected-gradient-v0` with a source-linked
     checked bad projected-decrease row. Exact objective replay computes
     projected decrease `3` for the interval-projected quadratic step, while
     the malformed source SMT-LIB artifact claims the same decrease is `4`;
     the shared QF_LRA/Farkas route now checks both projected-feasibility and
     projected-decrease conflicts without claiming convergence or rate
     theorems.
146. Landed: extend `finite-euler-method-v0` with a source-linked checked bad
     terminal-error row. Exact finite error-table replay computes terminal
     error `|9/4 - 3/2| = 3/4`, while the malformed source SMT-LIB artifact
     claims terminal error `1/2`; the shared QF_LRA/Farkas route now checks
     fixed-step, pointwise-error, and max-error conflicts without claiming
     convergence, stability, floating-point accuracy, or continuous-time ODE
     theory.
147. Landed: extend `finite-sdp-v0` with a source-linked checked bad
     slack-entry row. Exact primal/dual replay computes bottom-right slack
     entry `1` in `S = C - yI`, while the malformed source SMT-LIB artifact
     claims `1/2`; the shared QF_LRA/Farkas route now checks objective,
     duality-gap, and slack-entry conflicts without claiming SDP duality,
     Slater conditions, KKT sufficiency, or algorithm convergence.
148. Landed: extend `finite-wolfe-line-search-v0` with a source-linked checked
     bad sufficient-decrease row. Exact Wolfe replay computes Armijo RHS
     `1/2`, accepted value `0`, and sufficient-decrease slack `1/2`, while the
     malformed source SMT-LIB artifact claims the same slack is nonpositive;
     the shared QF_LRA/Farkas route now checks minimizer, sufficient-decrease,
     and curvature conflicts without claiming Wolfe existence, strong-Wolfe,
     convergence, rate, nonconvex, stochastic, or floating-point guarantees.
149. Landed: extend `finite-active-set-qp-v0` with a source-linked checked bad
     inactive-slack row. Exact active-face replay computes inactive lower-bound
     slack `0 - (-1) = 1` at `(1,1)`, while the malformed source SMT-LIB
     artifact claims that the same slack is nonpositive; the shared
     QF_LRA/Farkas route now checks free-gradient, inactive-slack, and
     degenerate-multiplier conflicts without claiming active-set termination,
     cycling avoidance, convergence, or numerical stability.
150. Landed: extend `finite-gradient-descent-v0` with a source-linked checked
     bad descent-bound row. Exact descent replay computes decrease `11/4`,
     descent bound `5/2`, and positive slack `1/4`, while the malformed
     source SMT-LIB artifact claims that the same slack is nonpositive; the
     shared QF_LRA/Farkas route now checks bad decrease, bad step-coordinate,
     and bad descent-bound conflicts without claiming convergence rates,
     stochastic variants, line-search theory, or floating-point optimization
     coverage.
151. Landed: extend `finite-line-search-v0` with a source-linked checked bad
     descent-direction row. Exact directional-derivative replay computes
     `2 * (-2) = -4`, while the malformed source SMT-LIB artifact claims the
     derivative is nonnegative; the shared QF_LRA/Farkas route now checks
     rejected-step Armijo violation, descent-direction sign, and
     accepted-candidate arithmetic without claiming line-search termination,
     Wolfe conditions, convergence, stochastic variants, or floating-point
     stability.
152. Landed: extend `finite-proximal-gradient-v0` with a source-linked checked
     bad composite-decrease row. Exact composite replay computes start value
     `9/2`, proximal value `3`, and decrease `3/2`, while the malformed source
     SMT-LIB artifact claims decrease `2`; the shared QF_LRA/Farkas route now
     checks bad proximal-point, bad composite-decrease, and bad
     box-proximal-point conflicts without claiming proximal-gradient
     convergence, nonsmooth convex analysis, stochastic variants, active-set
     identification, or floating-point stability.
153. Landed: extend `bounded-dynamics-v0` with a source-linked checked bad
     threshold-step row. Exact replay of the plus-three trace computes state
     `6` at step `2`, below threshold `7` by shortfall `1`, while the malformed
     source SMT-LIB artifact claims threshold reachability at that step; the
     shared QF_LRA/Farkas route now checks local transition arithmetic,
     threshold-step reachability, and invariant-bound conflicts without
     claiming continuous-time dynamics, ODE existence/uniqueness, stability,
     chaos, or PDE coverage.
154. Landed: extend `complex-plane-transforms-v0` with a source-linked checked
     bad conjugation-product imaginary-part row. Exact real-pair replay
     computes both `conjugate(z*w)` and `conjugate(z)*conjugate(w)` as
     `5 - 5i` for `z = 1 + 2i` and `w = 3 - i`, while the malformed source
     SMT-LIB artifact claims imaginary part `5`; the shared QF_LRA/Farkas
     route now checks both conjugation-product imaginary-part and unit-square
     real-part conflicts without claiming holomorphicity, contour integration,
     residues, analytic continuation, or algebraic-closure theorems.
155. Landed: extend `numerical-linear-algebra-v0` with a source-linked checked
     bad solution-box upper-bound row. Exact rational linear-system replay
     computes the fixed solution as `[6/5, 6/5]`, while the malformed source
     SMT-LIB artifact claims `x0 <= 1`; the shared QF_LRA/Farkas route now
     checks residual-bound, solution-box upper-bound, and Jacobi error-bound
     conflicts without claiming floating-point accuracy, conditioning,
     backward-error analysis, or general convergence.
156. Landed: extend `linear-algebra-rational-v0` with a source-linked checked
     bad nullspace-component row. Exact rational matrix replay checks
     `A*v = [0, 0]` for `A = [[1, 2], [2, 4]]` and `v = [2, -1]`, while the
     malformed source SMT-LIB artifact claims `v0 = 1`; the shared
     QF_LRA/Farkas route now checks singular-system, LU product-entry, and
     nullspace-component conflicts without claiming general rank-nullity,
     basis-extension, pivoting, conditioning, or numerical-stability theorems.
157. Landed: extend `metric-continuity-v0` with a source-linked checked
     bad open-ball preimage row. Exact finite metric replay recomputes the
     preimage of the open output ball `|y - 0| < 1` as `{p0, p1}`, while the
     malformed source SMT-LIB artifact claims `p2` is in that preimage even
     though `|f(p2) - 0| = 1`; the shared QF_LRA/Farkas route now checks both
     bad-delta and bad-preimage strict-bound conflicts without claiming
     quantified continuity, arbitrary metric-space topology, compactness, or
     general topological preservation theorems.
158. Landed: add generated analysis bridge-concept rows for rational interval
     replay, sequence-tail shadows, Cauchy-tail shadows, squeeze shadows,
     derivative-identity shadows, and integration horizons. These rows make
     existing real-analysis, topology, numerical-analysis, measure-theory, and
     probability packs discoverable by reusable concept rather than by pack id,
     while keeping convergence, completeness, differentiability, integration,
     FTC, and measure-theoretic limit theorems in the Lean-horizon lane.
159. Landed: add the generated bounded-family/asymptotic boundary bridge row.
     `bridge_bounded_family_asymptotic_boundary` makes finite BFS/DFS runtime
     counters, recurrence prefixes, fixed generating-function coefficient
     windows, bounded dynamics traces, and finite Euler error rows queryable by
     one concept. Concept-scoped LIA and Farkas queries now find checked rows
     while asymptotic runtime, recurrence closed forms, convergence rates, and
     limiting theorem claims remain Lean-horizon.
160. Landed: extend `finite-probability-v0` with a checked bad
     total-variation row as the next distinct probability finite-table
     conflict. Exact replay compares
     `p=[1/2,1/3,1/6]` and `q=[1/3,1/3,1/3]`, recomputes absolute differences
     `1/6,0,1/6`, `l1_distance=1/3`, and `TV=1/6`, while the malformed source
     SMT-LIB artifact claims `TV=1/4`; the shared QF_LRA/Farkas route now
     checks normalization, conditioning, Bayes, independence, and finite
     distribution-distance conflicts without claiming continuous probability
     metrics, sampling guarantees, asymptotic inference, or measure-theoretic
     probability theorems.
161. Landed: extend `graph-d-separation-v0` with a source-linked checked
     unconditioned-collider blocker. Exact finite DAG replay enumerates the
     only skeleton path in `a -> b <- c`, observes that `b` is a collider and
     no collider or descendant is conditioned, and rejects the malformed
     d-connected claim. The new DIMACS artifact encodes the collider-specific
     blocking rule and is checked by
     `graph_d_separation_collider_unconditioned_blocks_emits_checked_drat_and_lrat`
     through emitted DRAT, elaborated LRAT, and independent proof checks.
     This lands the graph-depth queue item with a learner-readable graph shape
     without claiming causal identification, do-calculus, or probabilistic
     graphical-model semantics.
162. Landed: source-link the matrix-corpus QF_LRA/Farkas regressions that were
     still duplicating source constraints inline. The least-squares bad
     coefficients, numerical residual-bound, finite random-matrix trace-square,
     spectral bad-eigenpair, and matrix-invariant bad-characteristic rows now
     parse and prove the committed SMT-LIB artifacts directly, and their pack
     validators pin both the exact artifact paths and artifact-backed cargo
     regression names. The inner-product negative-norm row stays on the
     existing inline Farkas route because the current SMT-LIB route rejects its
     strict-inequality artifact shape; the pack still validates, and that row
     remains checked without overstating source-artifact coverage.
163. Landed: add `real-completeness-theorem-boundary.md` as the next
     real-analysis theorem-boundary artifact. The page ties
     `real-analysis-rational-v0`, `sequence-limit-shadow-v0`,
     `bounded-monotone-sequence-v0`, `metric-continuity-v0`,
     `reals-rcf-shadow-v0`, and `finite-compactness-v0` to
     least-upper-bound completeness, Cauchy completeness, monotone
     convergence, compactness, and uniform-continuity prerequisites. It records
     copyable checked-row queries, replay commands, Lean dependency rows, and
     graduation criteria while keeping finite rational samples, finite tails,
     finite covers, and algebraic shadows separate from theorem-level claims.
164. Landed: add `bridge_algebra_equality_certificate_boundary` and
     `algebra-equality-certificate-boundary.md` as the algebra promotion
     boundary for finite table replay versus scoped QF_UF/Alethe equality
     certificates. The page ties finite groups, monoids, permutation groups,
     group actions, homomorphisms, ideals, vector spaces, dual spaces, modules,
     and tensor products to copyable concept, pack, and checked-row queries
     while keeping arbitrary algebraic theorems and universal properties in the
     Lean-horizon lane.
165. Landed: extend `finite-conditional-expectation-v0` with a checked bad
     variance-decomposition row. Exact finite replay computes
     `Var(X)=35/4`, `E[Var(X|G)]=5/2`, and `Var(E[X|G])=25/4` for the four-atom
     conditioning partition, while the malformed source SMT-LIB artifact
     claims total variance `9`; the shared QF_LRA/Farkas route now checks bad
     high-block, total-expectation, tower-property, and variance-decomposition
     conflicts without claiming Radon-Nikodym construction, regular
     conditional probabilities, martingale convergence, or general
     measure-theoretic conditional expectation.
166. Landed: extend `finite-group-actions-v0` with a checked
     `bad-compatibility-rejected` row. Exact finite replay first confirms the
     malformed action keeps the identity law but fails compatibility at
     `s.(s.01)=10` while `(s*s).01=e.01=01`; the source SMT-LIB artifact then
     isolates that equality conflict for the shared QF_UF/Alethe route via
     `finite_group_actions_bad_compatibility_emits_checked_alethe`, leaving
     orbit-stabilizer, Burnside/Cauchy-Frobenius, quotient actions, and
     representation theory in the Lean-horizon lane.
167. Landed: extend `affine-geometry-v0` with a checked
     `bad-collinearity-determinant-rejected` row. Exact affine replay sends
     the collinear triple `(0,0)`, `(1,1)`, `(3,3)` to
     `(1,-1)`, `(4,3)`, `(10,11)` and computes image determinant `0`; the
     source QF_LRA artifact rejects the malformed determinant `1` claim via
     `affine_geometry_bad_collinearity_determinant_artifact_emits_checked_farkas`,
     adding a distinct incidence/collinearity proof shape without claiming
     general affine-geometry theorems.
168. Landed: extend `finite-quotient-topology-v0` with a checked
     `bad-fiber-representative-rejected` row. Exact quotient-map replay
     computes `q(a)=q(b)=p` for the same fiber `{a,b}`, while the malformed
     source SMT-LIB artifact claims `q(a) != q(b)`; the shared QF_UF/Alethe
     route checks this representative-consistency conflict without claiming
     quotient topology universal properties, quotient-map theorem schemas, or
     arbitrary quotient-space invariance.
169. Landed: split the hidden QF_UF/Alethe preimage-membership artifact in
     `finite-continuous-maps-v0` into the explicit checked row
     `qf-uf-bad-preimage-membership`. Exact finite topology replay still owns
     the bad continuity claim that `preimage({u}) = {0}` is not open in the
     Sierpinski domain; the source SMT-LIB artifact separately rejects the
     malformed preimage table that excludes `0` even though `f(0)=u` and
     `u in {u}`. The public query surface now reports 640 checks, 315 checked
     rows, and 53 checked QF_UF/Alethe rows.
170. Landed: extend `finite-simplicial-homology-v0` with checked
     `bad-boundary-square-rejected` and
     `qf-lia-bad-boundary-square-coefficient` rows. Exact replay expands
     `d([a,b,c]) = [b,c] - [a,c] + [a,b]`, recomputes the second boundary,
     and checks the `[b]` contributions `-1 + 1 = 0`; the source SMT-LIB
     artifact then rejects the malformed coefficient claim via
     `finite_simplicial_bad_boundary_square_coefficient_emits_checked_diophantine_evidence`.
     The public query surface now reports 642 checks, 317 checked rows, and
     58 checked QF_LIA/Diophantine rows.
171. Landed: split the `finite-modules-v0` scalar-closure proof-object check
     into the explicit `qf-uf-bad-submodule-scalar-closure` row. Exact finite
     replay still owns `bad-submodule-rejected` by computing `2*1 = 2` in the
     regular `Z/4Z` module and checking that `2` is absent from `{0,1}`; the
     source SMT-LIB artifact separately rejects the malformed membership claim
     through the existing
     `finite_modules_bad_submodule_emits_checked_alethe` regression. The
     public query surface now reports 643 checks, 318 checked rows, and
     row-scoped Alethe lookup for the pack returns the scalar-closure row.
172. Landed: split the `finite-vector-spaces-v0` additive-closure proof-object
     check into the explicit `qf-uf-bad-subspace-addition-closure` row. Exact
     finite replay still owns `bad-subspace-rejected` by computing
     `10 + 01 = 11` in `F2^2` and checking that `11` is absent from
     `{00,10,01}`; the source SMT-LIB artifact separately rejects the malformed
     membership claim through the existing
     `finite_vector_spaces_bad_subspace_emits_checked_alethe` regression. The
     public query surface now reports 644 checks, 319 checked rows, and
     row-scoped Alethe lookup for the pack returns the addition-closure row.
173. Landed: split the `finite-dual-spaces-v0` covector-additivity proof-object
     check into the explicit `qf-uf-bad-covector-additivity` row. Exact finite
     replay still owns `bad-covector-rejected` by computing `10 + 01 = 11`,
     `f(11) = 1`, and `f(10)+f(01)=0`; the source SMT-LIB artifact separately
     rejects the malformed fixed additivity equality through the existing
     `finite_dual_spaces_bad_covector_emits_checked_alethe` regression. The
     public query surface now reports 645 checks, 320 checked rows, and
     row-scoped Alethe lookup for the pack returns the additivity row.
174. Landed: split the `finite-tensor-products-v0` bad-bilinear
     proof-object check into the explicit
     `qf-uf-bad-bilinear-left-additivity` row. Exact finite replay still owns
     `bad-bilinear-map-rejected` by computing `10 + 01 = 11`,
     `beta(11,1)=00`, and `beta(10,1)+beta(01,1)=11`; the source SMT-LIB
     artifact separately rejects the malformed fixed additivity equality
     through the existing
     `finite_tensor_products_bad_bilinear_emits_checked_alethe` regression.
     The public query surface now reports 646 checks, 321 checked rows, and
     row-scoped Alethe lookup for the pack returns the left-additivity row.
175. Landed: split the `finite-order-lattices-v0` bad-partial-order
     proof-object check into the explicit
     `qf-uf-bad-partial-order-antisymmetry` row. Exact finite replay still
     owns `bad-partial-order-rejected` by computing `x <= y`, `y <= x`, and
     `x != y`; the source SMT-LIB artifact separately rejects the malformed
     fixed antisymmetry equality through the existing
     `finite_order_lattices_bad_partial_order_emits_checked_alethe`
     regression. The public query surface now reports 647 checks, 322 checked
     rows, and row-scoped Alethe lookup for the pack returns the antisymmetry
     row.
176. Landed: split the `finite-ideals-v0` bad-ideal proof-object check into
     the explicit `qf-uf-bad-ideal-additive-closure` row. Exact finite replay
     still owns `bad-ideal-rejected` by computing `2 + 2 = 4` in `Z/6Z` and
     checking that `4` is absent from `{0,2}`; the source SMT-LIB artifact
     separately rejects the malformed fixed additive-closure membership claim
     through the existing `finite_ideals_bad_ideal_emits_checked_alethe`
     regression. The public query surface now reports 648 checks, 322 checked
     rows, 255 replay-only rows, and row-scoped Alethe lookup for the pack
     returns the additive-closure row.
177. Landed: split the `finite-permutation-groups-v0` bad-nonbijection
     proof-object check into the explicit
     `qf-uf-bad-nonbijection-injectivity` row. Exact finite replay still owns
     `bad-nonbijection-rejected` by computing `bad(1)=1`, `bad(2)=1`, and the
     missing image `2`; the source SMT-LIB artifact separately rejects the
     malformed fixed injectivity claim through the existing
     `finite_permutation_groups_bad_nonbijection_emits_checked_alethe`
     regression. The public query surface now reports 649 checks, 322 checked
     rows, 256 replay-only rows, and row-scoped Alethe lookup for the pack
     returns the injectivity row.
178. Landed: split the `finite-monoids-v0` bad-nonassociative-table
     proof-object check into the explicit `qf-uf-bad-monoid-associativity`
     row. Exact finite replay still owns `bad-nonassociative-table-rejected`
     by computing `(b*b)*b = a` and `b*(b*b) = b`; the source SMT-LIB artifact
     separately rejects the malformed fixed associativity equality through the
     existing `finite_monoids_associativity_failure_emits_checked_alethe`
     regression. The public query surface now reports 650 checks, 322 checked
     rows, 257 replay-only rows, and row-scoped Alethe lookup for the pack
     returns the associativity row.
179. Landed: split `finite-group-actions-v0` identity-action and
     compatibility proof-object checks into explicit QF_UF/Alethe rows. The
     malformed table rows remain exact finite replay: identity replay computes
     `e.01 = 10` instead of `01`, and compatibility replay computes
     `s.(s.01)=10` while `(s*s).01=e.01=01`. The new
     `qf-uf-bad-identity-action` and `qf-uf-bad-action-compatibility` rows link
     the source SMT-LIB artifacts and the existing
     `finite_group_actions_bad_identity_emits_checked_alethe` /
     `finite_group_actions_bad_compatibility_emits_checked_alethe`
     regressions. The public query surface now reports 652 checks, 322 checked
     rows, 259 replay-only rows, and row-scoped Alethe lookup for identity and
     compatibility.
180. Landed: split `finite-measure-v0` bad complement-measure proof-object
     checking into the explicit `qf-lra-bad-complement-measure` row. Exact
     finite replay still owns `bad-complement-measure-rejected` by computing
     `mu(A)=1/3`, `mu(A^c)=2/3`, and `mu(U)=1` while the malformed row claims
     `mu(A^c)=1/2`; the source SMT-LIB artifact separately rejects the fixed
     complement-additivity contradiction through the existing
     `finite_measure_bad_complement_artifact_emits_checked_farkas`
     regression. The row-scoped Farkas lookup for the pack returns the
     complement row.
181. Landed: split `linear-algebra-rational-v0` bad LU product-entry checking
     into the explicit `qf-lra-bad-lu-product-entry` row. Exact LU replay still
     owns `bad-lu-product-entry-rejected` by computing `(L*U)[1,1]=3` for the
     listed factors while the malformed row claims `4`; the source SMT-LIB
     artifact separately rejects the fixed product-entry equality
     contradiction through the existing
     `linear_algebra_bad_lu_product_entry_artifact_emits_checked_farkas`
     regression. The row-scoped Farkas lookup for the pack returns the
     product-entry row.
182. Landed: split `descriptive-statistics-v0` bad variance proof-object
     checking into the explicit `qf-lra-bad-variance` row. Exact finite-sample
     replay still owns `bad-variance-rejected` by computing mean `5/2`, second
     moment `15/2`, `mean^2 = 25/4`, and population variance `5/4` while the
     malformed row claims `3/2`; the source SMT-LIB artifact separately
     rejects the fixed variance equation through the existing
     `descriptive_stats_bad_variance_artifact_emits_checked_farkas`
     regression. The public query surface now reports 655 checks, 322 checked
     rows, 262 replay-only rows, and row-scoped Farkas lookup for the pack
     returns the explicit variance row.

## Validation Checklist

For plan-only edits:

```sh
git diff --check
./scripts/check-links.sh
```

For resource metadata or generated dashboard changes:

```sh
./scripts/check-foundational-resources.sh
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary
```

For a pack upgrade:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>
<route-specific cargo test>
./scripts/check-foundational-resources.sh
./scripts/check-links.sh
```

For a solver-reuse promotion, the pack must link the route regression and the
regression must include the source artifact from the pack folder.
