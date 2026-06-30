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
[MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md](MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md)
for the top-down curriculum-wide buildout plan,
[MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md](MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md)
for per-node gates, [RESOURCE-BUILDOUT-ROADMAP.md](RESOURCE-BUILDOUT-ROADMAP.md)
for the broader resource-family plan, and
[PROOF-UPGRADE-FRONTIER.md](PROOF-UPGRADE-FRONTIER.md) for route-specific proof
upgrades.

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
- 48 bridge-concept rows.
- 5 example-family rows.
- 102 non-template math packs.
- 516 expected checks.
- 222 checked proof/evidence rows.
- 229 replay-only rows.
- 65 Lean-horizon rows.
- 102 promoted solver-reuse packs.
- 0 non-benchmark-horizon solver-reuse packs.
- 0 unclassified solver-reuse packs.

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

### Wave 1: Stabilize The Current 102 Packs

Goal: every current non-template pack has a deliberate R5 disposition:
`promoted`, `non-benchmark-horizon`, or a clear reason to remain unclassified.

Current unclassified queue: empty.

Current non-benchmark queue: empty.

Last row closed:

| Pack | Upgrade Trigger |
|---|---|
| `finite-cyclic-geometry-v0` | added and promoted through a bad diagonal-intersection row with a source-linked QF_LRA/Farkas artifact and route regression |

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

### Wave 3: Proof-Route Depth

Goal: make checked evidence normal for representative UNSAT rows.

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
| `discrete_math` | counting, generating functions, graph resources, finite actions | maintain pigeonhole and coefficient-convolution examples; add new rows only for distinct counting pressure | Bool/CNF, QF_LIA, finite replay |
| `graph_theory` | coloring, reachability, search runtime, matching, cuts, d-separation | keep one promoted representative per family; add asymptotic horizons only as proof targets | Bool/CNF, QF_BV, QF_LIA, finite replay |
| `number_theory` | gcd, modular arithmetic, residues, bounded Diophantine checks | group recurring divisibility and residue obstructions | QF_LIA/Diophantine, QF_BV |
| `linear_algebra` | exact matrices, vector spaces, duals, modules, tensors, spectral rows, active-set QP rows, SDP rows, descent-step rows, line-search rows, Wolfe line-search rows, projected-gradient rows, proximal-gradient rows | make matrix rows queryable by computation type and solver route | QF_LRA/Farkas, finite replay, QF_UF/Alethe |
| `abstract_algebra` | finite groups/rings/fields, homomorphisms, ideals, modules, tensors | add narrower rows only when multiple packs reuse them | QF_UF/Alethe, QF_BV, finite replay |
| `real_analysis` | bounded rational intervals, metric continuity, RCF shadows, calculus shadows, root-finding shadows, separation/KKT/active-set/SDP/gradient-descent/line-search/Wolfe/projected-gradient/proximal-gradient shadows | keep bounded shadows distinct from completeness/convergence/separation/KKT/active-set/SDP/descent/line-search/Wolfe/projected/proximal-gradient theorems | QF_LRA/Farkas, QF_NRA/RCF, Lean horizon |
| `complex_analysis` | real-pair algebra and transformations | complex algebra now has a checked bad norm-squared row; add only distinct real-pair arithmetic, polynomial-root, or algebraic-identity pressure | real-pair LRA/NRA, finite replay, Lean horizon |
| `topology` | finite topologies, compactness, connectedness, continuous maps, homology | standalone finite-topology lesson and checked missing-empty-set Bool/CNF row landed; add only distinct closure, metric-ball, preimage, or finite-set pressure | Bool/CNF, QF_UF/Alethe, QF_LIA, Lean horizon |
| `measure_theory` | finite measures, monotonicity/subadditivity, product measure, integration, random variables | finite measure/additivity, monotonicity/subadditivity, and finite product/integration bridge rows landed; promote only distinct convergence-horizon, countable-measure, or new measure-table pressure next | QF_LRA/Farkas, finite replay, Lean horizon |
| `probability_theory` | finite probability, kernels, Markov chains, martingales, hitting times, concentration | standalone finite probability mass-table lesson landed; keep table rows exact and route bad rows through LRA/LIA | QF_LRA/Farkas, QF_LIA, finite replay |
| `statistics` | descriptive stats, exact tests, regression, finite count tables | distinguish exact finite tests from numerical/statistical inference | QF_LIA, QF_LRA/Farkas, replay |
| `optimization_and_convexity` | LP/Farkas, convexity, least squares, Hessians, root-finding steps, separation rows, KKT rows, active-set QP rows, SDP rows, gradient-descent rows, line-search rows, Wolfe line-search rows, projected-gradient rows, proximal-gradient rows | LP objective/Farkas, rational convexity/gradient bridge rows, finite root-finding step replay, finite hyperplane-separation replay, finite KKT replay, finite active-set QP face/slack replay, finite SDP primal/dual replay, finite gradient-descent replay, finite Armijo line-search replay, finite Wolfe line-search replay, finite projected-gradient interval replay, and finite proximal-gradient replay landed; add only distinct duality, degenerate active-set variants, working-set pivots, higher-dimensional SDP, strong-Wolfe/nonconvex line-search, box-plus-L1, or stochastic/convergence pressure next | QF_LRA/Farkas, QF_NRA shadows |
| `numerical_analysis` | residuals, Euler steps, exact error recurrences, matrix algorithms, root-finding, active-set QP, gradient-descent, Armijo/Wolfe line-search, projected-gradient, and proximal-gradient iterations | keep finite replay and numerical-honesty rows distinct from promoted exact residual/error certificates | QF_LRA/Farkas, replay, Lean horizon |
| `differential_equations_and_dynamical_systems` | bounded recurrences and Euler traces | keep bounded-dynamics and finite-Euler checked rows source-linked; add only distinct transition, reachability, invariant, stochastic, or finite-error pressure | QF_LRA/Farkas, replay, Lean horizon |
| `geometry` | coordinate, incidence, rigid-configuration, affine, orientation/area, circle, inversion, and cyclic rational geometry | finite cyclic geometry now has checked bad diagonal-intersection replay; add only distinct circle-line correspondence, angle variants beyond the square witness, Ptolemy shadows, or higher-degree polynomial-geometry pressure | QF_LRA/Farkas, finite replay |
| `functional_analysis_and_operator_theory` | finite operators, inner products, Chebyshev systems | finite-operator now has a checked bad-bound row; add only distinct norm, recurrence, interpolation, or finite-dimensional operator pressure | QF_LRA/Farkas, replay, Lean horizon |

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
| `reals` | deepen | RCF shadow now has a source-linked QF_LRA/Farkas negative-discriminant row, root-finding has a source-linked bad-iterate row, separation has a source-linked bad-separator row, KKT has a source-linked bad-stationarity row, active-set QP has a source-linked bad-free-gradient row, SDP has a source-linked bad-objective row, gradient descent has a source-linked bad-decrease row, finite circle geometry has a source-linked bad-radius row, finite inversion geometry has a source-linked bad inverse-coordinate row, and finite cyclic geometry has a source-linked bad diagonal-intersection row; keep completeness, convergence, separation, KKT sufficiency, active-set method theory, SDP duality, descent-rate, general circle/inversion/cyclic geometry, and broad CAD/SOS/RCF claims horizon |
| `complex` | deepen | complex-plane bad unit-square real-part row now has a source-linked QF_LRA/Farkas regression; keep analytic theorems Lean-horizon |
| `divisibility-and-euclid` | maintain | use gcd/Bezout rows as arithmetic-certificate examples |
| `modular-arithmetic` | maintain | keep LIA nonunit and BV fixed-width residue routes distinct |
| `groups` | maintain | table replay plus Alethe equality conflicts |
| `rings` | maintain | BV fixed finite rings only when width is conceptually relevant |
| `fields` | maintain | finite fields plus linear-algebra links; arbitrary-field facts horizon |
| `polynomials` | deepen | polynomial identities now have a QF_LIA false-root regression; factorization has a QF_LRA/Farkas discriminant regression; root-finding has exact polynomial evaluation plus a QF_LRA/Farkas bad-step regression |
| `sequences-and-limits` | deepen | bounded Cauchy-tail and bounded monotone-prefix bad-bound rows now have QF_LRA/Farkas regressions; convergence theorems stay Lean horizon |
| `counting` | promote | pigeonhole CNF/LRAT and coefficient-count rows |
| `number-theory` | maintain | bounded residue and Diophantine families |
| `linear-algebra` | deepen | matrix corpus notes, dot-product/separator/KKT/active-set-QP/SDP/gradient-step/line-search/Wolfe/projected-gradient/proximal-gradient/circle-tangent/inversion rows, and route-specific regression back-links |
| `calculus` | deepen | one-variable false derivative, Riemann-sum false integral, multivariable bad-gradient, finite root-finding bad-step, finite KKT bad-stationarity, finite active-set QP bad-free-gradient, finite gradient-descent bad-decrease, finite line-search bad-Armijo, finite Wolfe bad-curvature, finite projected-gradient bad-projection, and finite proximal-gradient bad-proximal-point rows now have QF_LRA/Farkas regressions |

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
7. Landed: promote `sequence-limit-shadow-v0` through a source-linked bounded
   Cauchy-tail QF_LRA/Farkas artifact and route regression.
8. Landed: add `bounded-monotone-sequence-v0` with finite monotone-prefix,
   finite supremum, finite tail-gap replay, a checked bad upper-bound
   QF_LRA/Farkas artifact, and a monotone-convergence Lean-horizon row.
9. Landed: add `finite-recurrence-prefix-v0` with Fibonacci prefix replay,
   affine recurrence replay, companion-matrix state replay, a checked bad
   finite-value QF_LRA/Farkas artifact, and a recurrence-theory Lean-horizon
   row.
10. Landed: promote `multivariable-calculus-rational-v0` through a source-linked
   bad-gradient QF_LRA/Farkas artifact and route regression.
11. Landed: promote `calculus-algebraic-shadow-v0` through a source-linked
   false-derivative QF_LRA/Farkas artifact and route regression.
12. Landed: promote `complex-plane-transforms-v0` through a source-linked
   bad unit-square real-part QF_LRA/Farkas artifact and route regression.
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
   QF_LRA/Farkas bad subset-measure artifact, and a Lean-horizon row for
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
   posterior replay, checked QF_LRA/Farkas bad-normalization rejection, and
   checked bad-posterior rejection out of the broad finite-probability process
   bridge lesson.
36. Landed: add standalone finite-operator learner page, splitting exact
   finite-dimensional `l1` norm replay, row-sum operator-bound replay,
   Chebyshev recurrence replay, and checked QF_LRA/Farkas bad-bound evidence
   out of the broad bounded-dynamics/operator bridge lesson.
37. Landed: add standalone bounded-dynamics learner page, splitting exact
   recurrence trace replay, finite invariant checking, threshold reachability,
   and checked QF_LRA/Farkas bad invariant-bound evidence out of the combined
   finite dynamics/Euler bridge lesson.
38. Landed: add standalone finite-Euler learner page, splitting exact
   explicit-Euler transition replay, finite polynomial-solution error tables,
   monotone invariant checking, checked QF_LRA/Farkas bad-step evidence, and
   the ODE/numerical-analysis Lean horizon out of the combined finite
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
   a false incidence claim, a focused learner page, and a bridge-row update so
   geometry queries expose incidence as a first-class promoted pack.
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
   and the rational-convexity bridge.
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
   projected objective decrease, checked QF_LRA/Farkas rejection of a false
   projected point, a focused learner page, and concept links under reals,
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
    perpendicularity, chord-midpoint perpendicularity, checked QF_LRA/Farkas
    rejection of a false radius claim, a focused learner page, and concept links
    under reals, polynomials, linear algebra, and the shared coordinate-geometry
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
    dot-product replay, checked QF_LRA/Farkas rejection of a false
    diagonal-intersection claim, a focused learner page, and concept links
    under reals, polynomials, linear algebra, and the shared coordinate-geometry
    bridge.
62. Landed: add
    [`matrix-computation-index.md`](../learn/math/matrix-computation-index.md)
    as the route-oriented learner index for LU, rank/nullity, residual,
    projection, eigenpair, characteristic-polynomial, finite random-matrix,
    chain-complex, operator, module, and tensor rows. The index groups existing
    validated packs by replay, QF_LRA/Farkas, QF_UF/Alethe, QF_LIA/Diophantine,
    Lean-horizon, and numerical-honesty boundaries.
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
    as the first rules/law generated-query surface. The dashboard reads the
    committed rule-pack JSON and reports bounded sample rows plus generated
    coverage, equivalence, threshold, cap, version-delta, and monotonicity
    query-family counts.
67. Landed: add functional-analysis/operator field-readiness consumer query
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
    lookups, checked exact-rational statistics rows, and checked Diophantine
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
