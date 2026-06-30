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
- 44 bridge-concept rows.
- 5 example-family rows.
- 84 non-template math packs.
- 422 expected checks.
- 204 checked proof/evidence rows.
- 171 replay-only rows.
- 47 Lean-horizon rows.
- 84 promoted solver-reuse packs.
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

### Wave 1: Stabilize The Existing 84 Packs

Goal: every current non-template pack has a deliberate R5 disposition:
`promoted`, `non-benchmark-horizon`, or a clear reason to remain unclassified.

Current unclassified queue: empty.

Current non-benchmark queue: empty.

Last row closed:

| Pack | Upgrade Trigger |
|---|---|
| `bounded-dynamics-v0` | promoted through a bad invariant-bound row with a source-linked QF_LRA/Farkas artifact and route regression |

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
| QF_LRA/Farkas | rationals, matrices, LP, probability tables, geometry, dynamics | express exact rational conflict, emit/recheck Farkas certificate | source pack links artifact and learner page names trust boundary |
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
   slices with replayed witnesses plus checked Bool/QF_LIA proof fixtures.
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
| `linear_algebra` | exact matrices, vector spaces, duals, modules, tensors, spectral rows | make matrix rows queryable by computation type and solver route | QF_LRA/Farkas, finite replay, QF_UF/Alethe |
| `abstract_algebra` | finite groups/rings/fields, homomorphisms, ideals, modules, tensors | add narrower rows only when multiple packs reuse them | QF_UF/Alethe, QF_BV, finite replay |
| `real_analysis` | bounded rational intervals, metric continuity, RCF shadows, calculus shadows | keep bounded shadows distinct from completeness/convergence theorems | QF_LRA/Farkas, QF_NRA/RCF, Lean horizon |
| `complex_analysis` | real-pair algebra and transformations | complex algebra now has a checked bad norm-squared row; add only distinct real-pair arithmetic, polynomial-root, or algebraic-identity pressure | real-pair LRA/NRA, finite replay, Lean horizon |
| `topology` | finite topologies, compactness, connectedness, continuous maps, homology | standalone finite-topology lesson and checked missing-empty-set Bool/CNF row landed; add only distinct closure, metric-ball, preimage, or finite-set pressure | Bool/CNF, QF_UF/Alethe, QF_LIA, Lean horizon |
| `measure_theory` | finite measures, product measure, integration, random variables | standalone finite-measure lesson and bad-complement QF_LRA/Farkas row landed; promote only distinct finite-additivity, monotonicity, or measure-table pressure next | QF_LRA/Farkas, finite replay, Lean horizon |
| `probability_theory` | finite probability, kernels, Markov chains, martingales, hitting times, concentration | standalone finite probability mass-table lesson landed; keep table rows exact and route bad rows through LRA/LIA | QF_LRA/Farkas, QF_LIA, finite replay |
| `statistics` | descriptive stats, exact tests, regression, finite count tables | distinguish exact finite tests from numerical/statistical inference | QF_LIA, QF_LRA/Farkas, replay |
| `optimization_and_convexity` | LP/Farkas, convexity, least squares, Hessians | standalone LP/Farkas lesson landed; add only distinct duality, KKT, convexity, gradient, or Hessian pressure next | QF_LRA/Farkas, QF_NRA shadows |
| `numerical_analysis` | residuals, Euler steps, exact error recurrences, matrix algorithms | keep finite replay and numerical-honesty rows distinct from promoted exact residual/error certificates | QF_LRA/Farkas, replay, Lean horizon |
| `differential_equations_and_dynamical_systems` | bounded recurrences and Euler traces | keep bounded-dynamics and finite-Euler checked rows source-linked; add only distinct transition, reachability, invariant, stochastic, or finite-error pressure | QF_LRA/Farkas, replay, Lean horizon |
| `geometry` | coordinate, affine, orientation/area rational geometry | coordinate geometry now has a checked bad squared-distance row; add only distinct incidence, collinearity, midpoint, or rigid-configuration pressure | QF_LRA/Farkas, finite replay |
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
| `reals` | deepen | RCF shadow now has a source-linked QF_LRA/Farkas negative-discriminant row; keep completeness and broad CAD/SOS/RCF claims horizon |
| `complex` | deepen | complex-plane bad unit-square real-part row now has a source-linked QF_LRA/Farkas regression; keep analytic theorems Lean-horizon |
| `divisibility-and-euclid` | maintain | use gcd/Bezout rows as arithmetic-certificate examples |
| `modular-arithmetic` | maintain | keep LIA nonunit and BV fixed-width residue routes distinct |
| `groups` | maintain | table replay plus Alethe equality conflicts |
| `rings` | maintain | BV fixed finite rings only when width is conceptually relevant |
| `fields` | maintain | finite fields plus linear-algebra links; arbitrary-field facts horizon |
| `polynomials` | deepen | polynomial identities now have a QF_LIA false-root regression; factorization now has a QF_LRA/Farkas discriminant regression |
| `sequences-and-limits` | deepen | bounded Cauchy-tail no-counterexample now has a QF_LRA/Farkas regression; convergence theorem stays Lean horizon |
| `counting` | promote | pigeonhole CNF/LRAT and coefficient-count rows |
| `number-theory` | maintain | bounded residue and Diophantine families |
| `linear-algebra` | deepen | matrix corpus notes and route-specific regression back-links |
| `calculus` | deepen | one-variable false derivative, Riemann-sum false integral, and multivariable bad-gradient rows now have QF_LRA/Farkas regressions |

## Commit-Sized Queue

Pick one row per commit unless the change is purely navigational.

1. Landed: promote the `proof-methods-refutation-v0` and `counting-v0`
   `PHP(3,2)` rows through source-linked DIMACS plus DRAT/LRAT regression.
2. Landed: classify `bounded-dynamics-v0`, `complex-algebraic-v0`,
   `coordinate-geometry-v0`, `finite-measure-v0`, `finite-operator-v0`, and
   initially `finite-topology-v0` as explicit non-benchmark educational rows
   until they gain negative, certificate-bearing examples. Finite topology has
   since been promoted by item 17.
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
8. Landed: promote `multivariable-calculus-rational-v0` through a source-linked
   bad-gradient QF_LRA/Farkas artifact and route regression.
9. Landed: promote `calculus-algebraic-shadow-v0` through a source-linked
   false-derivative QF_LRA/Farkas artifact and route regression.
10. Landed: promote `complex-plane-transforms-v0` through a source-linked
   bad unit-square real-part QF_LRA/Farkas artifact and route regression.
11. Landed: promote `induction-obligations-v0` through a source-linked bounded
   bad-step count QF_LIA arithmetic-DPLL artifact and route regression.
12. Landed: promote `cardinality-principles-v0` through a source-linked
   overlap-additivity count QF_LIA/Diophantine artifact and route regression.
13. Landed: promote `polynomial-factorization-rational-v0` through a
   source-linked irreducible-quadratic discriminant QF_LRA/Farkas artifact and
   route regression.
14. Landed: promote `reals-rcf-shadow-v0` through a source-linked
   negative-discriminant QF_LRA/Farkas artifact and route regression, closing
   the current unclassified solver-reuse queue.
15. Landed: promote `finite-measure-v0` through a source-linked bad complement
   QF_LRA/Farkas artifact and route regression.
16. Promote or classify any newly added unclassified packs, starting with compact
   source-level conflicts where the route is clear.
17. Landed: promote `finite-topology-v0` through a source-linked
   missing-empty-set Bool/CNF DIMACS artifact and DRAT/LRAT route regression.
18. Landed: promote `coordinate-geometry-v0` through a source-linked bad
   squared-distance QF_LRA/Farkas artifact and route regression.
19. Landed: promote `finite-operator-v0` through a source-linked bad
   operator-bound QF_LRA/Farkas artifact and route regression.
20. Landed: promote `complex-algebraic-v0` through a source-linked bad
   norm-squared QF_LRA/Farkas artifact and route regression.
21. Landed: promote `bounded-dynamics-v0` through a source-linked bad
   invariant-bound QF_LRA/Farkas artifact and route regression, closing the
   explicit non-benchmark-horizon queue.
22. Landed: add `proof-object-anatomy-end-to-end.md`, following
   `proof-methods-refutation-v0` from the PHP(3,2) source claim through
   committed CNF, emitted DRAT/LRAT proof objects, and same-artifact
   corrupted-proof rejection.
23. Landed: add `farkas-certificate-anatomy-end-to-end.md`, following
   `linear-optimization-v0` from the exact LP threshold conflict through source
   SMT-LIB, emitted `UnsatFarkas` evidence, and same-artifact multiplier tamper
   rejection.
24. Landed: add `alethe-certificate-anatomy-end-to-end.md`, following
   `equivalence-classes-v0` from the quotient-map congruence conflict through
   source SMT-LIB, emitted zero-trust `UnsatAletheProof` evidence, and
   same-artifact truncated-proof rejection.
25. Landed: add `diophantine-certificate-anatomy-end-to-end.md`, following
   `modular-arithmetic-v0` from the nonunit modular-inverse obstruction through
   source SMT-LIB, emitted `UnsatDiophantine` evidence, and same-artifact
   contradiction-row tamper rejection.
26. Landed: add `qf-bv-bitblast-certificate-anatomy-end-to-end.md`, following
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
   atlas now validates 44 bridge rows while keeping Banach, Hilbert,
   compact-operator, minimax, and infinite-dimensional approximation theorem
   coverage in the Lean-horizon lane.

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
