# Math Curriculum Resource Implementation Matrix

## Purpose

This is the build matrix for turning the formal math curriculum into a durable
resource system. It complements the phase/history plan in
[MATH-CURRICULUM-BUILDOUT.md](MATH-CURRICULUM-BUILDOUT.md) and the forward
execution plan in
[CURRICULUM-RESOURCE-EXECUTION-PLAN.md](CURRICULUM-RESOURCE-EXECUTION-PLAN.md).
The top-down curriculum-wide sequencing plan is
[MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md](MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md).
The current execution ledger for choosing the next pack-level increment is
[MATH-CURRICULUM-DETAILED-BUILD-PLAN.md](MATH-CURRICULUM-DETAILED-BUILD-PLAN.md).
The broader resource-family operating plan is
[RESOURCE-BUILDOUT-ROADMAP.md](RESOURCE-BUILDOUT-ROADMAP.md).

The invariant is:

```text
curriculum node -> concept row -> example pack -> learner page -> proof route -> solver feedback -> consumer boundary
```

The build order should stay top-down, but each commit should be narrow: one
concept row group, one example pack, one proof upgrade, one learner lesson, or
one generated dashboard change.

## Resource Acceptance Gates

| Gate | What Exists | Required Check |
|---|---|---|
| R0 source anchor | curriculum node or field row | appears in `curriculum.toml` or `MATH-FIELDS.md` |
| R1 concept row | atlas row with fields, prerequisites, fragments, gaps | `python3 scripts/validate-foundational-concepts.py` |
| R2 example pack | `README.md`, `metadata.json`, `model.md`, `checks.md`, `expected.json` | `python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>` plus `python3 scripts/check-foundational-negative-fixtures.py` for committed invalid schema fixtures |
| R3 learner path | focused lesson or named cluster page | `./scripts/check-links.sh` plus generated learner dashboard |
| R4 checked evidence | replay, DRAT/LRAT, Farkas, Alethe, QF_BV DRAT, or Lean horizon | route-specific cargo test plus pack validator |
| R5 solver reuse | regression, fuzz seed, benchmark slice, or explicit non-benchmark horizon | back-link from test/corpus metadata to resource pack |
| R6 consumer boundary | schema/API/data consumer | `python3 scripts/consume-foundational-resources.py` |

Do not promote a row past the gate it actually satisfies. A finite checked
example is useful at R2/R3; it is not a general theorem until an R4 proof route
or Lean reconstruction supports that scope.

## Build Units

Every new or upgraded resource should answer these questions before it lands:

- Audience: learner, solver contributor, proof contributor, educator, consumer,
  or several of these.
- Mathematical claim: exact finite claim, bounded shadow, computable witness, or
  proof-horizon theorem.
- Encoding: Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, arrays, finite replay, or
  Lean horizon.
- Evidence: SAT witness replay, UNSAT certificate, checked algebraic
  computation, explicit gap, or `unknown` with reason.
- Trust boundary: what is untrusted search/encoding and what is independently
  checked.
- Graduation: concrete command or proof-route target that moves the resource to
  the next gate.

## Curriculum Node Matrix

| Curriculum Node | Current Resource Surface | Next Build Work | Proof / Evidence Route | Graduation Signal |
|---|---|---|---|---|
| `propositional-logic` | `logic-basics-v0`, Boolean learner path | Add proof-object walkthrough for CNF refutation anatomy. | Boolean CNF/LRAT or DRAT; model replay for SAT rows. | Corrupted certificate test fails; lesson names encoder-vs-checker boundary. |
| `predicate-logic` | `finite-predicate-v0` | Add bridge concept rows for finite quantifier expansion and countermodel replay. | Finite expansion plus QF_UF/Alethe for equality-heavy fragments. | Pack rows distinguish finite-domain validity from first-order validity. |
| `proof-methods` | `proof-methods-refutation-v0`, `proof-methods-patterns-v0` | Turn direct/contrapositive/cases/contradiction into reusable proof-pattern rows. | CNF/LRAT for refutation examples; Lean horizon for natural deduction. | Learner page can trace proof method -> solver query -> checked evidence. |
| `induction` | `induction-obligations-v0`, `induction-patterns-v0` | Split bounded base/step checks from induction-schema reconstruction targets. | QF_LIA for finite obstructions; Lean horizon for general induction. | No pack claims full induction from bounded prefixes. |
| `sets` | finite sets, lattices, cardinality/topology packs | Add concept rows for Boolean algebra, finite lattice laws, compactness shadows, and counterexample replay. | CNF/LRAT for Boolean refutations including finite open-cover misses; QF_UF/Alethe for lattice/order conflicts. | Every false set/lattice/topology identity has either evidence or an explicit route gap. |
| `relations-and-functions` | relation/function, equivalence, composition, monoid, permutation, action packs | Landed bridge rows for quotient maps, finite group actions, finite partition/relation roundtrips, and image/preimage/inverse tables. | QF_UF/Alethe for function consistency and congruence conflicts. | Equality-heavy rows use checked Alethe where available. |
| `cardinality` | finite cardinality and cardinality-principles packs | Landed bridge rows for finite Boolean algebra, finite bijection/cardinality, powerset cardinality, and infinite cardinality theorem horizons. | finite replay/CNF for bounded no-map rows; Lean horizon for Cantor/infinite facts. | Infinite claims are never benchmarked as finite checks. |
| `naturals` | `natural-arithmetic-v0` | Landed totality-convention bridge row; add narrower Peano-shadow or BV-vs-LIA rows only when reused across packs. | Bounded replay, QF_LIA, QF_BV where fixed width is educationally relevant. | Width, operation conventions, and finite prefix limits are visible in metadata and lesson text. |
| `integers` | `integer-lia-v0` | Promote common linear-obstruction patterns into shared Diophantine examples. | QF_LIA/Diophantine. | Bad linear rows carry checked integer evidence or a named missing route. |
| `rationals` | `rationals-lra-v0`, rational polynomial pack | Landed exact-vs-floating arithmetic bridge row; split density/order further only when learner pages need it. | QF_LRA/Farkas for impossible rational inequalities. | Farkas-backed rows recheck independently of solver search, and exact rational rows do not imply floating-point claims. |
| `reals` | RCF shadow, bounded real analysis, metric continuity, finite root finding, finite separation, finite KKT, finite active-set QP, finite SDP, finite gradient descent, finite line search, finite Wolfe line search, finite projected gradient, finite proximal gradient, finite circle, inversion, and cyclic geometry | Add concept rows for balls, limits, continuity, compactness, root-finding, separation, KKT, active-set QP, SDP, gradient descent, line search, Wolfe line search, projected gradient, proximal gradient, finite circle/inversion/cyclic geometry, and completeness/convergence/geometry-theorem horizons. | QF_LRA/Farkas for bounded bad-delta, bad-iterate, bad-separator, bad-stationarity, bad-complementarity, bad-free-gradient, bad-inactive-slack, bad-objective, bad-duality-gap, bad-slack-entry, bad-decrease, bad-descent-bound, bad-Armijo, bad descent-direction, bad accepted-candidate, bad-Wolfe-minimizer, bad-Wolfe-curvature, bad-projection, bad-projected-decrease, bad-proximal-point, bad-composite-decrease, bad-box-proximal-point, bad-radius, bad-line-intersection, bad-inverse-coordinate, bad-diagonal-intersection, bad-opposite-angle, and bad-Ptolemy rows, QF_LRA/NRA for algebraic shadows; Lean horizon for completeness/general topology, separation, KKT sufficiency, active-set method theory, SDP duality, descent-rate, Wolfe/line-search/projected/proximal-gradient convergence, circle/inversion/cyclic geometry, and convergence. | Each epsilon-delta/root-finding/separation/KKT/active-set/SDP/descent/line-search/Wolfe/projected/proximal-gradient/circle/inversion/cyclic pack says fixed rational instance vs theorem, and metric-continuity, finite-root-finding, finite-separation, finite-KKT, finite-active-set-QP, finite-SDP, finite-gradient-descent, finite-line-search, finite-wolfe-line-search, finite-projected-gradient, finite-proximal-gradient, finite-circle-geometry, finite-inversion-geometry, plus finite-cyclic-geometry now have checked finite bad-row routes. |
| `complex` | complex algebraic and transform packs | Add real-pair encoding note and analytic-horizon rows. | NRA/LRA real-pair replay; Lean horizon for holomorphic theory. | Algebraic complex checks avoid claiming analytic coverage. |
| `divisibility-and-euclid` | `gcd-bezout-v0` | Landed reusable gcd/divisibility witness bridge row for number-theory and algebra packs. | Computed witness replay; QF_LIA/Diophantine for divisibility obstructions. | Bezout rows validate both gcd and coefficient identity, and gcd obstruction rows carry checked evidence where promoted. |
| `modular-arithmetic` | modular arithmetic and finite ideals | Landed modular CRT/inverse bridge row, checked nonunit inverse and incompatible non-coprime CRT Diophantine rows, checked fixed-width nonunit-inverse and Fermat-unit QF_BV rows, and adjacent quotient/ideal bridge rows; add narrower quotient-ring rows only when reuse demands them. | QF_LIA/Diophantine, QF_UF/Alethe quotient congruence, and QF_BV fixed-width finite residues. | Nonunit inverse, incompatible CRT, and Fermat-unit rows carry checked arithmetic evidence; quotient rows distinguish table replay from representative congruence. |
| `groups` | finite groups, monoids, permutations, actions, homomorphisms | Landed bridge rows for homomorphism preservation, kernel/image replay, quotient maps, and finite group actions; orbit-stabilizer and Burnside can split later if reused broadly. | QF_UF/Alethe for table congruence and action-law conflicts. | Table checks keep associativity/action-law replay explicit. |
| `rings` | finite rings, ideals, modules, homomorphisms | Maintain the landed bad distributivity and bad multiplicative-identity BV routes; add more finite ring-table contradictions only when they introduce distinct fixed-width pressure. | QF_BV bit-blast/DRAT plus QF_UF/Alethe for homomorphism preservation and quotient representative congruence. | Unsat finite-ring rows carry checked CNF or Alethe evidence without overclaiming Lean. |
| `fields` | finite fields, vector/dual/tensor packs | Maintain the landed composite no-inverse and bad inverse-candidate BV routes; add more fixed finite-field contradictions only when they introduce distinct inverse, distributivity, or table pressure. | QF_BV for finite fields; QF_UF/Alethe for table equality conflicts. | Composite-modulus non-field and bad inverse-candidate contrasts have checked routes. |
| `polynomials` | identities, rational factorization, generating functions, finite root finding, finite circle/inversion/cyclic geometry | Add coefficient-ring, polynomial-division, finite root-finding, and finite polynomial-geometry reusable rows. | Finite replay, QF_LIA/LRA coefficient constraints, QF_LRA/Farkas for linearized exact conflicts, Lean horizon for general factorization, circle/inversion/cyclic geometry, and convergence. | Factorization, root-finding, circle, inversion, and cyclic rows replay product, degree/leading constraints, polynomial values, exact iterates, bisection widths, squared radii, tangent lines, chord dot products, inverse images, distance products, diagonal midpoints, angle dot products, and Ptolemy product sums. |
| `sequences-and-limits` | sequence-limit shadow, bounded monotone sequence, finite recurrence prefix, real-analysis, generating functions | Bounded Cauchy-tail, monotone-prefix bad-bound, finite recurrence bad-value, and bad affine-step rows landed; add broader convergence-horizon rows only when reused. | Finite replay/LRA for bounded tails and recurrence prefixes; Lean horizon for general convergence and recurrence theory. | Lessons keep finite prefix evidence separate from convergence and closed-form/asymptotic theorems. |
| `counting` | counting, permutations, actions, generating functions | Landed finite-counting replay bridge for permutation/Pascal rows, pigeonhole, double counting, coefficient extraction, finite orbit counts, and exact tail counts; add narrower asymptotic or recurrence-horizon rows only when reused. | CNF/LRAT for pigeonhole; QF_LIA/Diophantine for finite count contradictions; finite replay for enumerative witnesses. | Count rows include deterministic universe, enumeration, route artifact, and theorem-horizon boundary. |
| `number-theory` | number theory, modular, gcd, integer LIA | Maintain the landed bounded Diophantine witness/obstruction pair and residue proof-route comparisons; add new families only when they introduce distinct BV/LIA pressure. | QF_LIA/Diophantine; QF_BV for fixed modulus; Lean horizon for deep theorems. | Each row identifies bounded search vs number-theory theorem. |
| `linear-algebra` | rational matrices, finite vector/dual/module/tensor, spectral, invariants, separation, KKT, active-set QP, SDP, gradient descent, line search, Wolfe line search, projected gradient, proximal gradient, circle tangent/chord checks, inversion vector checks, cyclic diagonal/angle/Ptolemy checks | Landed matrix-computation bridge rows plus algebra-map rows for LU replay with checked bad product-entry evidence, nullspace replay with checked bad component evidence, kernel/image, quotient maps, module actions, tensor bilinearity, inner-product projection-orthogonality replay, separating-hyperplane replay, KKT stationarity/complementarity replay, finite active-face stationarity/slack replay with checked inactive-slack evidence, finite SDP slack/objective replay, finite gradient-step replay, finite Armijo/Wolfe line-search replay, finite projected-gradient interval/decrease replay, finite proximal-gradient soft-threshold/composite-decrease and box-plus-L1 replay, finite circle tangent/chord dot-product replay, finite inversion scalar-vector/determinant replay, and finite cyclic diagonal/angle/Ptolemy replay; next split dual/projection maps only when reuse demands it. | QF_LRA/Farkas, finite-field replay, QF_UF/Alethe for algebraic table conflicts. | Matrix, LU product-entry, nullspace-component, dot-product, projection-orthogonality, stationarity, complementarity, active-set QP, SDP objective, descent-step, line-search, Wolfe-line-search, projected-gradient, proximal-gradient, finite circle, finite inversion, and finite cyclic rows can become solver regressions with source-pack back-links. |
| `calculus` | algebraic calculus, Riemann sums, multivariable rational calculus, finite root finding, finite active-set QP, finite line search, finite Wolfe line search, finite projected gradient, finite proximal gradient | Add derivative/integral/convergence theorem horizon rows plus exact algebraic and algorithm-step shadows. | LRA/NRA for polynomial shadows; Lean horizon for FTC, differentiability, active-set/Wolfe/line-search/projected/proximal-gradient convergence, and convergence. | Calculus packs never conflate finite symbolic or iterative replay with analytic theorem proof. |

## Field Extension Matrix

| Field | Curriculum Anchor | Build Next | Solver / Proof Pressure |
|---|---|---|---|
| `logic_and_proof` | foundations layer | proof-object lessons and proof-pattern atlas rows | CNF/LRAT, Alethe, Lean reconstruction |
| `set_theory_and_foundations` | sets, relations, cardinality | quotients, lattices, finite/infinite boundary rows | QF_UF/Alethe, finite replay, Lean horizon |
| `discrete_math` | counting, relations | graph search, matching, cuts, generating functions, asymptotic horizons | SAT/CNF, finite replay, Lean horizon |
| `graph_theory` | sets, relations, counting | maintain landed finite graph replay/obstruction bridge across coloring, reachability, search runtime, matching, cuts, and d-separation; add theorem/asymptotic rows only when reused | SAT/CNF, QF_BV for fixed color encodings, BV/LIA counters, model replay |
| `number_theory` | divisibility, modular, fields | bounded Diophantine and residue-family packs | QF_LIA, QF_BV |
| `linear_algebra` | fields, polynomials, relations | LU with checked bad product-entry evidence, rank/nullity, residual, spectral, tensor and module rows | QF_LRA/Farkas, finite-field replay |
| `abstract_algebra` | groups, rings, fields | homomorphisms, ideals, quotients, modules, tensor products | QF_UF/Alethe, QF_BV |
| `real_analysis` | rationals, reals, sequences, calculus | balls, bounded epsilon-delta, compactness/continuity horizons | QF_LRA/Farkas, QF_LRA/NRA, Lean horizon |
| `complex_analysis` | complex, reals, polynomials | real-pair algebra now; analytic rows later | NRA/LRA, Lean horizon |
| `topology` | sets, reals, linear algebra | landed finite topology/compactness/connectedness/preimage bridge rows plus finite topology-operator/homeomorphism, finite specialization-order, finite boundary-operator, finite chain-complex/homology, finite torsion-homology, finite cohomology, and finite cup-product replay bridges; add only distinct quotient, universal-coefficient, cohomology-ring quotienting, or theorem-invariance pressure | finite replay, QF_UF/Alethe, QF_LIA/LRA, QF_BV, Lean horizon |
| `measure_theory` | sets, probability, reals | landed finite measure/additivity, monotonicity/subadditivity, and finite product/integration bridge rows; add narrower countable-measure or convergence rows only when reused | finite replay, QF_LRA, Lean horizon |
| `probability_theory` | counting, rationals, measure | probability tables, kernels, Markov chains, hitting times, concentration | QF_LRA, QF_LIA counts, replay |
| `statistics` | probability, linear algebra | exact tests, regression, finite sampling tables, numerical-honesty rows | QF_LRA, QF_LIA, replay |
| `optimization_and_convexity` | rationals, reals, linear algebra | landed LP objective/Farkas, rational convexity/gradient bridge rows with checked bad midpoint and affine-threshold evidence, finite root-finding step and bisection-width replay, finite hyperplane-separation replay, finite KKT replay with checked stationarity/complementarity evidence, finite active-set QP face/slack replay with checked inactive-slack evidence, finite degenerate active-bound replay, finite SDP replay, finite gradient-descent replay with checked descent-bound evidence, finite Armijo line-search rejected-step, descent-direction, and accepted-candidate replay, finite Wolfe line-search replay, finite projected-gradient interval/decrease replay, finite proximal-gradient soft-threshold/composite-decrease replay, and finite box-plus-L1 proximal replay; add narrower duality, working-set pivots, higher-dimensional SDP, group-lasso/active-set proximal, strong-Wolfe/nonconvex line-search, or stochastic/convergence rows only when reused | QF_LRA/Farkas, NRA shadows |
| `numerical_analysis` | linear algebra, calculus | maintain landed finite dynamics/Euler bridge alongside residual bounds, interval boxes, exact error recurrences, root-finding, active-set QP, gradient-descent, Armijo/Wolfe line-search descent-direction and accepted-candidate arithmetic, projected-gradient, and proximal-gradient composite-decrease iterations | QF_LRA, replay, numerical-honesty metadata |
| `differential_equations_and_dynamical_systems` | calculus, linear algebra | maintain landed finite dynamics/Euler bridge for bounded recurrences, Euler traces, invariant checks, threshold reachability, checked bad threshold-step rows, and finite error tables | QF_LRA, BV/LIA counters, Lean horizon |
| `geometry` | reals, polynomials, linear algebra | landed coordinate/incidence/rigid/affine/oriented replay plus finite circle/inversion/cyclic replay bridge rows; add only distinct nontrivial circle-line correspondence, higher-degree polynomial-geometry, or theorem-reconstruction pressure beyond the current area-scaling, circle-line, square angle-dot, and Ptolemy rows when reused | QF_LRA/NRA, replay |
| `functional_analysis_and_operator_theory` | linear algebra, real analysis | finite operators, inner products, Chebyshev-system slices | QF_LRA, finite replay, Lean horizon |

## Route-Specific Build Plan

### Boolean CNF/LRAT

Use for finite Boolean refutations: graph coloring, pigeonhole, set identities,
proof-by-contradiction examples.

Build sequence:

1. Commit small deterministic DIMACS artifacts.
2. Add a cargo regression that produces DRAT/LRAT and checks it.
3. Link the proof artifact or generator from `expected.json`.
4. Update the learner page to explain that the encoder is trusted separately
   from the proof checker.

### QF_BV Bit-Blast

Use for fixed-width finite algebra and residue examples where the width is part
of the educational claim.

Build sequence:

1. Add SMT-LIB or generated BV artifacts under the pack.
2. Add model replay for SAT rows against the source finite object.
3. Add DRAT-backed CNF proof checks for UNSAT rows.
4. Keep bit-blast/Tseitin lowering in the trust ledger until Lean
   reconstruction covers the original formula.

### QF_LIA / Diophantine

Use for integer equalities, modular obstructions, counts, rank coefficients, and
finite statistical tail counts.

Build sequence:

1. Encode the impossible integer relation as a tiny SMT-LIB or test fixture.
2. Check the obstruction through the arithmetic proof route.
3. Add a pack row that names the witness or obstruction, not just `unsat`.
4. Promote recurring patterns into reusable cookbook examples.

### QF_LRA / Farkas

Use for rational infeasibility: linear systems, LP thresholds, probability
normalization, expected-time equations, residual bounds, and affine geometry.

Build sequence:

1. Express the row as exact rational constraints.
2. Produce and recheck a Farkas certificate.
3. Link the certificate route from the pack metadata and learner page.
4. Reuse the row as a solver regression only after replay is deterministic.

### QF_UF / Alethe

Use for equality-heavy finite structures: functions, quotient maps,
homomorphisms, monoids, modules, ideals, tensor maps, and action laws.

Build sequence:

1. Encode the equality conflict as a small congruence problem.
2. Export an Alethe proof and check it with the available checker.
3. Keep finite table replay for the mathematical object itself.
4. Add Lean reconstruction only when the Alethe-to-Lean route covers the shape.

### Lean Horizon

Use for general theorems: induction schemas, completeness, compactness, general
algebra, measure convergence, asymptotics, Hilbert/Banach-space theorems, and
analytic complex analysis.

Build sequence:

1. Add a concept row that states the theorem shape and prerequisite resources.
2. Add finite shadows only as examples, not as theorem evidence.
3. Name the missing Lean dependencies in `expected.json` or pack metadata.
4. Promote only after kernel-checked reconstruction lands.

## Commit-Sized Execution Queue

1. R1 bridge-concept rows landed for finite replay, bounded theorem shadows,
   counterexample proof, Lean horizon, and the first analysis/topology boundary
   terms: metric balls, bounded epsilon-delta shadows, compactness shadows,
   connectedness shadows, and continuity-by-preimage. Keep future bridge rows
   narrow and generated from `scripts/gen-foundational-concepts.py`.
2. R1 bridge-concept rows landed for linear-algebra computation vocabulary:
   LU replay, rank/nullity replay, residual bounds, Rayleigh/eigenpair witnesses,
   characteristic-polynomial replay with checked trace-invariant evidence, and
   finite random-matrix moments.
3. R1 bridge-concept rows landed for algebra-map vocabulary: homomorphism
   preservation, kernel/image replay, quotient maps, ideal closure, module
   actions, tensor bilinearity, and finite group actions.
4. R1 bridge-concept rows landed for probability/statistics finite-table
   vocabulary, measure-theory finite additivity/product/integration
   vocabulary, optimization/convexity LP objective and convexity-shadow
   vocabulary, proof/logic vocabulary, proof-object anatomy vocabulary, and
   set/foundations vocabulary, including finite Boolean algebra,
   partition/relation roundtrips, image/preimage/inverse tables, finite
   bijection/cardinality, and cardinality theorem horizons. R1 bridge-concept
   rows now also land for coordinate/incidence/rigid/oriented geometry replay,
   finite circle/inversion/cyclic geometry replay, and complex real-pair
   transform replay, plus finite inner-product/projection and finite
   operator/Chebyshev replay, keeping those field-specific finite shadows
   queryable without overstating synthetic, differential, analytic, Lebesgue,
   optimization duality, KKT, SDP, convergence, Banach, Hilbert,
   compact-operator, minimax, or
   infinite-dimensional theorem coverage.
5. Landed: add "math example using this route" sections to the six active
   proof cookbook recipes.
6. Continue learner audit so every non-template pack appears in a focused
   lesson or a named combined lesson; standalone finite topology and finite
   measure pages now split those first-principles stories from the combined
   topology/measure bridge, and standalone linear optimization now splits the
   LP/Farkas story from the combined linear-system/LP bridge. Standalone
   finite probability mass tables now split the PMF/conditioning/Bayes story
   from the broader finite-probability process bridge. Standalone finite
   operators now split the norm/operator-bound/Chebyshev-prefix story from the broad
   bounded-dynamics/operator bridge. Standalone bounded dynamics now splits
   recurrence traces, finite invariants, and threshold reachability from the
   finite dynamics/Euler bridge, including checked bad transition-step, bad
   threshold-step, and bad invariant-bound rows. Standalone finite Euler now splits
   explicit-Euler transition replay, finite error tables, and bad-step
   evidence from the same bridge.
7. Recurring fixed-width finite algebra, residue, and one-bit graph
   obstructions now have the `family_fixed_width_bv_drat` example-family row,
   backed by the shared `math_resource_bv_routes` regression across finite
   fields, finite rings, graph coloring, modular arithmetic, and bounded
   number-theory residue search/bad-witness packs. Continue QF_BV promotions
   only when fixed width is part of the educational claim.
8. First route-specific proof-upgrade note pass landed on the highest-use
   learner pages: logic/proof, graph/discrete, linear algebra/optimization,
   probability/statistics, and algebra/number theory.
9. Recurring finite algebra equality conflicts now have the
   `family_finite_algebra_alethe` example-family row, backed by the shared
   `math_resource_uf_routes` regression.
10. Recurring exact-rational infeasibility conflicts now have the
   `family_exact_rational_farkas` example-family row, backed by the shared
   `math_resource_lra_routes` regression.
11. Recurring finite Boolean refutations now have the
   `family_boolean_cnf_lrat` example-family row, backed by the shared
   `math_resource_boolean_routes` regression across logic, counting, graph,
   finite-set, and finite-topology packs.
12. Recurring integer/count obstructions now have the
   `family_integer_diophantine` example-family row, backed by the shared
   `math_resource_lia_routes` regression across number theory, induction,
   counting, statistics, graph-search, polynomial, and homology packs.
13. Generated dashboard columns for R0-R6 gate level and "next gate" now land
   in the coverage, field, proof-gap, and learner/proof-upgrade dashboards;
   the curriculum-status audit now separates source curriculum status from
   generated resource maturity.
14. The first deterministic `solver_reuse` batch is now fully promoted; no pack
   remains tagged `candidate` in that initial batch.
15. Consumer-facing sample queries now land through
   `scripts/query-foundational-resources.py` and
   [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md): summary counts, pack discovery,
   field-plus-proof-route discovery, checked-row mining, solver-reuse rows,
   atlas concept lookup, and field-level curriculum readiness over the
   committed JSON data contract. The smoke set now covers logic/Boolean,
   set-theory/Alethe, discrete-math/Diophantine, probability/Farkas,
   dynamics/Farkas, topology/Boolean+Alethe, measure/Farkas,
   statistics/Farkas+Diophantine, linear-algebra/Farkas+Alethe,
   abstract-algebra/Alethe+QF_BV, number-theory/Diophantine,
   graph-theory/Boolean, real-analysis/Farkas, numerical-analysis/Farkas,
   complex-analysis/Farkas, optimization/Farkas, geometry/Farkas, and
   functional-analysis/operator Farkas field-readiness examples, plus topology
   compactness/preimage bridge lookups, proof-vocabulary lookup, partition
   bridge lookup, discrete finite-family lookup, probability bridge lookup,
   measure bridge concept lookup,
   statistics finite-table/tail-count bridge lookups, linear-algebra
   rank/projection bridge lookups, abstract-algebra homomorphism/ideal bridge
   lookups, number-theory finite-family lookup, graph-family lookup,
   real-analysis epsilon/gradient bridge lookups, numerical-analysis
   residual/operator bridge lookups, complex-analysis real-pair bridge lookup,
   LP-objective and convexity bridge concept lookup, operator bridge concept
   lookup, checked topology Boolean/Alethe rows, checked measure-theory Farkas
   rows, checked statistics Farkas/Diophantine rows, checked linear-algebra
   Farkas/Alethe rows, checked abstract-algebra Alethe/QF_BV rows, checked
   number-theory Diophantine rows, checked graph-theory Boolean rows, checked
   real-analysis Farkas rows, checked numerical-analysis Farkas rows, checked
   complex-analysis Farkas rows, checked logic/proof Boolean rows, checked
   set-theory/foundations Alethe rows, checked discrete-math Diophantine rows,
   checked probability-theory Farkas rows, checked optimization/convexity
   Farkas rows, checked geometry Farkas rows, and checked
   functional-analysis/operator Farkas rows.
16. Negative example-pack validator fixtures now land through
    `scripts/check-foundational-negative-fixtures.py` and
    `artifacts/fixtures/foundational-example-pack-invalid/`, covering unknown
    fields, metadata/check id drift, and missing witness references.
17. Rules/law transfer now lands through
   [RULES-LAW-CROSSWALK.md](RULES-LAW-CROSSWALK.md): finite predicates,
   arithmetic thresholds, graph reachability, precedence, and proof routes are
   mapped to concrete policy/rule checks before new rule packs are added.
   `benefit-eligibility-v0` now has checked Bool/QF_LIA fixtures for
   consistency, coverage, fixed no-exception monotonicity, and active-threshold
   implementation equivalence through `rules_as_code_examples`.
   `authorization-policy-v0` now adds the access-control slice with checked
   Bool/QF_LIA fixtures for tenant isolation, explicit deny precedence, admin
   tenant guarding, and bounded implementation equivalence.
   `tax-benefit-arithmetic-v0` now adds the threshold/cap/phase-out slice with
   checked Bool/QF_LIA fixtures for non-negative benefit, cap, active phase-out
   monotonicity, and bounded implementation equivalence.
18. First solver-reuse promotions landed: `logic-basics-v0` now links
    `tiny-cnf-refutation` to a DIMACS artifact, `finite-cardinality-v0` links
    `no-injection-four-to-three` to a DIMACS artifact, and
    `graph-matching-v0` links `triangle-no-perfect-matching` to a DIMACS
    artifact. `graph-reachability-v0` now links `disconnected-no-path` to a
    bounded reachability fixed-point DIMACS artifact, and `graph-cut-v0` links
    `one-edge-cut-rejected` to a bounded post-removal reachability DIMACS
    artifact. `graph-d-separation-v0` now links `chain-conditioned-blocks` to
    a conditioned non-collider blocking DIMACS artifact. These Boolean rows are
    checked by the `math_resource_boolean_routes` DRAT/LRAT regression.
    `graph-search-runtime-v0` now links `bad-dfs-cost-bound-rejected` to
    `artifacts/examples/math/graph-search-runtime-v0/smt2/bad-dfs-cost-bound-lia-conflict.smt2`,
    checked by the `math_resource_lia_routes` arithmetic-DPLL regression.
    `integer-lia-v0` now links `diophantine-gcd-obstruction` to
    `artifacts/examples/math/integer-lia-v0/smt2/diophantine-gcd-obstruction-conflict.smt2`,
    checked by the `math_resource_lia_routes` Diophantine regression.
    `number-theory-v0` now links `diophantine-gcd-obstruction-qf-lia` to
    `artifacts/examples/math/number-theory-v0/smt2/diophantine-gcd-obstruction-conflict.smt2`,
    checked by the `math_resource_lia_routes` Diophantine regression.
    `natural-arithmetic-v0` now links `bounded-natural-negative-rejected` to
    `artifacts/examples/math/natural-arithmetic-v0/smt2/bounded-natural-negative-lia-conflict.smt2`,
    checked by the `math_resource_lia_routes` arithmetic-DPLL regression.
    `number-theory-v0` now links `quadratic-nonresidue-qf-bv-drat` to
    `artifacts/examples/math/number-theory-v0/smt2/quadratic-nonresidue-mod7-bitblast-conflict.smt2`
    and `bad-square-witness-qf-bv-drat` to
    `artifacts/examples/math/number-theory-v0/smt2/bad-square-witness-mod7-bitblast-conflict.smt2`,
    both checked by the `math_resource_bv_routes` QF_BV/DRAT regression.
    `modular-arithmetic-v0` now links
    `composite-nonunit-no-inverse-qf-bv-drat` to
    `artifacts/examples/math/modular-arithmetic-v0/smt2/nonunit-inverse-mod6-bitblast-conflict.smt2`
    and `fermat-units-mod-prime-qf-bv-drat` to
    `artifacts/examples/math/modular-arithmetic-v0/smt2/fermat-units-mod5-bitblast-conflict.smt2`,
    both checked by the shared QF_BV/DRAT route regression.
    `finite-chebyshev-systems-v0` now links
    `bad-duplicate-node-grid-rejected` and
    `bad-interpolation-sample-rejected` plus
    `bad-alternating-residual-rejected` to source-level QF_LRA/Farkas
    artifacts, checked by the `math_resource_lra_routes` regression.
    `finite-stochastic-kernels-v0` now links `bad-kernel-row-rejected` to
    `artifacts/examples/math/finite-stochastic-kernels-v0/smt2/bad-kernel-row-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
    `finite-ideals-v0` now links
    `qf-uf-quotient-ring-representative-alethe` to
    `artifacts/examples/math/finite-ideals-v0/smt2/quotient-ring-representative-congruence-conflict.smt2`,
    checked by the `math_resource_uf_routes` QF_UF/Alethe regression.
19. `finite-group-actions-v0` now links `bad-action-rejected` to
    `artifacts/examples/math/finite-group-actions-v0/smt2/bad-identity-action-alethe-conflict.smt2`,
    checked by the `math_resource_uf_routes` QF_UF/Alethe regression.
20. `finite-continuous-maps-v0` now links `bad-continuous-map-rejected` to
    `artifacts/examples/math/finite-continuous-maps-v0/smt2/bad-preimage-membership-alethe-conflict.smt2`,
    checked by the `math_resource_uf_routes` QF_UF/Alethe regression.
21. `finite-product-measure-v0` now links `bad-product-measure-rejected` to
    `artifacts/examples/math/finite-product-measure-v0/smt2/bad-product-measure-farkas-conflict.smt2`
    and `bad-product-marginal-rejected` to
    `artifacts/examples/math/finite-product-measure-v0/smt2/bad-product-marginal-farkas-conflict.smt2`,
    both checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
22. `finite-random-variables-v0` now links `bad-pushforward-rejected` to
    `artifacts/examples/math/finite-random-variables-v0/smt2/bad-pushforward-farkas-conflict.smt2`
    and `bad-expectation-through-pushforward-rejected` to
    `artifacts/examples/math/finite-random-variables-v0/smt2/bad-expectation-through-pushforward-farkas-conflict.smt2`,
    both checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
23. `finite-integration-v0` now links `bad-expectation-rejected` to
    `artifacts/examples/math/finite-integration-v0/smt2/bad-expectation-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
24. `finite-martingales-v0` now links `bad-stopped-expectation-rejected` to
    `artifacts/examples/math/finite-martingales-v0/smt2/bad-stopped-expectation-farkas-conflict.smt2`
    and `bad-martingale-rejected` to
    `artifacts/examples/math/finite-martingales-v0/smt2/bad-martingale-farkas-conflict.smt2`,
    both checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
25. Route-specific tamper/rejection regressions now land for the active
    certificate routes: Boolean CNF/LRAT, QF_BV DRAT, QF_LRA/Farkas,
    QF_LIA/Diophantine, and QF_UF/Alethe all mutate emitted resource
    certificates and require independent checker rejection.
26. `incidence-geometry-v0` now lands as the next geometry pack: exact
    line-equation replay, non-parallel line intersection, point-on-line replay,
    checked QF_LRA/Farkas bad intersection-coordinate and bad-incidence
    rejection, a focused learner page, and a bridge-row update under
    `bridge_coordinate_orientation_geometry`.
27. `rigid-configuration-geometry-v0` now lands as the next geometry pack:
    exact triangle distance-table replay, translation isometry replay,
    congruent-triangle distance replay, checked QF_LRA/Farkas bad-distance
    rejection, a focused learner page, and a bridge-row update under
    `bridge_coordinate_orientation_geometry`.
28. `finite-root-finding-v0` now links `bad-newton-step-rejected` to
    `artifacts/examples/math/finite-root-finding-v0/smt2/bad-newton-step-farkas-conflict.smt2`
    and `bad-bisection-width-rejected` to
    `artifacts/examples/math/finite-root-finding-v0/smt2/bad-bisection-width-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
29. `finite-separation-v0` now links
    `bad-convex-combination-point-rejected` to
    `artifacts/examples/math/finite-separation-v0/smt2/bad-convex-combination-point-farkas-conflict.smt2`
    and `bad-separator-rejected` to
    `artifacts/examples/math/finite-separation-v0/smt2/bad-separator-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
30. `finite-kkt-v0` now links `bad-kkt-stationarity-rejected` to
    `artifacts/examples/math/finite-kkt-v0/smt2/bad-stationarity-farkas-conflict.smt2`,
    and `bad-kkt-complementarity-rejected` to
    `artifacts/examples/math/finite-kkt-v0/smt2/bad-complementarity-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
31. `finite-sdp-v0` now links `bad-sdp-objective-rejected` to
    `artifacts/examples/math/finite-sdp-v0/smt2/bad-objective-farkas-conflict.smt2`,
    and `bad-sdp-duality-gap-rejected` to
    `artifacts/examples/math/finite-sdp-v0/smt2/bad-duality-gap-farkas-conflict.smt2`,
    and `bad-sdp-slack-entry-rejected` to
    `artifacts/examples/math/finite-sdp-v0/smt2/bad-slack-entry-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
32. `finite-gradient-descent-v0` now links `bad-descent-value-rejected`,
    `bad-step-coordinate-rejected`, and `bad-descent-bound-slack-rejected` to
    `artifacts/examples/math/finite-gradient-descent-v0/smt2/bad-decrease-farkas-conflict.smt2`
    `artifacts/examples/math/finite-gradient-descent-v0/smt2/bad-step-coordinate-farkas-conflict.smt2`,
    and
    `artifacts/examples/math/finite-gradient-descent-v0/smt2/bad-descent-bound-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regressions.
33. `finite-line-search-v0` now links `bad-armijo-acceptance-rejected`,
    `bad-descent-direction-rejected`, and
    `bad-accepted-candidate-rejected` to
    `artifacts/examples/math/finite-line-search-v0/smt2/bad-armijo-farkas-conflict.smt2`,
    `artifacts/examples/math/finite-line-search-v0/smt2/bad-descent-direction-farkas-conflict.smt2`,
    and
    `artifacts/examples/math/finite-line-search-v0/smt2/bad-accepted-candidate-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regressions.
34. `finite-wolfe-line-search-v0` now links `bad-line-minimizer-rejected` and
    `bad-wolfe-curvature-rejected` to
    `artifacts/examples/math/finite-wolfe-line-search-v0/smt2/bad-line-minimizer-farkas-conflict.smt2`
    and
    `artifacts/examples/math/finite-wolfe-line-search-v0/smt2/bad-wolfe-curvature-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regressions.
35. `finite-active-set-qp-v0` now links
    `bad-active-set-free-gradient-rejected` to
    `artifacts/examples/math/finite-active-set-qp-v0/smt2/bad-free-gradient-farkas-conflict.smt2`,
    `bad-inactive-slack-rejected` to
    `artifacts/examples/math/finite-active-set-qp-v0/smt2/bad-inactive-slack-farkas-conflict.smt2`,
    and `bad-degenerate-active-multiplier-rejected` to
    `artifacts/examples/math/finite-active-set-qp-v0/smt2/bad-degenerate-multiplier-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regressions.
36. `finite-projected-gradient-v0` now links `bad-projected-point-rejected` to
    `artifacts/examples/math/finite-projected-gradient-v0/smt2/bad-projection-farkas-conflict.smt2`
    and `bad-projected-decrease-rejected` to
    `artifacts/examples/math/finite-projected-gradient-v0/smt2/bad-projected-decrease-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regressions.
37. `finite-proximal-gradient-v0` now links `bad-proximal-point-rejected` to
    `artifacts/examples/math/finite-proximal-gradient-v0/smt2/bad-proximal-point-farkas-conflict.smt2`
    and `bad-composite-decrease-rejected` to
    `artifacts/examples/math/finite-proximal-gradient-v0/smt2/bad-composite-decrease-farkas-conflict.smt2`
    and `bad-box-proximal-point-rejected` to
    `artifacts/examples/math/finite-proximal-gradient-v0/smt2/bad-box-proximal-point-farkas-conflict.smt2`,
    all checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
38. `finite-circle-geometry-v0` now links `bad-circle-radius-rejected` to
    `artifacts/examples/math/finite-circle-geometry-v0/smt2/bad-radius-farkas-conflict.smt2`
    and `bad-circle-line-intersection-rejected` to
    `artifacts/examples/math/finite-circle-geometry-v0/smt2/bad-line-intersection-farkas-conflict.smt2`,
    both checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
39. `finite-inversion-geometry-v0` now links `bad-inversion-image-rejected`
    to
    `artifacts/examples/math/finite-inversion-geometry-v0/smt2/bad-inversion-x-farkas-conflict.smt2`
    and `bad-inverse-distance-product-rejected` to
    `artifacts/examples/math/finite-inversion-geometry-v0/smt2/bad-inverse-distance-product-farkas-conflict.smt2`,
    both checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
40. `finite-cyclic-geometry-v0` now links
    `bad-cyclic-diagonal-intersection-rejected` to
    `artifacts/examples/math/finite-cyclic-geometry-v0/smt2/bad-diagonal-intersection-farkas-conflict.smt2`
    and `bad-cyclic-opposite-angle-rejected` to
    `artifacts/examples/math/finite-cyclic-geometry-v0/smt2/bad-opposite-angle-farkas-conflict.smt2`,
    and `bad-cyclic-ptolemy-rejected` to
    `artifacts/examples/math/finite-cyclic-geometry-v0/smt2/bad-ptolemy-farkas-conflict.smt2`,
    all checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
41. [`matrix-computation-index.md`](../learn/math/matrix-computation-index.md)
    now groups LU, rank/nullity, residual, projection, Rayleigh/eigenpair,
    characteristic-polynomial, checked trace-invariant, finite random-matrix,
    chain-complex, operator, module, and tensor rows by replay, QF_LRA/Farkas, QF_UF/Alethe,
    QF_LIA/Diophantine, Lean-horizon, and numerical-honesty boundary.
42. [`analysis-calculus-theorem-horizon-map.md`](../learn/math/analysis-calculus-theorem-horizon-map.md)
    now maps analysis/calculus-adjacent finite shadows to their theorem
    horizons: real completeness, IVT/MVT/FTC, compactness/connectedness,
    sequence and recurrence convergence, root-finding convergence,
    optimization convergence and duality, measure/probability convergence,
    functional/operator theory, and dynamics.
43. [`matrix-corpus-benchmark-boundary.md`](../learn/math/matrix-corpus-benchmark-boundary.md)
    now separates matrix educational resources, solver regressions,
    benchmark-corpus rows, and theorem-horizon claims, with promotion criteria
    before any matrix row is used for solver-reuse or performance language.
44. [`tax-benefit-arithmetic-v0`](../rules-as-code/examples/tax-benefit-arithmetic-v0/)
    now adds the third rules/law pack, reusing integer thresholds,
    household-size adjustments, caps, active phase-out monotonicity,
    effective-date witnesses, and checked Bool/QF_LIA proof fixtures.
45. [`rules-query-dashboard.md`](../rules-as-code/generated/rules-query-dashboard.md)
    now adds the generated rules/law query surface, exposing bounded sample
    rows, generated-query families, and deterministic query-row JSON under
    [`../rules-as-code/generated/queries/`](../rules-as-code/generated/queries/)
    from committed rule-pack JSON.
46. Functional-analysis/operator field-readiness consumer queries now land in
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
    `scripts/check-foundational-resources.sh`, covering the Farkas field
    summary, operator bridge lookup, and checked finite-operator,
    inner-product positivity/projection, Chebyshev, and spectral rows without promoting
    infinite-dimensional theorem claims.
47. Topology field-readiness consumer queries now land in
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
    `scripts/check-foundational-resources.sh`, covering the Boolean field
    summary, compactness/preimage bridge lookups, and checked Boolean/Alethe
    topology rows without promoting arbitrary compactness, connectedness,
    homeomorphism, or homology-invariance theorems.
48. Statistics field-readiness consumer queries now land in
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
    `scripts/check-foundational-resources.sh`, covering the Farkas field
    summary, finite-table/tail-count bridge lookups, checked exact-rational
    statistics rows, and checked integer-count rows without promoting
    floating-point inference or asymptotic sampling claims.
49. Linear-algebra field-readiness consumer queries now land in
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
    `scripts/check-foundational-resources.sh`, covering Farkas and Alethe field
    summaries, rank/projection bridge lookups, checked exact-rational matrix
    rows, and checked equality-heavy finite vector/module/tensor rows without
    promoting spectral, stability, or general vector-space theorem claims.
50. Core algebra/number/graph field-readiness consumer queries now land in
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
    `scripts/check-foundational-resources.sh`, covering abstract-algebra
    Alethe readiness, homomorphism/ideal bridge lookups, checked Alethe and
    fixed-width QF_BV finite-algebra rows, number-theory Diophantine
    readiness, checked integer-arithmetic rows, and graph-theory Boolean
    readiness with checked finite graph rows without promoting arbitrary
    algebraic-structure, unbounded number-theory, asymptotic algorithm, or
    general graph-theorem claims.
51. Analysis/numerical/complex field-readiness consumer queries now land in
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
    `scripts/check-foundational-resources.sh`, covering real-analysis Farkas
    readiness, epsilon/gradient bridge lookups, checked bounded-analysis rows,
    numerical-analysis Farkas readiness, residual/operator bridge lookups,
    checked exact numerical rows, complex-analysis Farkas readiness, real-pair
    bridge lookup, and checked algebraic complex rows without promoting
    completeness, convergence, floating-point stability, holomorphic,
    analytic-continuation, or theorem-level calculus claims.
52. Foundations/discrete/probability field-readiness consumer queries now land
    in [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
    `scripts/check-foundational-resources.sh`, covering logic/proof Boolean
    readiness, proof-vocabulary lookups, checked proof-pattern/CNF rows,
    set-theory/foundations Alethe readiness, partition lookups, checked finite
    relation/function/quotient rows, discrete-math Diophantine readiness,
    finite-family lookups, checked counting/coefficient/tail-count rows,
    probability-theory Farkas readiness, probability-table lookups, and checked
    finite probability/process rows without promoting proof automation,
    ZFC/infinite set theory, asymptotic combinatorics, continuous probability,
    stochastic-process limits, or theorem-level probability claims.
53. [FIELD-READINESS-QUERY-MATRIX.md](FIELD-READINESS-QUERY-MATRIX.md) now
    lands as the compact R6 consumer map for all 18 math fields. It records
    pack/check counts, the primary smoke-checked route, bridge lookup terms,
    checked-row drilldown, and theorem-horizon boundary for each field while
    keeping the public boundary as committed JSON plus
    `query-foundational-resources.py`.
54. [MATRIX-COMPUTATION-QUERIES.md](MATRIX-COMPUTATION-QUERIES.md) now lands
    as the matrix-resource consumer map for concept-plus-route discovery.
    `query-foundational-resources.py packs/checks --concept ...` reads atlas
    `example_packs` membership so LU, residual, rank/nullity, eigenpair,
    random-matrix, tensor/module, operator, and Chebyshev rows are queryable by
    computation family and proof route.
55. [PROOF-ROUTE-QUERY-MATRIX.md](PROOF-ROUTE-QUERY-MATRIX.md) now lands as
    the proof-route consumer map. `query-foundational-resources.py routes`
    summarizes route coverage from proof-cookbook recipe links with normalized
    route aliases and optional field scoping.
56. Landed: add number-system semantic-boundary bridge rows.
    `bridge_exact_vs_floating_arithmetic` and
    `bridge_totality_conventions` make exact rational replay, numerical
    honesty, SMT totality, explicit side conditions, and frontend
    trapping/UB boundaries queryable from the atlas. `CONSUMER-QUERIES.md` and
    `check-foundational-resources.sh` now smoke-check number-theory totality
    lookup and numerical-analysis floating-boundary lookup.
57. Landed: add the gcd/divisibility witness bridge row.
    `bridge_gcd_divisibility_witness` makes gcd/common-divisor replay, Bezout
    coefficient replay, quotient witnesses, and gcd non-divisibility
    QF_LIA/Diophantine certificates queryable from the atlas. The
    number-theory consumer smoke now includes `concepts --field number_theory
    --text gcd --require-any`.
58. Landed: add the finite chain-complex/homology replay bridge row.
    `bridge_finite_chain_homology_replay` makes finite simplicial-complex
    closure, oriented-boundary replay, boundary-squared-zero, Betti-rank
    replay, and checked bad-boundary coefficient evidence queryable through
    topology homology lookup and concept-scoped Diophantine route queries while
    keeping homology invariance, exact sequences, homotopy equivalence,
    cohomology-operation laws, and general algebraic topology in the
    Lean-horizon lane.
59. Landed: add the finite topology-operator/homeomorphism bridge row.
    `bridge_finite_topology_operator_homeomorphism` makes finite topology
    axiom replay, closure/interior replay, continuity by open preimage,
    homeomorphism replay, checked malformed-topology Bool/CNF rows, and
    checked malformed-preimage QF_UF/Alethe rows queryable through topology
    closure/homeomorphism lookup and concept-scoped Alethe route queries while
    keeping arbitrary closure-operator theorems, homeomorphism invariance,
    compactness/connectedness preservation, homology invariance, and general
    topology in the Lean-horizon lane.
60. Landed: add the finite boundary-operator replay bridge row.
    `bridge_finite_boundary_operator_replay` makes oriented boundary
    coefficients, boundary-of-boundary cancellation, boundary-matrix shape, and
    checked bad-boundary coefficient evidence queryable through topology
    boundary lookup and concept-scoped Diophantine route queries while keeping
    functoriality, exactness, homology invariance, cohomology-operation laws,
    and general algebraic topology in the Lean-horizon lane.
61. Landed: add the finite specialization-order replay bridge row.
    `bridge_finite_specialization_order_replay` makes finite topology to
    preorder replay, singleton-closure characterization, finite `T0`
    antisymmetry replay, and checked bad `T0` QF_UF/Alethe evidence queryable
    through topology specialization lookup and concept-scoped Alethe route
    queries while keeping T0 quotients, sobriety, domain theory, and
    arbitrary-space specialization-order theorems in the Lean-horizon lane.
62. Landed: add the finite cohomology replay bridge row.
    `bridge_finite_cohomology_replay` makes finite F2 cochain coboundary
    replay, `delta^2 = 0`, F2 cohomology-rank replay, non-coboundary cocycle
    checking, and checked bad coboundary-value QF_UF/Alethe evidence queryable
    through topology cohomology lookup and concept-scoped Alethe route queries
    while keeping cohomology functoriality, cohomology-operation laws,
    universal coefficients, de Rham comparison, sheaf cohomology, duality, and
    invariance theorems in the Lean-horizon lane.
63. Landed: add the finite cup-product replay bridge row.
    `bridge_finite_cup_product_replay` makes ordered F2 cup-product replay,
    one finite coboundary-Leibniz row, and checked bad cup-product QF_BV/DRAT
    evidence queryable through topology cup lookup and concept-scoped QF_BV
    route queries while keeping associativity, graded commutativity,
    naturality, cohomology-ring quotienting, universal coefficients, and
    invariance theorems in the Lean-horizon lane.
64. Landed: add the finite torsion-homology replay bridge row.
    `bridge_finite_torsion_homology_replay` makes a two-term integer chain
    complex, one-entry Smith diagonal replay, `H0 = Z/2`, and checked bad
    torsion-generator QF_LIA/Diophantine evidence queryable through topology
    torsion lookup and concept-scoped Diophantine route queries while keeping
    general Smith normal form, universal coefficients, Ext/Tor functor laws,
    exact sequences, and homology invariance in the Lean-horizon lane.
65. Revisit crate/repo boundaries only after three real consumers or repeated
    encoder implementations make scripts insufficient.

## Validation Commands

For documentation-only plan edits:

```sh
git diff --check
./scripts/check-links.sh
```

For resource metadata, generated dashboard, or pack edits:

```sh
git diff --check
./scripts/check-foundational-resources.sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>
python3 scripts/consume-foundational-resources.py
```

For proof-route promotions, add the relevant cargo regression from
[PROOF-UPGRADE-FRONTIER.md](PROOF-UPGRADE-FRONTIER.md) before updating status.
