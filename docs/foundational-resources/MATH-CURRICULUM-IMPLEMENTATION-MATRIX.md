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
| R3 learner path | focused lesson or named cluster page | `./scripts/check-links.sh` plus generated learner dashboard and [Learner Coverage Audit](LEARNER-COVERAGE-AUDIT.md) |
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
| `predicate-logic` | `finite-predicate-v0` | Landed bridge rows for finite quantifier expansion and finite countermodel replay. | Finite expansion plus QF_UF/Alethe for equality-heavy fragments. | Pack rows distinguish finite-domain validity from first-order validity. |
| `proof-methods` | `proof-methods-refutation-v0`, `proof-methods-patterns-v0` | Turn direct/contrapositive/cases/contradiction into reusable proof-pattern rows. | CNF/LRAT for refutation examples; Lean horizon for natural deduction. | Learner page can trace proof method -> solver query -> checked evidence. |
| `induction` | `induction-obligations-v0`, `induction-patterns-v0` | Split bounded base/step checks from induction-schema reconstruction targets. | QF_LIA for finite obstructions; Lean horizon for general induction. | No pack claims full induction from bounded prefixes. |
| `sets` | finite sets, lattices, cardinality/topology packs | Add concept rows for Boolean algebra, finite lattice laws, compactness shadows, and counterexample replay. | CNF/LRAT for Boolean refutations including finite open-cover misses; QF_UF/Alethe for lattice/order conflicts. | Every false set/lattice/topology identity has either evidence or an explicit route gap. |
| `relations-and-functions` | relation/function, equivalence, composition, monoid, permutation, action packs | Landed bridge rows for quotient maps, finite group actions, finite partition/relation roundtrips, and image/preimage/inverse tables. | QF_UF/Alethe for function consistency and congruence conflicts. | Equality-heavy rows use checked Alethe where available. |
| `cardinality` | finite cardinality and cardinality-principles packs | Landed bridge rows for finite Boolean algebra, finite bijection/cardinality, powerset cardinality, and infinite cardinality theorem horizons. | finite replay/CNF for bounded no-map rows; Lean horizon for Cantor/infinite facts. | Infinite claims are never benchmarked as finite checks. |
| `naturals` | `natural-arithmetic-v0` | Landed totality-convention bridge row; add narrower Peano-shadow or BV-vs-LIA rows only when reused across packs. | Bounded replay, QF_LIA, QF_BV where fixed width is educationally relevant. | Width, operation conventions, and finite prefix limits are visible in metadata and lesson text. |
| `integers` | `integer-lia-v0` | Promote common linear-obstruction patterns into shared Diophantine examples. | QF_LIA/Diophantine. | Bad linear rows carry checked integer evidence or a named missing route. |
| `rationals` | `rationals-lra-v0`, rational polynomial pack, finite Aitken acceleration, finite Steffensen method, finite ridge regression, finite linear discriminant | Landed exact-vs-floating arithmetic bridge row; split density/order, exact sequence/fixed-point acceleration, regression, or discriminant rows further only when learner pages need them. | QF_LRA/Farkas for impossible rational inequalities, bad exact accelerated-value claims, bad ridge coefficients, and bad Fisher directions. | Farkas-backed rows recheck independently of solver search, and exact rational rows do not imply floating-point claims. |
| `reals` | RCF shadow, bounded real analysis, metric continuity, finite Simpson quadrature, finite Romberg extrapolation, finite divided-difference and barycentric interpolation, finite-difference derivatives, finite Taylor polynomials, finite cubic Hermite interpolation, finite natural cubic spline interpolation, finite root finding, finite secant method, finite Aitken acceleration, finite Steffensen method, finite ridge regression, finite linear discriminant, finite separation, finite KKT, finite active-set QP, finite SDP, finite gradient descent, finite line search, finite Wolfe line search, finite projected gradient, finite proximal gradient, finite circle, inversion, and cyclic geometry | Add concept rows for balls, limits, continuity, compactness, integration/quadrature/extrapolation/interpolation/finite-difference derivatives/Taylor polynomials/Hermite/spline interpolation, root-finding/secant/Aitken/Steffensen acceleration, regularized regression, linear discriminants, separation, KKT, active-set QP, SDP, gradient descent, line search, Wolfe line search, projected gradient, proximal gradient, finite circle/inversion/cyclic geometry, and completeness/convergence/geometry-theorem horizons. | QF_LRA/Farkas for bounded bad-delta, bad-quadrature-value, bad-Romberg-value, bad-interpolation-value, bad-barycentric-value, bad-finite-difference-value, bad-Taylor-value, bad-Hermite-value, bad-spline-value, bad-iterate, bad-secant-step, bad-Aitken-value, bad-Steffensen-value, bad-ridge-beta0, bad-Fisher-direction, bad-separator, bad-stationarity, bad-complementarity, bad-free-gradient, bad-inactive-slack, bad-objective, bad-duality-gap, bad-slack-entry, bad-decrease, bad-descent-bound, bad-Armijo, bad descent-direction, bad accepted-candidate, bad-Wolfe-minimizer, bad-Wolfe-curvature, bad-projection, bad-projected-decrease, bad-proximal-point, bad-composite-decrease, bad-box-proximal-point, bad-radius, bad-line-intersection, bad-inverse-coordinate, bad-diagonal-intersection, bad-opposite-angle, and bad-Ptolemy rows, QF_LRA/NRA for algebraic shadows; Lean horizon for completeness/general topology, integration/quadrature/extrapolation/interpolation/Hermite/spline/finite-difference/Taylor theory, ridge-regression and Fisher LDA theory, separation, KKT sufficiency, active-set method theory, SDP duality, descent-rate, Wolfe/line-search/projected/proximal-gradient convergence, circle/inversion/cyclic geometry, and convergence. | Each epsilon-delta/integration/interpolation/Hermite/spline/finite-difference/Taylor/root-finding/sequence/fixed-point-acceleration/regularized-regression/linear-discriminant/separation/KKT/active-set/SDP/descent/line-search/Wolfe/projected/proximal-gradient/circle/inversion/cyclic pack says fixed rational instance vs theorem, and metric-continuity, finite-Simpson, finite-Romberg-extrapolation, finite-divided-differences, finite-barycentric-interpolation, finite-difference-derivatives, finite-taylor-polynomials, finite-cubic-hermite-interpolation, finite-cubic-spline-interpolation, finite-root-finding, finite-secant-method, finite-aitken-acceleration, finite-steffensen-method, finite-ridge-regression, finite-linear-discriminant, finite-separation, finite-KKT, finite-active-set-QP, finite-SDP, finite-gradient-descent, finite-line-search, finite-wolfe-line-search, finite-projected-gradient, finite-proximal-gradient, finite-circle-geometry, finite-inversion-geometry, plus finite-cyclic-geometry now have checked finite bad-row routes. |
| `complex` | complex algebraic and transform packs | Add real-pair encoding note and analytic-horizon rows. | NRA/LRA real-pair replay; Lean horizon for holomorphic theory. | Algebraic complex checks avoid claiming analytic coverage. |
| `divisibility-and-euclid` | `gcd-bezout-v0` | Landed reusable gcd/divisibility witness bridge row for number-theory and algebra packs. | Computed witness replay; QF_LIA/Diophantine for divisibility obstructions. | Bezout rows validate both gcd and coefficient identity, and gcd obstruction rows carry checked evidence where promoted. |
| `modular-arithmetic` | modular arithmetic and finite ideals | Landed modular CRT/inverse bridge row, checked nonunit inverse and incompatible non-coprime CRT Diophantine rows, checked fixed-width nonunit-inverse and Fermat-unit QF_BV rows, and adjacent quotient/ideal bridge rows; add narrower quotient-ring rows only when reuse demands them. | QF_LIA/Diophantine, QF_UF/Alethe quotient congruence, and QF_BV fixed-width finite residues. | Nonunit inverse, incompatible CRT, and Fermat-unit rows carry checked arithmetic evidence; quotient rows distinguish table replay from representative congruence. |
| `groups` | finite groups, monoids, permutations, actions, homomorphisms | Landed bridge rows for homomorphism preservation, kernel/image replay, quotient maps, and finite group actions; orbit-stabilizer and Burnside can split later if reused broadly. | QF_UF/Alethe for table congruence and action-law conflicts. | Table checks keep associativity/action-law replay explicit. |
| `rings` | finite rings, ideals, modules, homomorphisms | Maintain the landed bad distributivity and bad multiplicative-identity BV routes; add more finite ring-table contradictions only when they introduce distinct fixed-width pressure. | QF_BV bit-blast/DRAT plus QF_UF/Alethe for homomorphism preservation and quotient representative congruence. | Unsat finite-ring rows carry checked CNF or Alethe evidence without overclaiming Lean. |
| `fields` | finite fields, vector/dual/tensor packs | Maintain the landed composite no-inverse and bad inverse-candidate BV routes; add more fixed finite-field contradictions only when they introduce distinct inverse, distributivity, or table pressure. | QF_BV for finite fields; QF_UF/Alethe for table equality conflicts. | Composite-modulus non-field and bad inverse-candidate contrasts have checked routes. |
| `polynomials` | identities, rational factorization, generating functions, finite root finding/secant method, finite interpolation, finite quadrature/extrapolation, finite-difference derivatives, finite Taylor polynomials, finite cubic Hermite interpolation, finite natural cubic spline interpolation, finite circle/inversion/cyclic geometry | Add coefficient-ring, polynomial-division, finite root-finding/secant method, finite interpolation/Taylor/Hermite/spline, finite polynomial quadrature/extrapolation, and finite polynomial-geometry reusable rows. | Finite replay, QF_LIA/LRA coefficient constraints, QF_LRA/Farkas for linearized exact conflicts, Lean horizon for general factorization, interpolation, quadrature/extrapolation, Taylor/Hermite/spline theory, circle/inversion/cyclic geometry, and convergence. | Factorization, root-finding/secant-method, interpolation, Simpson/Romberg quadrature, finite-difference, Taylor, Hermite, spline, circle, inversion, and cyclic rows replay product, degree/leading constraints, polynomial values, exact iterates, bisection widths, divided-difference tables, barycentric weights, derivative stencils, Taylor coefficients, Taylor remainders, Hermite endpoint value/slope rows, spline piece polynomials and knot-continuity rows, Simpson weighted sums, Romberg source trapezoid values and extrapolated values, squared radii, tangent lines, chord dot products, inverse images, distance products, diagonal midpoints, angle dot products, and Ptolemy product sums. |
| `sequences-and-limits` | sequence-limit shadow, bounded monotone sequence, finite recurrence prefix, finite Aitken acceleration, finite Steffensen method, real-analysis, generating functions | Bounded Cauchy-tail, monotone-prefix bad-bound, finite recurrence bad-value, bad affine-step, and bad exact accelerated-value rows landed; add broader convergence-horizon rows only when reused. | Finite replay/LRA for bounded tails, recurrence prefixes, exact sequence-acceleration triples, and fixed-point acceleration triples; Lean horizon for general convergence and recurrence theory. | Lessons keep finite prefix and finite acceleration evidence separate from convergence and closed-form/asymptotic theorems. |
| `counting` | counting, permutations, actions, generating functions | Landed finite-counting replay bridge for permutation/Pascal rows, pigeonhole, double counting, coefficient extraction, finite orbit counts, and exact tail counts; add narrower asymptotic or recurrence-horizon rows only when reused. | CNF/LRAT for pigeonhole; QF_LIA/Diophantine for finite count contradictions; finite replay for enumerative witnesses. | Count rows include deterministic universe, enumeration, route artifact, and theorem-horizon boundary. |
| `number-theory` | number theory, modular, gcd, integer LIA | Maintain the landed bounded Diophantine witness/obstruction pair and residue proof-route comparisons; add new families only when they introduce distinct BV/LIA pressure. | QF_LIA/Diophantine; QF_BV for fixed modulus; Lean horizon for deep theorems. | Each row identifies bounded search vs number-theory theorem. |
| `linear-algebra` | rational matrices, finite vector/dual/module/tensor, spectral, singular-value, Gaussian-elimination, Schur-complement, real-Schur, polar-decomposition, QR-iteration, shifted-QR, Jordan-chain, covariance, ridge, and linear-discriminant rows, orthogonal transforms, exact LU/QR/Cholesky factorizations, invariants, separation, KKT, active-set QP, SDP, gradient descent, line search, Wolfe line search, projected gradient, proximal gradient, circle tangent/chord checks, inversion vector checks, cyclic diagonal/angle/Ptolemy checks | Landed matrix-computation bridge rows plus algebra-map rows for exact Gaussian elimination, LU, QR, Cholesky, Schur-complement, real-Schur, polar, QR-step, and shifted-QR replay with separate checked bad row-operation, product-entry, scalar, superdiagonal, diagonal, or next-step entry proof rows, nullspace replay with checked bad component evidence, kernel/image, quotient maps, module actions, vector subspace closure, dual covector additivity, tensor bilinearity and left-additivity evidence, inner-product projection-orthogonality replay, Walsh-Hadamard transform/inverse/Parseval replay, covariance/Gram replay, finite Fisher-discriminant within-scatter and direction replay, singular-vector/SVD shadow replay, Jordan-chain/nilpotent-part replay, separating-hyperplane replay, KKT stationarity/complementarity replay, finite active-face stationarity/slack replay with checked inactive-slack evidence, finite SDP slack/objective replay, finite gradient-step replay, finite Armijo/Wolfe line-search replay, finite projected-gradient interval/decrease replay, finite proximal-gradient soft-threshold/composite-decrease and box-plus-L1 replay, finite circle tangent/chord dot-product replay, finite inversion scalar-vector/determinant replay, and finite cyclic diagonal/angle/Ptolemy replay; split more dual/projection/transform/SVD/Gaussian/Schur/Jordan/QR-iteration/discriminant maps only when reuse demands a distinct equality shape. | QF_LRA/Farkas, finite-field replay, QF_UF/Alethe for algebraic table conflicts. | Matrix, Gaussian-elimination eliminated-RHS, LU/QR/Cholesky product-entry, Schur scalar, real-Schur superdiagonal, polar diagonal, QR-step entry, shifted-QR entry, nullspace-component, dot-product, projection-orthogonality, transform-coefficient, singular-value-bound, Fisher-direction, Jordan-component, stationarity, complementarity, active-set QP, SDP objective, descent-step, line-search, Wolfe-line-search, projected-gradient, proximal-gradient, finite circle, finite inversion, and finite cyclic rows can become solver regressions with source-pack back-links. |
| `calculus` | algebraic calculus, Riemann sums, finite Simpson-rule quadrature, finite Romberg extrapolation, finite divided-difference and barycentric interpolation, finite-difference derivatives, finite Taylor polynomials, finite cubic Hermite interpolation, finite natural cubic spline interpolation, multivariable rational calculus, finite root finding/secant method, finite active-set QP, finite line search, finite Wolfe line search, finite projected gradient, finite proximal gradient | Add derivative/integral/quadrature/extrapolation/interpolation/Taylor/Hermite/spline/convergence theorem horizon rows plus exact algebraic, quadrature/extrapolation, interpolation, Taylor/Hermite/spline, and algorithm-step shadows. | LRA/NRA for polynomial shadows; QF_LRA/Farkas for bad finite quadrature, bad Romberg extrapolated values, interpolation, finite-difference, Taylor, Hermite, and spline values; Lean horizon for FTC, differentiability, Simpson/Newton-Cotes and Romberg/Richardson quadrature theory, interpolation theory, Taylor theorem/remainder/convergence, Hermite/spline theory, active-set/Wolfe/line-search/projected/proximal-gradient convergence, and convergence. | Calculus packs never conflate finite symbolic, quadrature/extrapolation, interpolation, Taylor, Hermite, spline, or iterative replay with analytic theorem proof. |

## Field Extension Matrix

| Field | Curriculum Anchor | Build Next | Solver / Proof Pressure |
|---|---|---|---|
| `logic_and_proof` | foundations layer | proof-object lessons and proof-pattern atlas rows | CNF/LRAT, Alethe, Lean reconstruction |
| `set_theory_and_foundations` | sets, relations, cardinality | quotients, lattices, finite/infinite boundary rows | QF_UF/Alethe, finite replay, Lean horizon |
| `discrete_math` | counting, relations | graph search, matching, cuts, generating functions, asymptotic horizons | SAT/CNF, finite replay, Lean horizon |
| `graph_theory` | sets, relations, counting | maintain landed finite graph replay/obstruction bridge across coloring, reachability, search runtime, matching, cuts, and d-separation; add theorem/asymptotic rows only when reused | SAT/CNF, QF_BV for fixed color encodings, BV/LIA counters, model replay |
| `number_theory` | divisibility, modular, fields | bounded Diophantine and residue-family packs | QF_LIA, QF_BV |
| `linear_algebra` | fields, polynomials, relations | Gaussian-elimination transcript replay, LU/QR/Cholesky exact replay plus checked bad row/product proof rows, Schur-complement block replay plus checked bad scalar proof row, rank/nullity, residual, ordinary/ridge regression, condition-number, singular-value/SVD, Jordan-chain, spectral, tensor and module rows | QF_LRA/Farkas, finite-field replay |
| `abstract_algebra` | groups, rings, fields | homomorphisms, ideals, quotients, modules, tensor products | QF_UF/Alethe, QF_BV |
| `real_analysis` | rationals, reals, sequences, calculus | balls, bounded epsilon-delta, Simpson-rule quadrature, Romberg extrapolation, divided-difference and barycentric interpolation, finite-difference derivatives, Taylor polynomials, Hermite interpolation, sequence/fixed-point acceleration, compactness/continuity horizons | QF_LRA/Farkas, QF_LRA/NRA, Lean horizon |
| `complex_analysis` | complex, reals, polynomials | real-pair algebra now; analytic rows later | NRA/LRA, Lean horizon |
| `topology` | sets, reals, linear algebra | landed finite topology/compactness/connectedness/preimage bridge rows plus finite topology-operator/homeomorphism, finite specialization-order, finite boundary-operator, finite chain-complex/homology, finite torsion-homology, finite cohomology, and finite cup-product replay bridges; add only distinct quotient, universal-coefficient, cohomology-ring quotienting, or theorem-invariance pressure | finite replay, QF_UF/Alethe, QF_LIA/LRA, QF_BV, Lean horizon |
| `measure_theory` | sets, probability, reals | landed finite measure/additivity, monotonicity/subadditivity, and finite product/integration bridge rows; add narrower countable-measure or convergence rows only when reused | finite replay, QF_LRA, Lean horizon |
| `probability_theory` | counting, rationals, measure | probability tables, kernels, Markov chains, hitting times, concentration | QF_LRA, QF_LIA counts, replay |
| `statistics` | probability, linear algebra | exact tests, ordinary and ridge regression, finite linear-discriminant/classification replay, finite sampling tables, Schur conditional-variance shadows, numerical-honesty rows | QF_LRA, QF_LIA, replay |
| `optimization_and_convexity` | rationals, reals, linear algebra | landed LP objective/Farkas, rational convexity/gradient bridge rows with checked bad midpoint and affine-threshold evidence, finite root-finding step and bisection-width replay, finite hyperplane-separation replay, finite KKT replay with checked stationarity/complementarity evidence, finite active-set QP face/slack replay with checked inactive-slack evidence, finite degenerate active-bound replay, finite SDP replay, exact Gaussian-elimination, QR/Cholesky factorization replay, Schur-complement positive-definite replay, ordinary and ridge-regression objective replay, finite Fisher-discriminant direction/threshold replay, finite gradient-descent replay with checked descent-bound evidence, finite Armijo line-search rejected-step, descent-direction, and accepted-candidate replay, finite Wolfe line-search replay, finite projected-gradient interval/decrease replay, finite proximal-gradient soft-threshold/composite-decrease replay, and finite box-plus-L1 proximal replay; add narrower duality, working-set pivots, higher-dimensional SDP, covariance/Hessian factorization families, group-lasso/active-set proximal, discriminant/regularized-classifier variants, strong-Wolfe/nonconvex line-search, or stochastic/convergence rows only when reused | QF_LRA/Farkas, NRA shadows |
| `numerical_analysis` | linear algebra, calculus | maintain landed finite dynamics/Euler bridge alongside residual bounds, interval boxes, exact condition-number/perturbation shadows, Gaussian-elimination transcripts, Schur-complement block shadows, singular-value/SVD norm shadows, exact Jordan-chain shadows, exact ridge regularized-normal-equation replay, exact linear-discriminant/classification replay, exact Simpson quadrature, exact Romberg extrapolation, exact divided-difference and barycentric interpolation, exact finite-difference derivative stencils, exact Taylor polynomial/truncation replay, exact cubic Hermite interpolation replay, exact sequence and fixed-point acceleration replay, exact error recurrences, root-finding, explicit and implicit time-stepping replay including backward Euler and Crank-Nicolson plus Adams-Bashforth and BDF2 multistep replay, LU/QR/Cholesky factorization replay, active-set QP, gradient-descent, Armijo/Wolfe line-search descent-direction and accepted-candidate arithmetic, projected-gradient, and proximal-gradient composite-decrease iterations | QF_LRA, replay, numerical-honesty metadata |
| `differential_equations_and_dynamical_systems` | calculus, linear algebra | maintain landed finite dynamics/Euler bridge for bounded recurrences, Euler traces, implicit backward Euler and Crank-Nicolson traces, Adams-Bashforth derivative-history traces, BDF2 implicit-history traces, invariant checks, threshold reachability, replay-only bad dynamics rows, separate checked QF_LRA proof rows, and finite error tables | QF_LRA, BV/LIA counters, Lean horizon |
| `geometry` | reals, polynomials, linear algebra | landed coordinate/incidence/rigid/affine/oriented replay plus finite circle/inversion/cyclic replay bridge rows; add only distinct nontrivial circle-line correspondence, higher-degree polynomial-geometry, or theorem-reconstruction pressure beyond the current affine collinearity-determinant, area-scaling, circle-line, square angle-dot, and Ptolemy rows when reused | QF_LRA/NRA, replay |
| `functional_analysis_and_operator_theory` | linear algebra, real analysis | finite operators, inner products, exact condition-number, singular-value, and Jordan/nilpotent shadows, Chebyshev-system slices | QF_LRA, finite replay, Lean horizon |

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
   Gaussian-elimination, LU/QR/Cholesky replay, rank/nullity replay, residual bounds, Rayleigh/eigenpair witnesses,
   characteristic-polynomial replay with checked trace-invariant evidence,
   exact Walsh-Hadamard transform replay, and finite random-matrix moments.
3. R1 bridge-concept rows landed for algebra-map vocabulary: homomorphism
   preservation, kernel/image replay, quotient maps, ideal closure, module
   actions, tensor bilinearity, and finite group actions.
4. R1 bridge-concept rows landed for probability/statistics finite-table and
   distribution-distance vocabulary, measure-theory finite additivity/product/
   integration
   vocabulary, optimization/convexity LP objective and convexity-shadow
   vocabulary, proof/logic vocabulary, proof-object anatomy vocabulary, and
   set/foundations vocabulary, including finite Boolean algebra,
   partition/relation roundtrips, image/preimage/inverse tables, finite
   bijection/cardinality, and cardinality theorem horizons. R1 bridge-concept
   rows now also land for coordinate/incidence/rigid/oriented geometry replay,
   finite circle/inversion/cyclic geometry replay, and complex real-pair
   transform replay, plus finite inner-product/projection, finite orthogonal
   transform, and finite
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
   finite probability mass tables now split the PMF/conditioning/Bayes/
   independence/total-variation story
   from the broader finite-probability process bridge. Standalone finite
   operators now split the norm/operator-bound/Chebyshev-prefix story from the broad
   bounded-dynamics/operator bridge. Standalone bounded dynamics now splits
   recurrence traces, finite invariants, and threshold reachability from the
   finite dynamics/Euler bridge, including replay-only bad transition-step, bad
   threshold-step, and bad invariant-bound rows plus separate checked QF_LRA
   proof rows. Standalone finite Euler now splits
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
18. `procurement-scoring-v0` now adds a fourth rules/law pack, reusing finite
   predicate exclusions, bid-cap and deadline arithmetic, bonus-threshold
   witnesses, score monotonicity, and Bool/QF_LIA checked fixtures through the
   current JSON boundary.
   `grant-allocation-v0` now adds the rational-allocation slice with exact
   share replay, budget balance, shelter/clinic floors, administrative caps,
   and QF_LRA/Farkas checked fixtures through the same JSON boundary.
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
    a conditioned non-collider blocking DIMACS artifact and
    `collider-unconditioned-blocks` to an unconditioned-collider blocking DIMACS
    artifact. These Boolean rows are checked by the
    `math_resource_boolean_routes` DRAT/LRAT regression.
    `graph-search-runtime-v0` now links `bad-dfs-cost-bound-rejected` to
    `artifacts/examples/math/graph-search-runtime-v0/smt2/bad-dfs-cost-bound-lia-conflict.smt2`,
    checked by the `math_resource_lia_routes` arithmetic-DPLL regression.
    `finite-flow-cut-v0` adds exact finite directed-flow feasibility,
    cut-capacity optimality replay, malformed capacity rejection, malformed
    flow-value rejection, and a max-flow/min-cut theorem horizon; its later
    `qf-lra-bad-flow-value-cut-bound` promotion adds the source Farkas artifact
    and checked proof route.
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
    `qf-lra-bad-duplicate-node-grid`,
    `qf-lra-bad-interpolation-sample`, and
    `qf-lra-bad-alternating-residual` to source-level QF_LRA/Farkas artifacts,
    checked by the `math_resource_lra_routes` regression while the malformed
    source rows remain exact replay.
    `finite-stochastic-kernels-v0` now links `qf-lra-bad-kernel-row` to
    `artifacts/examples/math/finite-stochastic-kernels-v0/smt2/bad-kernel-row-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
    `finite-ideals-v0` now links
    `qf-uf-bad-ideal-additive-closure` to
    `artifacts/examples/math/finite-ideals-v0/smt2/bad-ideal-additive-closure-conflict.smt2`
    and
    `qf-uf-quotient-ring-representative-alethe` to
    `artifacts/examples/math/finite-ideals-v0/smt2/quotient-ring-representative-congruence-conflict.smt2`,
    checked by the `math_resource_uf_routes` QF_UF/Alethe regression.
    `finite-permutation-groups-v0` now links
    `qf-uf-bad-nonbijection-injectivity` to
    `artifacts/examples/math/finite-permutation-groups-v0/smt2/bad-nonbijection-injectivity-conflict.smt2`,
    checked by the `math_resource_uf_routes` QF_UF/Alethe regression.
    `finite-monoids-v0` now links
    `qf-uf-bad-monoid-associativity` to
    `artifacts/examples/math/finite-monoids-v0/smt2/nonassociative-table-alethe-conflict.smt2`,
    checked by the `math_resource_uf_routes` QF_UF/Alethe regression.
19. `finite-group-actions-v0` now links `qf-uf-bad-identity-action` and
    `qf-uf-bad-action-compatibility` to
    `artifacts/examples/math/finite-group-actions-v0/smt2/bad-identity-action-alethe-conflict.smt2`,
    `artifacts/examples/math/finite-group-actions-v0/smt2/bad-compatibility-action-alethe-conflict.smt2`,
    checked by the `math_resource_uf_routes` QF_UF/Alethe regressions.
20. `finite-continuous-maps-v0` now links `bad-continuous-map-rejected` to
    `artifacts/examples/math/finite-continuous-maps-v0/smt2/bad-preimage-membership-alethe-conflict.smt2`,
    checked by the `math_resource_uf_routes` QF_UF/Alethe regression.
21. `finite-product-measure-v0` now links `bad-product-measure-rejected` to
    `artifacts/examples/math/finite-product-measure-v0/smt2/bad-product-measure-farkas-conflict.smt2`
    and `bad-product-marginal-rejected` to
    `artifacts/examples/math/finite-product-measure-v0/smt2/bad-product-marginal-farkas-conflict.smt2`,
    both checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
22. `finite-random-variables-v0` now links `qf-lra-bad-pushforward` to
    `artifacts/examples/math/finite-random-variables-v0/smt2/bad-pushforward-farkas-conflict.smt2`
    and `qf-lra-bad-expectation-through-pushforward` to
    `artifacts/examples/math/finite-random-variables-v0/smt2/bad-expectation-through-pushforward-farkas-conflict.smt2`,
    both checked by the `math_resource_lra_routes` QF_LRA/Farkas regression;
    the original bad rows remain exact finite replay.
23. `finite-integration-v0` now links `qf-lra-bad-expectation` to
    `artifacts/examples/math/finite-integration-v0/smt2/bad-expectation-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regression; the
    original `bad-expectation-rejected` row remains exact finite replay.
24. `finite-martingales-v0` now keeps `bad-stopped-expectation-rejected` and
    `bad-martingale-rejected` as exact finite replay, and links
    `qf-lra-bad-stopped-expectation` to
    `artifacts/examples/math/finite-martingales-v0/smt2/bad-stopped-expectation-farkas-conflict.smt2`
    and `qf-lra-bad-martingale` to
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
28. `finite-root-finding-v0` now keeps `bad-newton-step-rejected` and
    `bad-bisection-width-rejected` as replay-only source rows, with separate
    checked `qf-lra-bad-newton-step` and `qf-lra-bad-bisection-width` rows
    linking to
    `artifacts/examples/math/finite-root-finding-v0/smt2/bad-newton-step-farkas-conflict.smt2`
    and
    `artifacts/examples/math/finite-root-finding-v0/smt2/bad-bisection-width-farkas-conflict.smt2`,
    checked by the `math_resource_lra_routes` QF_LRA/Farkas regression.
29. `finite-separation-v0` now keeps `bad-convex-combination-point-rejected`
    and `bad-separator-rejected` as replay-only source rows, with separate
    checked `qf-lra-bad-convex-combination-point` and
    `qf-lra-bad-separator` rows linking to
    `artifacts/examples/math/finite-separation-v0/smt2/bad-convex-combination-point-farkas-conflict.smt2`
    and
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
    now groups LU/QR/Cholesky, rank/nullity, residual, projection, Rayleigh/eigenpair,
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
46. [`procurement-scoring-v0`](../rules-as-code/examples/procurement-scoring-v0/)
    now adds debarment, late-submission, bid-cap, score-monotonicity, and
    implementation-equivalence proof fixtures plus generated award and adjacent
    quality-score query rows to the rules/law lane.
47. [`RULES-LAW-QUERIES.md`](RULES-LAW-QUERIES.md) and
    `scripts/query-rules-as-code.py` now add a copyable rules/law query
    surface for pack discovery, checked obligations, generated query families,
    and bounded generated rows; `just rules-as-code` smoke-checks the current
    procurement queries.
48. [`RULES-LAW-PATTERN-MATRIX.md`](RULES-LAW-PATTERN-MATRIX.md) now maps the
    current rules/law patterns back to math concept rows, proof routes, pack
    checks, generated query families, and copyable query commands so the next
    rule pack is gated on distinct proof-shape or consumer demand.
49. [`rules-law-trust-boundary.md`](../learn/rules-law-trust-boundary.md) now
    adds the learner-facing rules/law trust-boundary page, covering source
    rules, formal models, replayed witnesses, checked obligations, and
    legal/theorem horizons for the current packs.
50. [`grant-allocation-v0`](../rules-as-code/examples/grant-allocation-v0/)
    now adds the rational-allocation rules/law slice, with source-linked
    QF_LRA/Farkas fixtures for budget balance, shelter and clinic minimum
    shares, administrative caps, and bounded implementation equivalence plus
    generated bounded allocation and balanced-budget query rows.
48. Functional-analysis/operator field-readiness consumer queries now land in
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and
    `scripts/check-foundational-resources.sh`, covering the Farkas field
    summary, operator bridge lookup, and checked finite-operator,
    inner-product positivity/projection, Chebyshev, spectral, and
    Walsh-Hadamard transform rows without promoting infinite-dimensional theorem
    claims.
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
    `example_packs` membership so LU/QR/Cholesky, residual, rank/nullity, eigenpair,
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
    replay, checked bad-boundary coefficient evidence, and checked
    boundary-square cancellation evidence queryable through
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
    checked bad-boundary coefficient plus boundary-square cancellation evidence
    queryable through topology
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
65. Landed: add the bounded-family/asymptotic boundary bridge row.
    `bridge_bounded_family_asymptotic_boundary` groups finite graph-runtime
    counters, recurrence prefixes, fixed coefficient windows, bounded dynamics,
    and finite Euler rows, with concept-scoped LIA and Farkas checked-row
    queries and theorem-scale runtime/convergence/asymptotic claims kept in the
    Lean-horizon lane.
66. Landed: add the polynomial coefficient/factor replay bridge row.
    `bridge_polynomial_coefficient_factor_replay` groups fixed identities,
    factor/division witnesses, finite coefficient windows, root-finding steps,
    derivative shadows, and rational polynomial-geometry obligations, with
    concept-scoped Diophantine and Farkas checked-row queries and general
    factorization/algebraic-closure claims kept in the Lean-horizon lane.
67. Landed: add the finite countermodel replay bridge row.
    `bridge_finite_countermodel_replay` groups explicit finite universes,
    Boolean assignments, predicate extensions, relation/function tables, and
    finite order/lattice counterexamples under one checked concept-scoped query
    while keeping arbitrary first-order validity and induction schemas in the
    Lean-horizon lane.
68. Landed: add the affine-geometry theorem-boundary page.
    `affine-geometry-theorem-boundary.md` maps exact affine-map, midpoint,
    collinearity, and fixed distance replay plus checked QF_LRA/Farkas bad-row
    evidence to the missing affine-combination, incidence, ratio, projective,
    synthetic, differential, and numerical-geometry theorem routes, with
    pack-specific checked-row and horizon-frontier queries.
69. Landed: add the incidence-geometry theorem-boundary page.
    `incidence-geometry-theorem-boundary.md` maps exact line-equation,
    non-parallel intersection, and point-on-line replay plus checked
    QF_LRA/Farkas bad-row evidence to the missing projective-duality, named
    configuration, synthetic-incidence, algebraic-incidence, and
    numerical-geometry theorem routes, with pack-specific checked-row and
    horizon-frontier queries.
70. Landed: add the rigid-configuration geometry theorem-boundary page.
    `rigid-configuration-geometry-theorem-boundary.md` maps exact triangle
    distance-table, translation-isometry, and congruent-triangle replay plus
    checked QF_LRA/Farkas bad-row evidence to the missing graph-rigidity,
    rigid-motion-classification, synthetic-rigidity, higher-dimensional,
    manifold, and numerical-geometry theorem routes, with pack-specific
    checked-row and horizon-frontier queries.
71. Landed: add the orientation/area geometry theorem-boundary page.
    `orientation-area-geometry-theorem-boundary.md` maps exact signed-area,
    affine determinant area-scaling, barycentric replay, and checked
    QF_LRA/Farkas bad-row evidence to the missing oriented-geometry,
    affine-volume, determinant/Jacobian, change-of-variables,
    differential/manifold, higher-dimensional, and numerical-geometry theorem
    routes, with pack-specific checked-row and horizon-frontier queries.
72. Landed: add the calculus theorem-boundary page.
    `calculus-theorem-boundary.md` maps exact derivative coefficients,
    product-rule/tangent replay, finite Riemann sums, antiderivative endpoint
    replay, gradient/Jacobian/Hessian replay, and checked QF_LRA/Farkas bad-row
    evidence to the missing differentiability, MVT, integrability, FTC,
    inverse/implicit-function, change-of-variables, and manifold-calculus
    theorem routes, with pack-specific checked-row and horizon-frontier queries.
73. Landed: add the convexity theorem-boundary page.
    `convexity-theorem-boundary.md` maps exact midpoint/Jensen replay, finite
    second-difference checks, affine-threshold replay, and checked QF_LRA/Farkas
    bad-row evidence to the missing Jensen, convexity-equivalence, separation,
    duality, KKT/SDP, first-order optimality, nonsmooth, and convergence theorem
    routes, with pack-specific checked-row and horizon-frontier queries.
74. Landed: add the Lebesgue integration theorem-boundary page.
    `lebesgue-integration-theorem-boundary.md` maps exact simple-function
    weighted sums, indicator integrals, finite linearity replay, and checked
    QF_LRA/Farkas bad expectation evidence to the missing Lebesgue integration,
    monotone/dominated convergence, Fubini/Tonelli, almost-everywhere,
    product-measure, and stochastic-integration theorem routes, with
    pack-specific checked-row and horizon-frontier queries.
75. Landed: add the Fubini/Tonelli theorem-boundary page.
    `fubini-tonelli-theorem-boundary.md` maps exact Cartesian-product
    probability table replay, rectangle probabilities, marginal replay, finite
    direct/iterated-sum replay, and checked QF_LRA/Farkas bad product-probability
    and bad marginal evidence to the missing product-measure construction,
    Fubini, Tonelli, section-measurability, sigma-finite, and
    almost-everywhere theorem routes, with pack-specific checked-row and
    horizon-frontier queries.
76. Landed: add the group-action theorem-boundary page.
    `group-action-theorem-boundary.md` maps exact finite action-law replay,
    orbit/stabilizer recomputation, Burnside fixed-point averaging, replay-only
    bad identity/compatibility rejection, and checked QF_UF/Alethe bad
    identity-action/action-compatibility evidence to the missing arbitrary
    group-action, orbit-stabilizer, Burnside/Cauchy-Frobenius, quotient-action,
    transported-structure, Sylow-action, class-equation, and
    representation-theory theorem routes, with pack-specific checked-row and
    horizon-frontier queries.
77. Landed: add the monoid/permutation theorem-boundary page.
    `monoid-permutation-theorem-boundary.md` maps exact finite
    transformation-monoid replay, units/idempotents, `S3` permutation replay,
    cycle/sign replay, natural-action orbit/stabilizer replay, replay-only bad
    associativity/nonbijection rejection, and checked QF_UF/Alethe
    associativity/injectivity evidence to the missing semigroup, monoid,
    quotient/free/presentation, Green's-relation, Cayley, conjugacy, Sylow,
    alternating-group, and representation-theory theorem routes, with
    pack-specific checked-row and horizon-frontier queries.
78. Landed: add the conditional-expectation theorem-boundary page.
    `conditional-expectation-theorem-boundary.md` maps finite partition
    averages, total-expectation replay, nested-partition tower replay,
    conditional variance decomposition, and checked QF_LRA/Farkas bad
    high-block, total-expectation, tower, and variance rows to the missing
    Radon-Nikodym, general conditional-expectation, regular conditional
    probability, martingale, stopping-time, and disintegration theorem routes,
    with pack-specific checked-row and horizon-frontier queries.
79. Landed: add the chain-complex torsion theorem-boundary page.
    `chain-complex-torsion-theorem-boundary.md` maps finite free abelian
    chain-complex replay, one-entry Smith diagonal/torsion replay,
    torsion-generator replay, checked bad-boundary divisibility replay, and
    QF_LIA/Diophantine `2*k = 1` evidence to the missing general Smith normal
    form, finitely-generated-abelian-group classification, quotient-module,
    universal-coefficient, Ext/Tor, exact-sequence, chain-homotopy, and
    topological-invariance theorem routes, with pack-specific checked-row and
    horizon-frontier queries.
80. Landed: promote the finite flow/cut cut-bound row.
    `finite-flow-cut-v0` now has `qf-lra-bad-flow-value-cut-bound`, a
    source-linked QF_LRA/Farkas artifact for the final exact-rational
    contradiction `4 <= 3`. The finite replay rows still compute feasibility,
    conservation, and cut capacity; only the isolated cut-bound conflict is
    promoted as solver-reuse evidence.
81. Landed: promote the finite shortest-path potential-bound row.
    `finite-shortest-path-v0` now has
    `qf-lra-bad-shorter-distance-potential-bound`, a source-linked
    QF_LRA/Farkas artifact for the final exact-rational contradiction
    `5 <= 4`. The finite replay rows still compute path length, edge
    relaxations, and the potential lower bound; only the isolated
    potential-bound conflict is promoted as solver-reuse evidence.
82. Landed: promote the finite DAG topological edge-order row.
    `finite-dag-topological-order-v0` now has
    `qf-lia-bad-topological-edge-order`, a source-linked QF_LIA artifact for
    the final exact-integer contradiction `2 < 1`. The finite replay rows still
    compute vertex coverage, edge positions, and cycle obstructions; only the
    isolated edge-order conflict is promoted as solver-reuse evidence.
83. Landed: add the finite QR decomposition resource.
    `finite-qr-decomposition-v0` now records an exact rational orthogonal
    matrix `Q`, upper-triangular `R`, and product `Q*R = A`, plus a checked
    QF_LRA/Farkas artifact for the malformed bottom-right product-entry claim
    `2/5 = 1/2`. The reused matrix-factorization bridge keeps exact finite
    replay separate from general QR existence, algorithm, conditioning, and
    stability theorem claims.
84. Landed: add the finite Cholesky decomposition resource.
    `finite-cholesky-decomposition-v0` now records an exact rational
    lower-triangular matrix `L`, positive diagonal entries, leading principal
    minors, and product `L*L^T = A`, plus a checked QF_LRA/Farkas artifact for
    the malformed bottom-right product-entry claim `10 = 9`. The reused
    matrix-factorization bridge keeps exact finite replay separate from
    general Cholesky existence, algorithm correctness, conditioning, and
    stability theorem claims.
85. Landed: add the finite covariance matrix resource.
    `finite-covariance-matrix-v0` now records exact finite sample rows, the
    mean vector, centered rows, the centered Gram matrix, the covariance
    matrix, and a two-by-two positive-semidefinite shadow, plus a checked
    QF_LRA/Farkas artifact for the malformed off-diagonal covariance claim
    `4/9 = 1/2`. The reused finite-moment and inner-product bridges keep exact
    finite replay separate from covariance-estimator consistency, PCA,
    random-matrix asymptotics, and floating-point covariance algorithms.
86. Landed: add the finite Newton-step resource.
    `finite-newton-step-v0` now records one exact two-variable quadratic
    Newton step, including gradient/Hessian replay, positive leading minors,
    Hessian inverse, Newton direction, stationary next point, objective
    decrease, and a checked QF_LRA/Farkas artifact for the malformed
    next-coordinate claim `10/7 = 3/2`. The reused derivative, convexity, and
    residual bridges keep exact finite replay separate from Newton
    convergence, globalization, trust-region, conditioning, and floating-point
    stability claims.
87. Landed: add the finite condition-number resource.
    `finite-condition-number-v0` now records one exact diagonal rational
    matrix inverse, infinity-norm condition number, perturbation-bound shadow,
    replay-only bad condition-number bound, and a checked QF_LRA/Farkas
    artifact for the malformed claim `kappa_infinity(A) <= 5`. The reused
    residual and exact-vs-floating bridges keep exact finite replay separate
    from algorithmic stability, singular-value theory, pseudospectra, and
    floating-point roundoff.
88. Landed: add the finite singular-value shadow resource.
    `finite-singular-value-shadow-v0` now records one exact diagonal rational
    matrix, `A^T A`, singular-vector equations, SVD reconstruction,
    spectral/Frobenius norms, a two-norm condition number, and a checked
    QF_LRA/Farkas artifact for the malformed claim `sigma_max(A) <= 2`. The
    reused eigenpair, inner-product, operator, and exact-vs-floating bridges
    keep exact finite replay separate from the general SVD theorem,
    perturbation theory, pseudospectra, rank-revealing algorithms, and
    floating-point SVD stability.
89. Landed: add the finite Jordan-chain resource.
    `finite-jordan-chain-v0` now records one exact non-diagonal Jordan block,
    its eigenvector, generalized eigenvector, nilpotent part, similarity
    reconstruction, and a checked QF_LRA/Farkas artifact for the malformed
    nilpotent-component claim. The reused eigenpair, characteristic-polynomial,
    and operator bridges keep exact finite replay separate from Jordan normal
    form, diagonalizability, multiplicity theorems, and numerical eigensolver
    claims.
90. Landed: add the finite Schur-complement resource.
    `finite-schur-complement-v0` now records one exact two-by-two block matrix,
    the leading-block inverse, one-by-one Schur complement, determinant
    factorization, two-sided inverse, positive-definite shadow, conditional
    variance shadow, and a checked QF_LRA/Farkas artifact for the malformed
    scalar claim `S = 3/2`. The new Schur bridge keeps exact finite block replay
    separate from general Schur-complement, block-inverse,
    Gaussian-elimination, pivoting, SDP, statistical-conditioning, and
    numerical-stability theorems.
91. Landed: add the finite Gaussian-elimination resource.
    `finite-gaussian-elimination-v0` now records one exact pivot multiplier,
    augmented row operation, determinant pivot product, and back-substitution
    transcript, plus a checked QF_LRA/Farkas artifact for the malformed
    eliminated-RHS claim `7 = 8`. The reused matrix-factorization bridge keeps
    exact finite transcript replay separate from general elimination
    correctness, pivoting, rank-revealing variants, sparse fill-in,
    conditioning, and floating-point stability.
92. Landed: add the finite power-iteration resource.
    `finite-power-iteration-v0` now records one exact diagonal rational matrix,
    two power steps, a normalized iterate, Rayleigh quotient, residual shadow,
    dominant eigenpair shadow, and a checked QF_LRA/Farkas artifact for the
    malformed second-iterate coordinate claim `4 = 3`. The reused eigenpair,
    residual-bound, and exact-vs-floating bridges keep exact finite spectral
    iteration replay separate from convergence theorems, spectral-gap
    assumptions, residual-to-eigenvalue error bounds, deflation, block
    iteration, conditioning, and floating-point eigensolver stability.
93. Landed: add the finite conjugate-gradient resource.
    `finite-conjugate-gradient-v0` now records one exact two-by-two SPD system,
    two CG steps, residual orthogonality, A-conjugacy, exact solution replay,
    and a checked QF_LRA/Farkas artifact for the malformed first-step-size
    claim `1/4 = 1/3`. The reused residual-bound, rational-convexity, and
    exact-vs-floating bridges keep exact finite CG replay separate from
    convergence, finite termination, Krylov minimization, preconditioning,
    roundoff, and floating-point stability.
94. Landed: add the finite Arnoldi-iteration resource.
    `finite-arnoldi-iteration-v0` now records one exact two-by-two Krylov
    transcript: `A = [[1,2],[3,4]]`, `q1 = [1,0]`, the first projection and
    residual, `h21 = 3`, `q2 = [0,1]`, the second projection column, an
    orthonormal basis, and `A*Q = Q*H`. It includes a checked
    QF_LRA/Farkas artifact for the malformed subdiagonal coefficient claim
    `h21 = 2`. The reused residual-bound, eigenpair, inner-product,
    finite-operator/Chebyshev, and exact-vs-floating bridges keep exact finite
    Arnoldi replay separate from GMRES convergence, Ritz-value theory,
    restart/reorthogonalization strategies, and floating-point stability.
95. Landed: add the finite Lanczos-iteration resource.
    `finite-lanczos-iteration-v0` now records one exact two-by-two symmetric
    Krylov transcript: `A = [[2,1],[1,2]]`, `q1 = [1,0]`, the first
    alpha/beta step, `beta1 = 1`, `q2 = [0,1]`, the second alpha step,
    exact termination residual, an orthonormal basis, and `A*Q = Q*T` for the
    symmetric tridiagonal `T`. It includes a checked QF_LRA/Farkas artifact
    for the malformed off-diagonal coefficient claim `beta1 = 2`. The reused
    residual-bound, eigenpair, inner-product, finite-operator/Chebyshev, and
    exact-vs-floating bridges keep exact finite Lanczos replay separate from
    convergence, Ritz-value theory, breakdown/restart behavior,
    finite-precision loss of orthogonality, and floating-point stability.
96. Landed: add the finite Givens-rotation resource.
    `finite-givens-rotation-v0` now records one exact rational orthogonal
    zeroing transform: `c = 3/5`, `s = 4/5`,
    `G = [[3/5,4/5],[-4/5,3/5]]`, `G^T*G = I`, `G*[3,4] = [5,0]`,
    inverse reconstruction, determinant `1`, and norm preservation. It
    includes a checked QF_LRA/Farkas artifact for the malformed sine
    coefficient claim `s = 3/5`. The reused matrix, inner-product,
    finite-operator/Chebyshev, and exact-vs-floating bridges keep exact finite
    Givens replay separate from QR algorithms, pivoting, conditioning, and
    floating-point stability.
97. Landed: add the finite Householder-reflection resource.
    `finite-householder-reflection-v0` now records one exact rational
    reflector-formula transcript: `v = [2,1]`, `v^T*v = 5`,
    `H = [[-3/5,-4/5],[-4/5,3/5]]`, `H^T = H`, `H^T*H = I`,
    `H*[3,4] = [-5,0]`, involution, determinant `-1`, and norm
    preservation. It includes a checked QF_LRA/Farkas artifact for the
    malformed top-left entry claim `H[0,0] = -4/5`. The reused matrix,
    inner-product, finite-operator/Chebyshev, and exact-vs-floating bridges
    keep exact finite Householder replay separate from QR algorithms,
    pivoting, conditioning, and floating-point stability.
98. Landed: add the finite Gram-Schmidt resource.
    `finite-gram-schmidt-v0` now records one exact rational orthogonalization
    transcript: `a1 = [3,4]`, `a2 = [1,0]`, `q1 = [3/5,4/5]`,
    `r12 = 3/5`, residual `[16/25,-12/25]`, `q2 = [4/5,-3/5]`,
    orthonormality, upper-triangular `R`, and `Q*R = A`. It includes a
    checked QF_LRA/Farkas artifact for the malformed projection coefficient
    claim `r12 = 4/5`. The reused matrix, inner-product,
    finite-operator/Chebyshev, and exact-vs-floating bridges keep exact finite
    Gram-Schmidt replay separate from QR correctness, rank-deficient variants,
    conditioning, and floating-point stability.
99. Landed: add the finite LU-decomposition resource.
    `finite-lu-decomposition-v0` now records one exact rational factorization
    transcript: `A = [[2,1],[4,5]]`, `L = [[1,0],[2,1]]`,
    `U = [[2,1],[0,3]]`, `L*U = A`, determinant pivot product `6`,
    triangular solve replay for `b = [5,17]`, and solution `[4/3,7/3]`.
    It includes a checked QF_LRA/Farkas artifact for the malformed multiplier
    claim `l21 = 3`. The reused matrix and exact-vs-floating bridges keep
    exact finite LU replay separate from general LU existence, pivoting,
    rank-deficient variants, sparse algorithms, conditioning, and
    floating-point stability.
100. Landed: add the finite pivoted-LU-decomposition resource.
    `finite-pivoted-lu-decomposition-v0` now records one exact rational
    row-swapped factorization transcript: `A = [[1,2],[3,4]]`,
    `P = [[0,1],[1,0]]`, `P*A = [[3,4],[1,2]]`,
    `L = [[1,0],[1/3,1]]`, `U = [[3,4],[0,2/3]]`,
    determinant-sign accounting `det(P) * det(A) = product(pivots) = 2`,
    triangular solve replay for `b = [3,7]`, and solution `[1,1]`.
    It includes a checked QF_LRA/Farkas artifact for the malformed pivot-sign
    claim `det(P) = +1`. The reused matrix and exact-vs-floating bridges keep
    exact finite pivoted-LU replay separate from pivot-selection correctness,
    rank-deficient behavior, sparse pivoting, growth-factor bounds,
    conditioning, and floating-point stability.
101. Landed: add the finite LDLT-decomposition resource.
    `finite-ldlt-decomposition-v0` now records one exact rational
    positive-definite factorization transcript: `A = [[4,2],[2,3]]`,
    `L = [[1,0],[1/2,1]]`, `D = [[4,0],[0,2]]`,
    `L*D*L^T = A`, determinant/product replay
    `det(A) = product(diag(D)) = 8`, positive leading minors `[4,8]`,
    triangular solve replay for `b = [6,5]`, and solution `[1,1]`.
    It includes a checked QF_LRA/Farkas artifact for the malformed diagonal
    claim `D[1,1] = 3`. The reused matrix and exact-vs-floating bridges keep
    exact finite LDLT replay separate from LDLT existence, pivoting strategy
    correctness, indefinite variants, sparse algorithms, conditioning, and
    floating-point stability.
102. Landed: add the finite orthogonal-diagonalization resource.
    `finite-orthogonal-diagonalization-v0` now records one exact rational
    spectral-theorem shadow: `Q = [[3/5,4/5],[-4/5,3/5]]`,
    `D = diag(1,4)`, `A = Q*D*Q^T`,
    `Q^T*Q = I`, column eigenpair replay, trace/eigenvalue-sum replay,
    and determinant/eigenvalue-product replay. It includes a checked
    QF_LRA/Farkas artifact for the malformed eigenvalue claim
    `lambda_1 = 5`. The reused eigenpair and exact-vs-floating bridges keep
    exact finite orthogonal diagonalization separate from the spectral theorem,
    diagonalization criteria, multiplicity theory, eigensolver convergence,
    perturbation bounds, and floating-point stability.
103. Landed: add the finite real-Schur decomposition resource.
    `finite-real-schur-decomposition-v0` now records one exact rational
    real-Schur shadow: `Q = [[3/5,4/5],[-4/5,3/5]]`,
    `T = [[1,2],[0,4]]`, `A = Q*T*Q^T`,
    `Q^T*Q = I`, `A*Q = Q*T`, trace/diagonal-sum replay,
    and determinant/diagonal-product replay. It includes a checked
    QF_LRA/Farkas artifact for the malformed superdiagonal claim
    `T[0,1] = 3`. The reused eigenpair and exact-vs-floating bridges keep
    exact finite real-Schur replay separate from the general Schur theorem,
    eigenvalue ordering, QR-iteration convergence, perturbation bounds, and
    floating-point stability.
104. Landed: add the finite polar-decomposition resource.
    `finite-polar-decomposition-v0` now records one exact rational polar
    shadow: `U = [[3/5,4/5],[-4/5,3/5]]`,
    `P = [[2,0],[0,5]]`, `A = U*P`,
    `U^T*U = I`, `A^T*A = P^2`, trace/diagonal replay, and
    determinant/product replay. It includes a checked QF_LRA/Farkas artifact
    for the malformed diagonal claim `P[1,1] = 4`. The reused eigenpair and
    exact-vs-floating bridges keep exact finite polar replay separate from
    polar theorem, partial-isometry variants, square-root functional calculus,
    iterative algorithms, perturbation bounds, and floating-point stability.
105. Landed: add the finite QR-iteration-step resource.
    `finite-qr-iteration-step-v0` now records one exact rational unshifted QR
    step: `Q = [[3/5,4/5],[-4/5,3/5]]`, `R = [[5,2],[0,1]]`,
    `A0 = Q*R`, `A1 = R*Q = Q^T*A0*Q`, trace replay
    `trace(A0) = trace(A1) = 2`, and determinant replay
    `det(A0) = det(A1) = 5`. It includes a checked QF_LRA/Farkas artifact for
    the malformed next-step entry claim `A1[0,0] = 2`. The reused eigenpair
    and exact-vs-floating bridges keep exact finite QR-step replay separate
    from QR-iteration convergence, shifted/deflated variants, Schur theorem
    reconstruction, loss-of-orthogonality analysis, and floating-point
    eigensolver stability.
106. Landed: add the finite shifted-QR-step resource.
    `finite-shifted-qr-step-v0` now records one exact rational shifted QR
    step with `mu = 1`: `A0 - mu*I = Q*R`, `A1 = R*Q + mu*I`,
    `A1 = Q^T*A0*Q`, trace replay `trace(A0) = trace(A1) = 4`, and
    determinant replay `det(A0) = det(A1) = 8`. It includes a checked
    QF_LRA/Farkas artifact for the malformed shifted next-step entry claim
    `A1[1,1] = 2`. The reused eigenpair and exact-vs-floating bridges keep
    exact finite shifted-QR replay separate from shift-selection theory,
    deflation, QR convergence, Schur theorem reconstruction,
    loss-of-orthogonality analysis, and floating-point eigensolver stability.
107. Landed: add the finite rounding-shadow resource.
    `finite-rounding-shadow-v0` now records one exact rational
    exact-vs-rounded transcript: `x = 1`, `y = 1/10000`,
    `exact_delta = (x + y) - x = 1/10000`, fixed three-decimal scale
    `1000`, `round3(x + y) - round3(x) = 0`, nearest-grid residual replay,
    and the exact difference between the rational and rounded increments. It
    includes a checked QF_LRA/Farkas artifact for the malformed equality claim
    `exact_delta = rounded_delta`. The exact-vs-floating bridge keeps this
    fixed rational rounding shadow separate from IEEE floating-point semantics,
    rounding-mode theory, accumulation-error bounds, and numerical-stability
    theorems.
108. Landed: add the finite interval-arithmetic-shadow resource.
    `finite-interval-arithmetic-shadow-v0` now records one exact rational closed
    interval transcript: `X = Y = [1, 10001/10000]`, endpoint-wise interval
    sum/product replay, interval widths, and the second-order product-width
    term. It includes a checked QF_LRA/Farkas artifact for the malformed shortcut
    claim `product_upper <= 5001/5000`. The rational-interval and
    exact-vs-floating bridges keep this fixed rational interval shadow separate
    from general interval analysis, dependency management, floating-point
    outward rounding, QF_FP semantics, and numerical-stability theorems.
109. Landed: add the finite Cauchy-Riemann-shadow resource.
    `finite-cauchy-riemann-shadow-v0` now records one exact complex polynomial
    transcript: `f(z)=z^2` at `z=1+2i`, real-pair square `-3+4i`, component
    polynomials `u=x^2-y^2` and `v=2xy`, fixed partial derivatives,
    Cauchy-Riemann equalities, and derivative `2+4i`. It includes a checked
    QF_LRA/Farkas artifact for the malformed claim
    `real(f'(1+2i)) = 3`. The complex real-pair and derivative-shadow bridges
    keep this fixed polynomial shadow separate from general holomorphicity,
    Cauchy-Riemann theorem schemas, residues, contour integration, and analytic
    continuation.
110. Landed: add the finite GMRES residual-shadow resource.
    `finite-gmres-residual-shadow-v0` now records one exact rational one-step
    GMRES transcript: `A=[[2,1],[1,2]]`, `b=[1,0]`, `x0=[0,0]`,
    `r0=[1,0]`, Krylov direction `A*r0=[2,1]`, residual-minimizing
    coefficient `alpha=2/5`, residual `[1/5,-2/5]`, residual orthogonality,
    and residual-norm decrease. It includes a checked QF_LRA/Farkas artifact
    for the malformed claim `alpha=1/2`. The residual-bound,
    finite-operator/Krylov, and inner-product/projection bridges keep this
    fixed exact row separate from general GMRES convergence, restart,
    preconditioner, breakdown, nonnormal, and floating-point stability
    theorems.
111. Landed: add the finite Runge-Kutta midpoint resource.
    `finite-runge-kutta-midpoint-v0` now records one exact RK2 midpoint
    transcript for `y' = 2t`, `y(0)=0`, and `h=1/2`, including midpoint
    stages, exact states `[0, 1/4, 1, 9/4]`, and zero error. It includes a
    checked QF_LRA/Farkas artifact for the malformed first-step claim `1/2`
    against exact `1/4`. The finite dynamics/time-stepping bridge keeps this
    fixed exact row separate from general Runge-Kutta order, convergence,
    stability, stiffness, and adaptive-step theorems.
112. Landed: add the finite Heun method resource.
    `finite-heun-method-v0` now records one exact explicit trapezoidal RK2
    transcript for `y' = 2t`, `y(0)=0`, and `h=1/2`, including predictor
    states, endpoint derivatives, averaged slopes, exact states
    `[0, 1/4, 1, 9/4]`, and zero error. It includes a checked QF_LRA/Farkas
    artifact for the malformed first-step claim `1/2` against exact `1/4`.
    The finite dynamics/time-stepping bridge keeps this fixed exact row
    separate from general RK2 order, convergence, stability, stiffness, and
    adaptive-step theorems.
113. Landed: add the finite Backward Euler method resource.
    `finite-backward-euler-method-v0` now records one exact implicit
    backward Euler transcript for `y' = -y`, `y(0)=1`, and `h=1/2`,
    including endpoint derivatives, zero implicit residuals, geometric decay
    ratio `2/3`, and states `[1, 2/3, 4/9, 8/27]`. It includes a checked
    QF_LRA/Farkas artifact for the malformed first-step claim `1/2` against
    exact `2/3`. The finite dynamics/time-stepping bridge keeps this fixed
    exact row separate from general backward Euler convergence, A-stability,
    stiffness, nonlinear solves, adaptive-step methods, floating-point
    implementations, and PDE time-integration theorems.
114. Landed: add the finite Crank-Nicolson method resource.
    `finite-crank-nicolson-method-v0` now records one exact implicit trapezoid
    transcript for `y' = -y`, `y(0)=1`, and `h=1/2`, including start
    derivatives, endpoint derivatives, averaged slopes, zero implicit
    residuals, geometric decay ratio `3/5`, and states
    `[1, 3/5, 9/25, 27/125]`. It includes a checked QF_LRA/Farkas artifact for
    the malformed first-step claim `1/2` against exact `3/5`. The finite
    dynamics/time-stepping bridge keeps this fixed exact row separate from
    general Crank-Nicolson order, convergence, A-stability, stiffness,
    nonlinear solves, adaptive-step methods, floating-point implementations,
    and PDE time-integration theorems.
115. Landed: add the finite Adams-Bashforth method resource.
    `finite-adams-bashforth-method-v0` now records one exact explicit two-step
    multistep transcript for `y' = 2t`, `y(0)=0`, and `h=1/2`, including exact
    starter `y_1=1/4`, derivative history, Adams-Bashforth slopes
    `[3/2, 5/2]`, exact states `[0, 1/4, 1, 9/4]`, and zero error. It includes
    a checked QF_LRA/Farkas artifact for the malformed first multistep claim
    `3/4` against exact `1`. The finite dynamics/time-stepping bridge keeps
    this fixed exact row separate from general Adams-Bashforth order,
    convergence, stability regions, variable-step methods, floating-point
    implementations, and PDE time-integration theorems.
116. Landed: add the finite BDF2 method resource.
    `finite-bdf2-method-v0` now records one exact implicit two-step multistep
    transcript for `y' = -y`, `y(0)=1`, and `h=1/2`, including backward-Euler
    starter `y_1=2/3`, endpoint derivatives `[-5/12, -1/4]`, zero implicit
    residuals, exact states `[1, 2/3, 5/12, 1/4]`, and strict monotone decay.
    It includes a checked QF_LRA/Farkas artifact for the malformed first
    multistep claim `1/3` against exact `5/12`. The finite
    dynamics/time-stepping bridge keeps this fixed exact row separate from
    general BDF2 order, convergence, zero-stability, nonlinear solves,
    variable-step methods, floating-point implementations, and PDE
    time-integration theorems.
117. Landed: add the finite Simpson-rule resource.
    `finite-simpson-rule-v0` now records exact single-panel Simpson quadrature
    transcripts for `x^3` and `1+x^2` on `[0,2]`, including nodes `[0,1,2]`,
    weights `[1,4,1]`, sample values, weighted sums, Simpson values `4` and
    `14/3`, and exact polynomial integrals. It includes a checked
    QF_LRA/Farkas artifact for the malformed cubic quadrature claim `7/2`
    against exact `4`. The integration-horizon bridge keeps this fixed exact
    row separate from general Simpson exactness, composite/adaptive
    quadrature convergence, error bounds, floating-point quadrature
    correctness, and numerical stability.
118. Landed: add the finite divided-differences resource.
    `finite-divided-differences-v0` now records exact Newton interpolation
    transcripts for `1+x^2` at nodes `0,1,2` and `x^3` at nodes `0,1,2,3`,
    including divided-difference tables, Newton coefficients, basis products,
    terms, and interpolation values `10` and `64`. It includes a checked
    QF_LRA/Farkas artifact for the malformed interpolation claim `9` against
    exact `10`. The polynomial replay bridge keeps this fixed exact row
    separate from general interpolation uniqueness, error estimates,
    node-choice conditioning, spline theory, floating-point interpolation
    correctness, and numerical stability.
119. Landed: add the finite barycentric interpolation resource.
    `finite-barycentric-interpolation-v0` now records exact barycentric
    interpolation transcripts for `1+2*x` and `x^2`, including weights,
    regular numerator/denominator terms, values `3` and `4`, and an explicit
    node-hit value `1`. It includes a checked QF_LRA/Farkas artifact for the
    malformed barycentric claim `5` against exact `4`. The polynomial replay
    bridge keeps this fixed exact row separate from barycentric/Lagrange/Newton
    equivalence, interpolation uniqueness, error estimates, node-choice
    conditioning, Runge phenomena, spline theory, floating-point interpolation
    correctness, and numerical stability.
120. Landed: add the finite difference derivative resource.
    `finite-difference-derivatives-v0` now records exact finite-difference
    derivative transcripts for a forward affine first derivative, a central
    quadratic first derivative, and a central quadratic second derivative,
    including stencil offsets, weights, sample values, weighted sums, scale,
    and exact symbolic derivative values. It includes a checked QF_LRA/Farkas
    artifact for the malformed finite-difference claim `5` against exact `4`.
    The derivative bridge keeps this fixed exact row separate from
    truncation-error, convergence-order, stability, boundary-stencil, PDE,
    automatic-differentiation, and floating-point finite-difference theory.
121. Landed: add the finite Taylor polynomial resource.
    `finite-taylor-polynomials-v0` now records exact Taylor-polynomial
    transcripts for a quadratic at center `1`, a cubic at center `0`, and a
    degree-1 truncated linearization, including derivative values,
    factorials, Taylor coefficients, basis powers, Taylor values, polynomial
    values, and the exact truncated remainder `1/4`. It includes a checked
    QF_LRA/Farkas artifact for the malformed Taylor-value claim `6` against
    exact `25/4`. The derivative and polynomial bridges keep this fixed exact
    row separate from Taylor theorem hypotheses, remainder bounds, analytic
    convergence, multivariable Taylor theory, and floating-point Taylor
    evaluation.
122. Landed: add the finite cubic Hermite interpolation resource.
    `finite-cubic-hermite-interpolation-v0` now records exact endpoint
    value/slope interpolation transcripts for smoothstep, unit-interval
    quadratic, and nonunit-interval quadratic rows, including Hermite basis
    values, interval-length scaled derivative terms, endpoint constraints, and
    polynomial values. It includes a checked QF_LRA/Farkas artifact for the
    malformed Hermite-value claim `2` against exact `7/4`. The derivative and
    polynomial bridges keep this fixed exact row separate from Hermite
    uniqueness, error estimates, spline assembly, shape-preservation,
    monotonicity, and floating-point Hermite evaluation.
123. Landed: add the finite natural cubic spline interpolation resource.
    `finite-cubic-spline-interpolation-v0` now records exact two-piece natural
    cubic spline transcripts through knots `0, 1, 2` with values `0, 1, 0`,
    including piece polynomials, knot values, C1/C2 interior continuity,
    natural endpoint second derivatives, and midpoint values `11/16`. It
    includes a checked QF_LRA/Farkas artifact for the malformed spline-value
    claim `3/4` against exact `11/16`. The derivative and polynomial bridges
    keep this fixed exact row separate from general spline existence,
    uniqueness, error, convergence, knot-selection, shape-preservation, and
    floating-point spline evaluation.
124. Landed: add the finite Romberg extrapolation resource.
    `finite-romberg-extrapolation-v0` now records exact one-step
    Romberg/Richardson extrapolation transcripts from one-panel and two-panel
    composite trapezoid rows for `x^2` and `x^4` on `[0,1]`, including exact
    extrapolated values, quadratic error cancellation, and the quartic
    residual. It includes a checked QF_LRA/Farkas artifact for the malformed
    extrapolated-value claim `1/4` against exact `1/3`. The integration,
    exact-vs-floating, calculus, and numerical-analysis bridges keep this
    fixed exact row separate from general Romberg/Richardson convergence,
    asymptotic error expansions, adaptive quadrature, floating-point
    quadrature correctness, and numerical stability.
125. Landed: add the finite ridge regression resource.
    `finite-ridge-regression-v0` now records exact lambda-one regularized
    normal-equation replay for a three-row rational dataset, coefficient
    shrinkage, residual and penalty arithmetic, and regularized-objective
    comparison against ordinary least squares. It includes a checked
    QF_LRA/Farkas artifact for the malformed coefficient claim `beta0 = 1`
    against exact `4/5`. The residual-bound, inner-product/projection,
    exact-vs-floating, statistics, optimization, and numerical-analysis
    bridges keep this fixed exact row separate from general ridge theory,
    cross-validation, model selection, floating-point solvers, and statistical
    guarantees.
126. Landed: add the finite linear-discriminant resource.
    `finite-linear-discriminant-v0` now records exact two-class rational
    means, centered rows, within-class scatter, Fisher direction, projected
    scores, threshold margins, and finite Fisher ratio. It includes a checked
    QF_LRA/Farkas artifact for the malformed direction claim `wy = 1` against
    exact `3/2`. The finite-linear-discriminant, inner-product/projection,
    exact-vs-floating, statistics, optimization, and numerical-analysis
    bridges keep this fixed exact row separate from Fisher LDA theory,
    Gaussian classifier assumptions, Bayes risk, multiclass or regularized
    LDA, floating-point classifiers, and statistical guarantees.
127. Landed: add the finite principal-components resource.
    `finite-principal-components-v0` now records exact finite centering,
    covariance, principal/secondary eigenpairs, projected scores,
    one-component reconstruction, residual energy, and explained-variance
    ratio for a four-row rational sample. It includes a checked QF_LRA/Farkas
    artifact for the malformed principal-eigenvalue claim `lambda = 3/2`
    against exact `2`. The finite-PCA, eigenpair, inner-product/projection,
    exact-vs-floating, statistics, optimization, and numerical-analysis
    bridges keep this fixed exact row separate from PCA/SVD optimality,
    best-rank approximation, estimator consistency, randomized algorithms,
    perturbation theory, floating-point PCA, and statistical guarantees.
128. Revisit crate/repo boundaries only after three real consumers or repeated
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
