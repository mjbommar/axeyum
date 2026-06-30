# Foundational Resource Expansion

This folder plans a broader sibling-resource ecosystem for foundational
mathematics, computer science, logic, and statistics.

It extends the existing [formal mathematics curriculum](../curriculum/README.md)
without replacing it. The curriculum remains the current machine-readable math
DAG; this folder is the expansion plan for adjacent resource families,
schemas, examples, and validation workflows.

## Files

- [SOURCES.md](SOURCES.md) records the web, GitHub, and shallow-clone research
  used to ground the plan.
- [MATH-FIELDS.md](MATH-FIELDS.md) defines the university-style mathematics
  field taxonomy that seeds the Foundational Concept Atlas.
- [MATH-CURRICULUM-BUILDOUT.md](MATH-CURRICULUM-BUILDOUT.md) is the detailed
  buildout plan from the current curriculum DAG to atlas rows, example packs,
  lessons, proof hooks, dashboards, and eventual library boundaries.
- [MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md](MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md)
  is the commit-sized build matrix for every curriculum node, math field,
  resource gate, and proof route.
- [CURRICULUM-RESOURCE-EXECUTION-PLAN.md](CURRICULUM-RESOURCE-EXECUTION-PLAN.md)
  is the forward execution plan for moving those resources from validated packs
  into learner paths, proof upgrades, solver feedback, and eventual consumer
  boundaries.
- [PROOF-UPGRADE-FRONTIER.md](PROOF-UPGRADE-FRONTIER.md) turns the generated
  proof-upgrade queue into a route-by-route execution plan for checked
  evidence, Lean horizons, and trust-boundary graduation.
- [LIBRARY-BOUNDARY-DECISION.md](LIBRARY-BOUNDARY-DECISION.md) records the
  current Phase M8 decision: keep the resources in-repo, expose a stable JSON
  data contract, and defer crates or repo splits until real consumers require
  them.
- [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) gives copyable sample queries over
  the committed JSON data contract for pack discovery, checked-row mining,
  solver-reuse rows, and atlas concept lookup.
- [ROADMAP.md](ROADMAP.md) is the implementation roadmap.
- [../learn/math/README.md](../learn/math/README.md) is the learner-facing
  math path built from the curriculum, concept atlas, and validated packs.
- [generated/math-coverage.md](generated/math-coverage.md) is generated
  curriculum-node coverage from the current concept atlas.
- [generated/math-field-dashboard.md](generated/math-field-dashboard.md) is
  generated field coverage from the current concept atlas.
- [generated/proof-gap-dashboard.md](generated/proof-gap-dashboard.md) is the
  generated proof/evidence gap view.
- [generated/learner-proof-upgrade-dashboard.md](generated/learner-proof-upgrade-dashboard.md)
  is the generated learner-coverage and proof-upgrade queue.

## Current Machine-Readable Artifacts

- [`artifacts/ontology/foundational-concepts.schema.json`](../../artifacts/ontology/foundational-concepts.schema.json)
  defines the seed concept-atlas row shape.
- [`artifacts/ontology/foundational-concepts.json`](../../artifacts/ontology/foundational-concepts.json)
  currently contains curriculum, math-field, bridge-concept, and example-family
  rows generated from the current resource data.
- [`scripts/gen-foundational-concepts.py`](../../scripts/gen-foundational-concepts.py)
  regenerates the seed atlas from the curriculum DAG and field/buildout maps.
- [`scripts/validate-foundational-concepts.py`](../../scripts/validate-foundational-concepts.py)
  validates row shape, curriculum alignment, field IDs, links, and proof/pack
  metadata.
- [`scripts/gen-foundational-dashboards.py`](../../scripts/gen-foundational-dashboards.py)
  regenerates the Markdown dashboards under `generated/`.
- [`scripts/consume-foundational-resources.py`](../../scripts/consume-foundational-resources.py)
  is a dependency-free downstream-consumer smoke test for the public atlas and
  example-pack JSON contract.
- [`scripts/query-foundational-resources.py`](../../scripts/query-foundational-resources.py)
  is a dependency-free consumer query helper for common pack, check, and concept
  lookups over the same committed JSON contract.
- [`artifacts/ontology/foundational-example-pack.schema.json`](../../artifacts/ontology/foundational-example-pack.schema.json)
  defines the example-pack metadata and expected-result shape.
- [`scripts/validate-foundational-example-pack.py`](../../scripts/validate-foundational-example-pack.py)
  validates foundational math example-pack folders.
- [`artifacts/examples/math/template-v0/`](../../artifacts/examples/math/template-v0/)
  is the validating template for future math packs.
- [`artifacts/examples/math/logic-basics-v0/`](../../artifacts/examples/math/logic-basics-v0/)
  validates propositional SAT witness replay, tautology/contradiction
  truth-table checks, De Morgan equivalence, and a tiny CNF refutation by
  enumeration.
- [`artifacts/examples/math/finite-predicate-v0/`](../../artifacts/examples/math/finite-predicate-v0/)
  validates finite-domain universal and existential predicate replay, a bounded
  non-empty `forall -> exists` enumeration row, finite relation asymmetry, and a
  general first-order Lean-horizon row.
- [`artifacts/examples/math/proof-methods-refutation-v0/`](../../artifacts/examples/math/proof-methods-refutation-v0/)
  is the first substantive math pack: proof-by-refutation over finite
  pigeonhole examples, with `PHP(2,2)` witness replay and `PHP(3,2)` checked
  by deterministic CNF truth-table enumeration. LRAT/DRAT remains the
  proof-object graduation target.
- [`artifacts/examples/math/proof-methods-patterns-v0/`](../../artifacts/examples/math/proof-methods-patterns-v0/)
  validates finite proof-method patterns: direct proof/modus ponens,
  contrapositive equivalence, proof by cases, contradiction refutation,
  invalid-converse counterexample evidence, and a natural-deduction
  Lean-horizon row.
- [`artifacts/examples/math/induction-obligations-v0/`](../../artifacts/examples/math/induction-obligations-v0/)
  validates bounded induction base, step, and conclusion obligations while
  keeping the full induction schema under Lean horizon.
- [`artifacts/examples/math/induction-patterns-v0/`](../../artifacts/examples/math/induction-patterns-v0/)
  validates finite weak-induction, strong-induction, and loop-invariant
  patterns, plus checked rejection of an invalid induction step.
- [`artifacts/examples/math/finite-sets-v0/`](../../artifacts/examples/math/finite-sets-v0/),
  [`artifacts/examples/math/relations-functions-v0/`](../../artifacts/examples/math/relations-functions-v0/),
  [`artifacts/examples/math/equivalence-classes-v0/`](../../artifacts/examples/math/equivalence-classes-v0/),
  [`artifacts/examples/math/function-composition-v0/`](../../artifacts/examples/math/function-composition-v0/),
  [`artifacts/examples/math/finite-order-lattices-v0/`](../../artifacts/examples/math/finite-order-lattices-v0/),
  [`artifacts/examples/math/finite-cardinality-v0/`](../../artifacts/examples/math/finite-cardinality-v0/),
  and [`artifacts/examples/math/cardinality-principles-v0/`](../../artifacts/examples/math/cardinality-principles-v0/)
  validate the finite foundations path: finite set identities, relation and
  function tables, finite partial orders and lattice tables, function
  composition, image/preimage and inverse replay, equivalence classes,
  quotient-map fibers, finite bijections, finite cardinal inequalities,
  bounded injection/surjection refutations, inclusion-exclusion,
  double counting, powersets, monotone fixed-point replay, and explicit
  infinite-cardinality Lean-horizon rows.
- [`artifacts/examples/math/natural-arithmetic-v0/`](../../artifacts/examples/math/natural-arithmetic-v0/),
  [`artifacts/examples/math/integer-lia-v0/`](../../artifacts/examples/math/integer-lia-v0/),
  [`artifacts/examples/math/gcd-bezout-v0/`](../../artifacts/examples/math/gcd-bezout-v0/),
  and [`artifacts/examples/math/number-theory-v0/`](../../artifacts/examples/math/number-theory-v0/)
  validate the core arithmetic path with bounded natural arithmetic, integer
  LIA witnesses, gcd/Bezout replay, and bounded number-theory checks.
- [`artifacts/examples/math/modular-arithmetic-v0/`](../../artifacts/examples/math/modular-arithmetic-v0/)
  validates small CRT, modular inverse, composite non-unit, and Fermat-style
  finite checks by replay/exhaustive search.
- [`artifacts/examples/math/rationals-lra-v0/`](../../artifacts/examples/math/rationals-lra-v0/)
  validates exact rational density, additive inverse, trichotomy, and
  transitivity checks using rational replay.
- [`artifacts/examples/math/reals-rcf-shadow-v0/`](../../artifacts/examples/math/reals-rcf-shadow-v0/)
  validates exact ordered-field replay, nonlinear product replay, a quadratic
  real-root witness, two tiny quadratic infeasibility checks, and a
  real-completeness Lean-horizon row.
- [`artifacts/examples/math/real-analysis-rational-v0/`](../../artifacts/examples/math/real-analysis-rational-v0/)
  validates exact rational interval/ball inclusion, bounded linear
  epsilon-delta replay, squeeze-style polynomial side conditions, checked
  bad-delta rejection, and a general real-analysis Lean-horizon row.
- [`artifacts/examples/math/sequence-limit-shadow-v0/`](../../artifacts/examples/math/sequence-limit-shadow-v0/)
  validates bounded epsilon-tail replay, finite limit counterexamples,
  monotone bounded prefixes, a fixed geometric partial-sum identity, a bounded
  finite Cauchy-tail check, and a general convergence Lean-horizon row.
- [`artifacts/examples/math/metric-continuity-v0/`](../../artifacts/examples/math/metric-continuity-v0/)
  validates finite Lipschitz, epsilon-delta, and open-ball preimage checks
  with exact rational metrics, plus checked rejection of an overlarge delta.
- [`artifacts/examples/math/finite-compactness-v0/`](../../artifacts/examples/math/finite-compactness-v0/)
  validates finite open-cover/subcover checks, minimal subcover enumeration,
  finite-intersection families, bad-cover rejection, and a compactness
  Lean-horizon row.
- [`artifacts/examples/math/finite-connectedness-v0/`](../../artifacts/examples/math/finite-connectedness-v0/)
  validates finite connectedness via clopen-subset enumeration, open
  separations, bad-connected-claim rejection, and a connectedness Lean-horizon
  row.
- [`artifacts/examples/math/finite-continuous-maps-v0/`](../../artifacts/examples/math/finite-continuous-maps-v0/)
  validates finite continuity by open-set preimage enumeration, finite
  homeomorphism replay, bad-continuity and bad-homeomorphism rejection, and a
  continuous-map Lean-horizon row.
- [`artifacts/examples/math/finite-simplicial-homology-v0/`](../../artifacts/examples/math/finite-simplicial-homology-v0/)
  validates finite simplicial-complex closure, oriented-boundary replay,
  `boundary^2 = 0`, Betti-rank replay for a three-edge circle, checked
  rejection of a bad boundary sign, and a homology Lean-horizon row.
- [`artifacts/examples/math/calculus-algebraic-shadow-v0/`](../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
  validates polynomial derivative replay, a product-rule polynomial identity,
  tangent-line replay, a convex quadratic critical point, false-derivative
  rejection, and a general calculus Lean-horizon row.
- [`artifacts/examples/math/calculus-riemann-sum-v0/`](../../artifacts/examples/math/calculus-riemann-sum-v0/)
  validates exact finite Riemann sums, midpoint/trapezoid replay,
  antiderivative endpoint replay, monotone lower/upper sums, checked false
  integral rejection, and a fundamental-theorem Lean-horizon row.
- [`artifacts/examples/math/multivariable-calculus-rational-v0/`](../../artifacts/examples/math/multivariable-calculus-rational-v0/)
  validates exact rational bivariate-polynomial value/gradient replay,
  directional derivatives, Jacobian chain-rule matrix replay, Hessian
  positive-definiteness by principal minors, checked bad-gradient rejection,
  and a multivariable-calculus Lean-horizon row.
- [`artifacts/examples/math/linear-algebra-rational-v0/`](../../artifacts/examples/math/linear-algebra-rational-v0/)
  validates exact rational matrix-vector solution replay, LU factorization
  replay, and a row-scaling inconsistency certificate for a singular system.
- [`artifacts/examples/math/finite-vector-spaces-v0/`](../../artifacts/examples/math/finite-vector-spaces-v0/)
  validates finite vector-space laws over `F2`, subspace and span replay,
  linear-map kernel/image replay, rank-nullity replay, checked rejection of a
  non-subspace, and a vector-space/module Lean-horizon row.
- [`artifacts/examples/math/finite-dual-spaces-v0/`](../../artifacts/examples/math/finite-dual-spaces-v0/)
  validates finite dual-space covector linearity over `F2`, pointwise dual
  operations, dual-basis pairing, annihilator recomputation, transpose-map
  replay, checked rejection of a bad covector, and a duality/functional-analysis
  Lean-horizon row.
- [`artifacts/examples/math/inner-product-spaces-rational-v0/`](../../artifacts/examples/math/inner-product-spaces-rational-v0/)
  validates exact rational Gram matrices, positive-definite principal minors,
  Cauchy-Schwarz replay for fixed vectors, orthogonal projection replay,
  Gram-Schmidt replay, checked rejection of an indefinite bilinear form, and a
  Hilbert/inner-product-theory Lean-horizon row.
- [`artifacts/examples/math/finite-modules-v0/`](../../artifacts/examples/math/finite-modules-v0/)
  validates finite module laws over `Z/4Z`, submodule and span replay,
  module-homomorphism kernel/image replay, quotient-module table replay,
  checked rejection of a non-submodule, and a module-theory Lean-horizon row.
- [`artifacts/examples/math/finite-tensor-products-v0/`](../../artifacts/examples/math/finite-tensor-products-v0/)
  validates finite tensor-product basis/dimension replay over `F2`,
  bilinear-map table replay, universal-factorization shadow through a linear
  map, Kronecker-product replay, checked bad-bilinear-map rejection, and a
  tensor-theory Lean-horizon row.
- [`artifacts/examples/math/finite-ideals-v0/`](../../artifacts/examples/math/finite-ideals-v0/)
  validates finite ideal laws over `Z/6Z`, principal ideal generation,
  ring-homomorphism kernel/image replay, quotient-ring table replay, checked
  rejection of a non-ideal, and an ideal-theory Lean-horizon row.
- [`artifacts/examples/math/numerical-linear-algebra-v0/`](../../artifacts/examples/math/numerical-linear-algebra-v0/)
  validates exact residual bounds, rational solution boxes, Jacobi one-step
  contraction replay, and checked rejection of a false residual bound.
- [`artifacts/examples/math/spectral-linear-algebra-v0/`](../../artifacts/examples/math/spectral-linear-algebra-v0/)
  validates exact finite eigenpair replay, orthogonal eigenbasis checks,
  Rayleigh quotients, spectral decomposition replay, and checked rejection of a
  false eigenpair.
- [`artifacts/examples/math/matrix-invariants-v0/`](../../artifacts/examples/math/matrix-invariants-v0/)
  validates exact trace/determinant characteristic-polynomial replay,
  characteristic roots, Cayley-Hamilton replay, finite Gershgorin intervals,
  and checked rejection of a false characteristic polynomial.
- [`artifacts/examples/math/random-matrix-finite-v0/`](../../artifacts/examples/math/random-matrix-finite-v0/)
  validates exact finite random-matrix moments, expected Gram matrices, rank
  probabilities, and checked rejection of a false trace-square moment.
- [`artifacts/examples/math/finite-markov-chain-v0/`](../../artifacts/examples/math/finite-markov-chain-v0/)
  validates exact stochastic matrices, finite-horizon distribution evolution,
  stationary distributions, and checked rejection of a malformed transition row.
- [`artifacts/examples/math/exact-statistical-tests-v0/`](../../artifacts/examples/math/exact-statistical-tests-v0/)
  validates exact binomial tails, hypergeometric point probabilities,
  one-sided Fisher p-values, and checked rejection of a false p-value.
- [`artifacts/examples/math/finite-groups-v0/`](../../artifacts/examples/math/finite-groups-v0/),
  [`artifacts/examples/math/finite-monoids-v0/`](../../artifacts/examples/math/finite-monoids-v0/),
  [`artifacts/examples/math/finite-permutation-groups-v0/`](../../artifacts/examples/math/finite-permutation-groups-v0/),
  [`artifacts/examples/math/finite-group-actions-v0/`](../../artifacts/examples/math/finite-group-actions-v0/),
  [`artifacts/examples/math/finite-rings-v0/`](../../artifacts/examples/math/finite-rings-v0/),
  [`artifacts/examples/math/finite-fields-v0/`](../../artifacts/examples/math/finite-fields-v0/),
  [`artifacts/examples/math/finite-algebra-homomorphisms-v0/`](../../artifacts/examples/math/finite-algebra-homomorphisms-v0/),
  [`artifacts/examples/math/finite-vector-spaces-v0/`](../../artifacts/examples/math/finite-vector-spaces-v0/),
  [`artifacts/examples/math/finite-dual-spaces-v0/`](../../artifacts/examples/math/finite-dual-spaces-v0/),
  [`artifacts/examples/math/inner-product-spaces-rational-v0/`](../../artifacts/examples/math/inner-product-spaces-rational-v0/),
  [`artifacts/examples/math/finite-modules-v0/`](../../artifacts/examples/math/finite-modules-v0/),
  [`artifacts/examples/math/finite-ideals-v0/`](../../artifacts/examples/math/finite-ideals-v0/),
  [`artifacts/examples/math/polynomial-identities-v0/`](../../artifacts/examples/math/polynomial-identities-v0/),
  [`artifacts/examples/math/polynomial-factorization-rational-v0/`](../../artifacts/examples/math/polynomial-factorization-rational-v0/),
  [`artifacts/examples/math/counting-v0/`](../../artifacts/examples/math/counting-v0/),
  and [`artifacts/examples/math/generating-functions-v0/`](../../artifacts/examples/math/generating-functions-v0/)
  validate the finite algebra and discrete core: finite group/monoid/ring/field
  table checks, finite transformation-composition monoids, unit/idempotent
  replay, finite permutation group composition/cycle/sign replay, finite
  group-action law replay, orbit/stabilizer and Burnside counting, finite
  homomorphism/kernel/quotient replay, finite ideal and quotient-ring replay,
  finite vector-space, dual-space, inner-product, and
  module replay, fixed polynomial identities, exact rational polynomial
  factorization/division/GCD rows, finite counting/pigeonhole rows, and finite
  generating-function coefficient/convolution replay.
- [`artifacts/examples/math/graph-coloring-v0/`](../../artifacts/examples/math/graph-coloring-v0/)
  validates finite graph coloring witnesses, invalid-coloring replay, and an
  exhaustive two-colorability refutation for `K3`.
- [`artifacts/examples/math/graph-reachability-v0/`](../../artifacts/examples/math/graph-reachability-v0/)
  validates finite BFS shortest-distance replay, deterministic DFS traversal
  replay, disconnected no-path refutation, and edge-cut separation replay.
- [`artifacts/examples/math/graph-search-runtime-v0/`](../../artifacts/examples/math/graph-search-runtime-v0/)
  validates finite BFS/DFS target-discovery cost counters, shortcut-tail
  family replay, checked rejection of a false DFS cost bound, and an
  asymptotic-runtime Lean-horizon row.
- [`artifacts/examples/math/graph-matching-v0/`](../../artifacts/examples/math/graph-matching-v0/)
  validates finite matching witnesses, invalid-overlap rejection,
  augmenting-path flip replay, and a perfect-matching obstruction by
  exhaustive enumeration.
- [`artifacts/examples/math/graph-d-separation-v0/`](../../artifacts/examples/math/graph-d-separation-v0/)
  validates finite DAG d-separation checks for chains, forks, colliders, and
  descendant-opened colliders.
- [`artifacts/examples/math/graph-cut-v0/`](../../artifacts/examples/math/graph-cut-v0/)
  validates finite minimum edge-cut and vertex-cut certificates, plus checked
  rejection of non-separating one-edge and one-vertex cuts.
- [`artifacts/examples/math/finite-probability-v0/`](../../artifacts/examples/math/finite-probability-v0/)
  validates exact finite probability mass tables, conditional probability, and
  Bayes posterior replay.
- [`artifacts/examples/math/descriptive-statistics-v0/`](../../artifacts/examples/math/descriptive-statistics-v0/)
  validates exact mean/variance identities, contingency-table margins, and a
  Simpson's paradox count-table witness.
- [`artifacts/examples/math/least-squares-regression-v0/`](../../artifacts/examples/math/least-squares-regression-v0/)
  validates exact least-squares normal equations, residual orthogonality,
  mean-baseline RSS comparison, checked rejection of bad coefficients, and a
  regression-statistics Lean-horizon row.
- [`artifacts/examples/math/linear-optimization-v0/`](../../artifacts/examples/math/linear-optimization-v0/)
  validates exact LP feasibility witnesses, objective-threshold replay, and a
  tiny checked Farkas infeasibility certificate.
- [`artifacts/examples/math/convexity-rational-v0/`](../../artifacts/examples/math/convexity-rational-v0/)
  validates exact rational midpoint convexity, finite-grid second
  differences, affine threshold monotonicity, checked bad midpoint-convexity
  rejection, and a general convex-analysis Lean-horizon row.
- [`artifacts/examples/math/coordinate-geometry-v0/`](../../artifacts/examples/math/coordinate-geometry-v0/)
  validates exact midpoint, collinearity, and squared-distance coordinate
  checks.
- [`artifacts/examples/math/affine-geometry-v0/`](../../artifacts/examples/math/affine-geometry-v0/)
  validates exact affine point-image replay, midpoint preservation,
  collinearity preservation, checked rejection of false distance preservation,
  and an affine-geometry Lean-horizon row.
- [`artifacts/examples/math/orientation-area-geometry-v0/`](../../artifacts/examples/math/orientation-area-geometry-v0/)
  validates exact signed-area/orientation replay, affine area scaling,
  barycentric point-inside replay, checked rejection of a false orientation
  claim, and an oriented-geometry Lean-horizon row.
- [`artifacts/examples/math/finite-topology-v0/`](../../artifacts/examples/math/finite-topology-v0/)
  validates finite topology axioms, closure/interior computation, and exact
  finite metric-ball replay.
- [`artifacts/examples/math/finite-measure-v0/`](../../artifacts/examples/math/finite-measure-v0/)
  validates finite sigma-algebra axioms, exact finite additivity, and
  event/complement measure replay.
- [`artifacts/examples/math/finite-integration-v0/`](../../artifacts/examples/math/finite-integration-v0/)
  validates exact finite simple-function integrals, indicator integrals,
  integral linearity, checked rejection of a false expectation, and a
  Lebesgue-integration Lean-horizon row.
- [`artifacts/examples/math/finite-product-measure-v0/`](../../artifacts/examples/math/finite-product-measure-v0/)
  validates exact finite product-measure tables, rectangle probabilities,
  left and right marginals, finite Fubini replay, checked rejection of a false
  product probability, and a Fubini/Tonelli Lean-horizon row.
- [`artifacts/examples/math/finite-random-variables-v0/`](../../artifacts/examples/math/finite-random-variables-v0/)
  validates exact finite random-variable pushforwards, expectation through
  pushforward distributions, finite independence checks, checked rejection of a
  false pushforward distribution, and a general random-variable Lean-horizon
  row.
- [`artifacts/examples/math/finite-conditional-expectation-v0/`](../../artifacts/examples/math/finite-conditional-expectation-v0/)
  validates exact finite partition conditional expectations, law of total
  expectation, tower property replay, checked rejection of a false
  conditional-expectation table, and a general conditional-expectation
  Lean-horizon row.
- [`artifacts/examples/math/finite-martingales-v0/`](../../artifacts/examples/math/finite-martingales-v0/)
  validates exact finite filtrations, adapted process values, martingale
  conditional-expectation equalities, square submartingale inequalities,
  bounded stopping-time replay, checked rejection of a false martingale table,
  and a general martingale Lean-horizon row.
- [`artifacts/examples/math/finite-stochastic-kernels-v0/`](../../artifacts/examples/math/finite-stochastic-kernels-v0/)
  validates exact finite stochastic kernels, pushforward distributions, joint
  table factorization/disintegration, finite kernel composition, checked
  rejection of a malformed kernel row, and a regular-conditional-probability
  Lean-horizon row.
- [`artifacts/examples/math/finite-hitting-times-v0/`](../../artifacts/examples/math/finite-hitting-times-v0/)
  validates exact finite first-hit distributions, survival probabilities,
  absorption-probability equations, expected hitting-time equations, checked
  rejection of a malformed expected-time table, and a recurrence/transience
  Lean-horizon row.
- [`artifacts/examples/math/finite-concentration-v0/`](../../artifacts/examples/math/finite-concentration-v0/)
  validates exact finite Markov, Chebyshev, and union-bound replays over
  rational atom tables, checked rejection of a false tail bound, and a
  concentration/limit-theorem Lean-horizon row.
- [`artifacts/examples/math/bounded-dynamics-v0/`](../../artifacts/examples/math/bounded-dynamics-v0/)
  validates exact rational recurrence traces, bounded invariant witnesses, and
  threshold reachability replay.
- [`artifacts/examples/math/finite-euler-method-v0/`](../../artifacts/examples/math/finite-euler-method-v0/)
  validates exact finite Euler-method traces, polynomial-solution error replay,
  invariant checks, checked rejection of a bad Euler step, and an ODE-theory
  Lean-horizon row.
- [`artifacts/examples/math/finite-operator-v0/`](../../artifacts/examples/math/finite-operator-v0/)
  validates exact finite-dimensional norm, matrix-operator, and Chebyshev
  recurrence checks.
- [`artifacts/examples/math/finite-chebyshev-systems-v0/`](../../artifacts/examples/math/finite-chebyshev-systems-v0/)
  validates exact finite Vandermonde unisolvence, interpolation replay,
  alternating residual signs, checked rejection of a duplicate-node grid, and a
  general Chebyshev-system Lean-horizon row.
- [`artifacts/examples/math/complex-algebraic-v0/`](../../artifacts/examples/math/complex-algebraic-v0/)
  validates exact complex arithmetic, conjugate/norm replay, and a fixed
  polynomial-root witness using real-pair algebra.
- [`artifacts/examples/math/complex-plane-transforms-v0/`](../../artifacts/examples/math/complex-plane-transforms-v0/)
  validates exact unit-root cycles, conjugation/product replay, rational
  Mobius-transform replay, checked rejection of a false unit-square real-part
  claim, and a complex-analysis Lean-horizon row.

Validation commands:

```sh
python3 scripts/gen-foundational-concepts.py
python3 scripts/validate-foundational-concepts.py
python3 scripts/gen-foundational-dashboards.py
python3 scripts/validate-foundational-example-pack.py
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/template-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/logic-basics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-predicate-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-patterns-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-obligations-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/induction-patterns-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/equivalence-classes-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/function-composition-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-order-lattices-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/cardinality-principles-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/modular-arithmetic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/rationals-lra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/reals-rcf-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/real-analysis-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/sequence-limit-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/metric-continuity-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-continuous-maps-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-simplicial-homology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-algebraic-shadow-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/calculus-riemann-sum-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/multivariable-calculus-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-algebra-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-vector-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-dual-spaces-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/inner-product-spaces-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-modules-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-tensor-products-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-ideals-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/numerical-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/spectral-linear-algebra-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/matrix-invariants-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/random-matrix-finite-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-markov-chain-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/exact-statistical-tests-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/polynomial-factorization-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-monoids-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-permutation-groups-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-group-actions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/generating-functions-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-search-runtime-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-matching-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-cut-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-probability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/descriptive-statistics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/least-squares-regression-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/linear-optimization-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/convexity-rational-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/coordinate-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/affine-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/orientation-area-geometry-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-measure-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-integration-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-product-measure-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-random-variables-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-conditional-expectation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-martingales-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-stochastic-kernels-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-hitting-times-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-concentration-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/bounded-dynamics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-euler-method-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-operator-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-chebyshev-systems-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-algebraic-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/complex-plane-transforms-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-algebra-homomorphisms-v0
```

## Principle

Every resource should reinforce Axeyum's core identity:

```text
untrusted fast search, trusted small checking
```

For educational and knowledge artifacts, that means:

- distinguish concept maps from executable examples;
- mark decidable, bounded, computable, and proof-assistant-only material;
- replay every concrete witness;
- require checkable evidence for `unsat` examples when possible;
- keep generated or machine-readable data validated by scripts.
