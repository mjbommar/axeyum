# Learn: Mathematics As Checkable Resources

This path connects the university-style math curriculum to Axeyum's resource
packs. It is not a textbook. Each page shows what can be checked today, what
evidence exists, and what remains a proof-assistant or numerical horizon.

Source maps:

- [curriculum DAG](../../curriculum/README.md)
- [Foundational Concept Atlas](../../../artifacts/ontology/foundational-concepts.json)
- [math coverage dashboard](../../foundational-resources/generated/math-coverage.md)
- [math field dashboard](../../foundational-resources/generated/math-field-dashboard.md)
- [example-pack inventory](../../foundational-resources/README.md)

## Lesson Paths

| Path | Start With | First Checkable Packs |
|---|---|---|
| [Logic And Proof](logic-and-proof.md) | `curriculum_propositional_logic`, `curriculum_predicate_logic`, `curriculum_proof_methods`, `curriculum_induction`, `field_logic_and_proof` | `logic-basics-v0`, `finite-predicate-v0`, `proof-methods-refutation-v0`, `proof-methods-patterns-v0`, `induction-obligations-v0`, `induction-patterns-v0`, `graph-coloring-v0` |
| [Sets, Relations, And Finite Structures](sets-relations-and-finite-structures.md) | `curriculum_sets`, `curriculum_relations_and_functions`, `curriculum_cardinality`, `field_set_theory_and_foundations` | `finite-sets-v0`, `relations-functions-v0`, `equivalence-classes-v0`, `function-composition-v0`, `finite-monoids-v0`, `finite-permutation-groups-v0`, `finite-group-actions-v0`, `finite-order-lattices-v0`, `finite-cardinality-v0`, `cardinality-principles-v0`, `finite-topology-v0`, `finite-compactness-v0`, `finite-connectedness-v0`, `finite-continuous-maps-v0`, `finite-simplicial-homology-v0` |
| [Number Systems And Arithmetic](number-systems-and-arithmetic.md) | `curriculum_naturals`, `curriculum_integers`, `curriculum_divisibility_and_euclid`, `curriculum_modular_arithmetic`, `curriculum_number_theory`, `curriculum_rationals`, `curriculum_complex` | `natural-arithmetic-v0`, `integer-lia-v0`, `gcd-bezout-v0`, `modular-arithmetic-v0`, `number-theory-v0`, `rationals-lra-v0`, `complex-algebraic-v0`, `complex-plane-transforms-v0` |
| [Algebra And Number Theory](algebra-and-number-theory.md) | `field_abstract_algebra`, `field_number_theory` | `gcd-bezout-v0`, `number-theory-v0`, `finite-groups-v0`, `finite-monoids-v0`, `finite-permutation-groups-v0`, `finite-group-actions-v0`, `finite-rings-v0`, `finite-fields-v0`, `finite-algebra-homomorphisms-v0`, `finite-ideals-v0`, `finite-vector-spaces-v0`, `finite-dual-spaces-v0`, `finite-modules-v0`, `finite-tensor-products-v0`, `polynomial-factorization-rational-v0`, `generating-functions-v0`, `complex-plane-transforms-v0` |
| [Rational And Real Algebra](rational-real-algebra.md) | `field_real_analysis`, `curriculum_reals` | `rationals-lra-v0`, `real-analysis-rational-v0`, `reals-rcf-shadow-v0`, `polynomial-identities-v0`, `polynomial-factorization-rational-v0`, `generating-functions-v0`, `matrix-invariants-v0`, `multivariable-calculus-rational-v0`, `linear-optimization-v0`, `convexity-rational-v0`, `coordinate-geometry-v0`, `affine-geometry-v0`, `orientation-area-geometry-v0` |
| [Graph And Discrete Reasoning](graph-and-discrete-reasoning.md) | `field_graph_theory`, `field_discrete_math` | `counting-v0`, `generating-functions-v0`, `finite-permutation-groups-v0`, `finite-group-actions-v0`, `graph-coloring-v0`, `graph-reachability-v0`, `graph-search-runtime-v0`, `graph-matching-v0`, `graph-d-separation-v0`, `graph-cut-v0`, `proof-methods-refutation-v0` |
| [Linear Algebra And Optimization](linear-algebra-and-optimization.md) | `curriculum_linear_algebra`, `field_optimization_and_convexity` | `linear-algebra-rational-v0`, `finite-vector-spaces-v0`, `finite-dual-spaces-v0`, `inner-product-spaces-rational-v0`, `finite-modules-v0`, `finite-tensor-products-v0`, `numerical-linear-algebra-v0`, `spectral-linear-algebra-v0`, `matrix-invariants-v0`, `random-matrix-finite-v0`, `least-squares-regression-v0`, `finite-simplicial-homology-v0`, `multivariable-calculus-rational-v0`, `linear-optimization-v0`, `convexity-rational-v0`, `finite-operator-v0`, `finite-chebyshev-systems-v0` |
| [Probability And Statistics](probability-and-statistics.md) | `field_probability_theory`, `field_statistics` | `finite-probability-v0`, `finite-random-variables-v0`, `finite-conditional-expectation-v0`, `finite-stochastic-kernels-v0`, `finite-hitting-times-v0`, `finite-concentration-v0`, `finite-martingales-v0`, `finite-integration-v0`, `finite-product-measure-v0`, `finite-markov-chain-v0`, `descriptive-statistics-v0`, `least-squares-regression-v0`, `exact-statistical-tests-v0`, `finite-measure-v0`, `random-matrix-finite-v0` |
| [Analysis And Topology Proof Horizons](analysis-topology-proof-horizons.md) | `field_topology`, `field_measure_theory`, `field_functional_analysis_and_operator_theory` | `real-analysis-rational-v0`, `sequence-limit-shadow-v0`, `generating-functions-v0`, `metric-continuity-v0`, `finite-compactness-v0`, `finite-connectedness-v0`, `finite-continuous-maps-v0`, `finite-simplicial-homology-v0`, `finite-integration-v0`, `finite-product-measure-v0`, `calculus-algebraic-shadow-v0`, `calculus-riemann-sum-v0`, `multivariable-calculus-rational-v0`, `finite-topology-v0`, `bounded-dynamics-v0`, `finite-euler-method-v0`, `finite-markov-chain-v0`, `finite-hitting-times-v0`, `inner-product-spaces-rational-v0`, `finite-operator-v0`, `finite-chebyshev-systems-v0` |

Each cluster page includes an `Encode / Check Walkthrough` section with
validated pack data and the repo-root command that replays it.

## End-To-End Lessons

- [Logic Basics](logic-basics-end-to-end.md): follows Boolean assignment replay,
  excluded-middle and contradiction truth-table checks, De Morgan equivalence,
  and a tiny CNF refutation.
- [Finite Predicate Logic](finite-predicate-end-to-end.md): follows finite
  universal/existential predicate replay, bounded quantifier implication
  enumeration with checked DRAT/LRAT evidence, relation symmetry
  counterexamples, and the first-order Lean horizon.
- [Proof By Refutation](proof-methods-refutation-end-to-end.md): follows a
  pigeonhole SAT control, checked `PHP(3,2)` CNF truth-table refutation, and
  checked DRAT/LRAT proof-object evidence for the source DIMACS artifact.
- [Proof Method Patterns](proof-methods-patterns-end-to-end.md): follows
  direct proof, contrapositive, proof by cases, contradiction, invalid-converse
  counterexample, and the natural-deduction Lean horizon.
- [Induction Obligations](induction-obligations-end-to-end.md): follows
  prefix-sum base, bounded step and conclusion checks, a bad-step
  counterexample, a QF_LIA arithmetic-DPLL bad step-count certificate, and the
  induction-schema Lean horizon.
- [Induction Patterns](induction-patterns-end-to-end.md): follows finite weak
  induction, a QF_LIA/Diophantine even-product certificate, strong induction,
  loop-invariant replay, invalid-step rejection, and the general
  induction-schema Lean horizon.
- [Finite Sets](finite-sets-end-to-end.md): follows finite universe/subset
  replay, union/intersection identity replay, subset transitivity, and a fixed
  malformed-identity rejection.
- [Relations And Functions](relations-functions-end-to-end.md): follows finite
  partial-order replay, bijective function-table replay, and checked rejection
  of a multi-valued graph.
- [Equivalence Classes](equivalence-classes-end-to-end.md): follows finite
  equivalence-relation class replay, quotient-map fiber replay, partition
  round-trip checking, checked non-transitivity rejection, and the QF_UF/Alethe
  quotient congruence proof row.
- [Function Composition](function-composition-end-to-end.md): follows finite
  composition, image/preimage, inverse-table, associativity, and
  non-injective inverse-counterexample checks, plus a QF_UF/Alethe composition
  application proof row.
- [Counting And Pigeonhole](counting-pigeonhole-end-to-end.md): follows a fixed
  permutation count, one Pascal-identity instance, finite pigeonhole
  enumeration, and the CNF/LRAT proof-upgrade route.
- [Triangle Coloring](graph-coloring-end-to-end.md): follows a finite graph
  coloring resource from data row through replayed `sat`, checked finite
  `unsat`, and proof/evidence status.
- [Graph Reachability And Traversal](graph-reachability-end-to-end.md):
  follows BFS shortest-distance replay, deterministic DFS traversal replay,
  disconnected no-path refutation, and edge-cut separation over finite graphs.
- [Graph Search Runtime Counters](graph-search-runtime-end-to-end.md):
  follows finite BFS and DFS visited-node counter replay, shortcut-tail family
  checks, checked QF_LIA arithmetic-DPLL bad DFS-bound rejection, and the
  asymptotic runtime Lean horizon.
- [Graph Matching And Augmenting Paths](graph-matching-end-to-end.md): follows
  finite matching witness replay, overlapping-edge rejection, augmenting-path
  flip replay, and a `K3` perfect-matching refutation.
- [Graph Cut Certificates](graph-cut-end-to-end.md): follows finite
  minimum-edge-cut and minimum-vertex-cut certificates, rejected one-cut claims,
  and checked smaller-cut enumeration.
- [DAG D-Separation Checks](graph-d-separation-end-to-end.md): follows finite
  active chains, conditioned chain/fork blocking, collider blocking, and
  descendant-opened collider replay.
- [Natural Arithmetic](natural-arithmetic-end-to-end.md): follows successor
  arithmetic, fixed addition and multiplication replay, bounded successor
  no-counterexample enumeration, a checked QF_LIA negative-domain refutation,
  and the universal Nat theorem horizon.
- [Integer Linear Arithmetic](integer-lia-end-to-end.md): follows signed order
  replay, integer ring and linear-equation witnesses, interval infeasibility,
  and a checked QF_LIA/Diophantine gcd refutation.
- [GCD And Bezout](gcd-bezout-end-to-end.md): follows gcd/common-divisor
  replay, Bezout coefficient checking, divisibility quotient replay, and a
  fixed Diophantine gcd obstruction.
- [Modular Arithmetic](modular-arithmetic-end-to-end.md): follows a CRT
  witness, modular inverse witness, finite composite non-unit search, a
  checked QF_LIA/Diophantine nonunit obstruction, and a Fermat-style finite
  unit search.
- [Bounded Number Theory](number-theory-end-to-end.md): follows compatible
  non-coprime CRT replay, quadratic residue and nonresidue checks,
  sum-of-two-squares replay and rejection, and a Diophantine witness.
- [Complex Algebraic Replay](complex-algebraic-end-to-end.md): follows exact
  complex real-pair addition, multiplication, conjugate/norm replay, and the
  fixed `i` root witness for `x^2 + 1`.
- [Complex Plane Transforms](complex-plane-transforms-end-to-end.md): follows
  unit-root cycle replay, conjugation over products, a rational Mobius
  transform, QF_LRA/Farkas bad unit-square real-part rejection, and the
  complex-analysis Lean horizon.
- [Rational Midpoint](rational-midpoint-end-to-end.md): follows an exact
  density witness through fraction arithmetic and replay-only evidence status.
- [Bounded Rational Real Analysis](real-analysis-rational-end-to-end.md):
  follows rational interval/ball replay, bounded epsilon-delta samples,
  polynomial side conditions, a QF_LRA/Farkas bad-delta certificate, and the
  Lean horizon.
- [Sequence And Limit Shadows](sequence-limit-shadow-end-to-end.md): follows
  finite epsilon-tail replay, a proposed-limit counterexample, monotone-prefix
  checks, geometric partial sums, finite Cauchy-tail enumeration with a
  QF_LRA/Farkas max-distance certificate, and the general limit Lean horizon.
- [Finite Calculus Shadows](calculus-shadows-end-to-end.md): follows
  polynomial derivative replay, product-rule and tangent checks, finite
  Riemann sums, antiderivative endpoint replay, false derivative/integral
  rejection with QF_LRA/Farkas certificates, and the calculus Lean horizons.
- [Metric Continuity](metric-continuity-end-to-end.md): follows finite metric
  table replay, finite Lipschitz checks, epsilon-delta containment,
  open-ball preimage replay, checked QF_LRA/Farkas bad-delta rejection, and
  the continuity Lean horizon.
- [Real Algebra RCF Shadow](reals-rcf-shadow-end-to-end.md): follows ordered
  field and nonlinear product witnesses, a quadratic root replay, square
  nonnegativity, negative-discriminant rejection with QF_LRA/Farkas evidence,
  and the completeness horizon.
- [Polynomial Identities](polynomial-identities-end-to-end.md): follows exact
  coefficient multiplication, factor-theorem root replay, quotient checking,
  and checked false-root rejection through QF_LIA/Diophantine evidence.
- [Rational Polynomial Factorization](polynomial-factorization-end-to-end.md):
  follows factor-list replay, long division, Euclidean GCD, square-free
  decomposition, fixed irreducibility rejection, a QF_LRA/Farkas discriminant
  conflict, and the algebra Lean horizon.
- [Generating Functions](generating-functions-end-to-end.md): follows finite
  coefficient extraction, Cauchy product convolution, a bounded Fibonacci
  generating-function identity, bad-product rejection, and the general
  recurrence/asymptotic Lean horizon.
- [Matrix Invariants](matrix-invariants-end-to-end.md): follows exact trace,
  determinant, characteristic-polynomial, root, Cayley-Hamilton, Gershgorin,
  and a QF_LRA/Farkas bad-characteristic-polynomial certificate for a fixed
  rational matrix.
- [Spectral Linear Algebra](spectral-linear-algebra-end-to-end.md): follows
  exact eigenpair replay, orthogonal eigenbasis arithmetic, Rayleigh quotient
  checking, spectral decomposition reconstruction, and a QF_LRA/Farkas
  bad-eigenpair certificate.
- [Finite Random Matrices](random-matrix-finite-end-to-end.md): follows exact
  matrix-valued probability tables, trace/determinant moments, expected Gram
  matrices, rank probabilities, and a QF_LRA/Farkas bad trace-square
  certificate.
- [Numerical Linear Algebra](numerical-linear-algebra-end-to-end.md): follows
  exact residual infinity norms, rational solution boxes, one-step Jacobi
  contraction replay, QF_LRA/Farkas bad residual-bound rejection, and the
  numerical horizon.
- [Descriptive Statistics And Regression](descriptive-statistics-regression-end-to-end.md):
  follows exact mean/variance replay, contingency-table margins, Simpson's
  paradox counts, a QF_LIA/Diophantine bad total-count certificate,
  least-squares normal equations, residual orthogonality, RSS comparison, and
  a QF_LRA/Farkas bad-coefficients certificate.
- [Exact Statistical Tests](exact-statistical-tests-end-to-end.md): follows a
  one-sided exact binomial tail, hypergeometric point probability, one-sided
  Fisher tail, checked bad p-value rejection, a QF_LIA/Diophantine bad
  tail-count certificate, and the statistical numerical-honesty horizon.
- [Coordinate And Affine Geometry](coordinate-affine-geometry-end-to-end.md):
  follows exact midpoint, collinearity, distance, affine-map, area-scaling,
  barycentric, QF_LRA/Farkas bad-distance, and QF_LRA/Farkas bad-orientation
  checks.
- [Rational Multivariable Calculus](multivariable-calculus-end-to-end.md):
  follows exact polynomial gradient replay, directional derivatives, Jacobian
  chain-rule matrix multiplication, Hessian minor checks, QF_LRA/Farkas
  bad-gradient rejection, and the analysis Lean horizon.
- [Linear System And LP Replay](linear-system-end-to-end.md): follows exact
  matrix replay and a tiny checked Farkas-style LP certificate.
- [Rational Convexity](convexity-rational-end-to-end.md): follows exact
  midpoint Jensen replay, finite second differences, affine threshold
  monotonicity, bad midpoint-convexity rejection, and the convex-analysis
  Lean horizon.
- [Rational Inner Product Spaces](inner-product-spaces-end-to-end.md):
  follows exact Gram-matrix replay, fixed Cauchy-Schwarz, orthogonal
  projection, Gram-Schmidt, and a QF_LRA/Farkas bad-inner-product
  certificate.
- [Finite Vector Spaces](finite-vector-spaces-end-to-end.md): follows `F2^2`
  table replay, subspace/span recomputation, linear-map kernel/image replay,
  rank-nullity by finite cardinality, and checked QF_UF/Alethe bad-subspace
  rejection.
- [Finite Dual Spaces](finite-dual-spaces-end-to-end.md): follows covector
  linearity, pointwise dual operations, dual-basis pairing, annihilator replay,
  transpose-map replay, and checked QF_UF/Alethe bad-covector rejection.
- [Finite Modules](finite-modules-end-to-end.md): follows `Z/4Z` module-law
  replay, generated submodule replay, multiplication-by-`2` kernel/image,
  quotient-module table replay, and checked QF_UF/Alethe bad-submodule
  rejection.
- [Finite Tensor Products](finite-tensor-products-end-to-end.md): follows
  finite tensor-basis replay, bilinear-map checks, factorization through a
  tensor map, Kronecker-product replay, and checked QF_UF/Alethe bad-bilinear
  rejection.
- [Finite Groups](finite-groups-end-to-end.md): follows `Z/4Z`
  Cayley-table replay, inverse-table replay, and checked rejection of
  subtraction modulo `3` as a group operation, plus a QF_UF/Alethe operation
  congruence proof row.
- [Finite Monoids](finite-monoids-end-to-end.md): follows a two-point
  transformation monoid through function-composition replay, identity and
  associativity checks, unit/idempotent recomputation, and checked
  QF_UF/Alethe non-associativity rejection.
- [Finite Permutation Groups](finite-permutation-groups-end-to-end.md):
  follows `S3` point maps through bijection checks, composition-table replay,
  cycle/sign replay, natural action orbit-stabilizer counting, and checked
  QF_UF/Alethe bad-nonbijection rejection.
- [Finite Group Actions And Burnside Counting](finite-group-actions-end-to-end.md):
  follows action-law replay, orbit/stabilizer recomputation, Burnside fixed-point
  counting, and checked bad-action rejection.
- [Finite Order Lattices](finite-order-lattices-end-to-end.md): follows finite
  partial-order replay, meet/join recomputation, distributivity checks,
  monotone fixed-point replay, and checked QF_UF/Alethe bad-order rejection.
- [Finite Cardinality](finite-cardinality-end-to-end.md): follows finite
  bijection and proper-subset injection witnesses, finite no-injection and
  no-surjection enumeration refutations, and the Cantor Lean horizon.
- [Cardinality Principles](cardinality-principles-end-to-end.md): follows
  inclusion-exclusion, disjoint-union additivity, double-counting, powerset
  cardinality, an overlapping-set counterexample to false additivity, and a
  checked QF_LIA/Diophantine overlap-additivity contradiction.
- [Finite Rings](finite-rings-end-to-end.md): follows `Z/4Z` ring-table replay,
  zero-divisor witness replay, and checked non-distributive-table rejection.
- [Finite Fields](finite-fields-end-to-end.md): follows `F_7` inverse-table
  replay, exhaustive no-distributivity-counterexample checking in `F_5`, and
  checked no-inverse rejection for `2 mod 6`.
- [Finite Algebra Homomorphisms](finite-algebra-homomorphisms-end-to-end.md):
  follows parity-map preservation, kernel/image recomputation,
  quotient/induced-map replay, ring-homomorphism replay, QF_UF/Alethe
  homomorphism-preservation congruence, and checked bad-homomorphism
  rejection.
- [Finite Ideals And Quotient Rings](finite-ideals-quotient-rings-end-to-end.md):
  follows `Z/6Z` ideal closure, principal generation, parity-map kernel/image,
  quotient-ring table replay, and checked QF_UF/Alethe bad non-ideal
  rejection.
- [Conditional Probability, Random Variables, Kernels, Concentration, Martingales, And Product Measures](finite-probability-end-to-end.md):
  follows finite atom tables through exact conditional-probability,
  checked Bayes-posterior refutation, random-variable, conditional-expectation,
  finite stochastic-kernel, concentration, finite martingale, product-measure,
  and simple-function integral replay.
- [Finite Integration](finite-integration-end-to-end.md): follows finite
  simple-function integrals, indicator integrals, integral linearity, checked
  bad-expectation rejection, and the Lebesgue-integration Lean horizon.
- [Finite Product Measure](finite-product-measure-end-to-end.md): follows
  Cartesian-product probability tables, rectangle probabilities, marginals,
  finite Fubini replay, checked bad product-probability rejection, and the
  Fubini/Tonelli Lean horizon.
- [Finite Random Variables](finite-random-variables-end-to-end.md): follows
  finite random-variable functions, pushforward distributions, expectation
  through pushforwards, finite independence, checked bad pushforward rejection,
  and the general random-variable Lean horizon.
- [Finite Conditional Expectation](finite-conditional-expectation-end-to-end.md):
  follows finite conditioning partitions, blockwise conditional expectations,
  total-expectation replay, tower-property replay, checked QF_LRA/Farkas bad
  table rejection, and the general conditional-expectation Lean horizon.
- [Finite Martingales](finite-martingales-end-to-end.md): follows finite
  filtrations, adaptedness, martingale conditional-expectation equalities,
  square-submartingale inequalities, bounded stopping replay, checked bad
  martingale rejection, and the general martingale Lean horizon.
- [Finite Stochastic Kernels](finite-stochastic-kernels-end-to-end.md): follows
  row-normalized finite kernels, pushforward distributions, joint
  factorization/disintegration, kernel composition, checked bad kernel-row
  rejection, and the regular-conditional-probability Lean horizon.
- [Finite Hitting Times](finite-hitting-times-end-to-end.md): follows finite
  absorbing-chain first-hit distributions, survival mass, absorption
  equations, expected hitting-time equations, checked bad expected-time
  rejection, and the general hitting-theory Lean horizon.
- [Finite Concentration](finite-concentration-end-to-end.md): follows exact
  finite Markov, Chebyshev, and union-bound replay over rational atom tables,
  checked bad concentration-bound rejection, and the general concentration
  Lean horizon.
- [Finite Markov Chains](finite-markov-chain-end-to-end.md): follows exact
  row-stochastic transition matrices, finite-horizon distribution replay,
  stationary distributions, checked bad transition-row rejection, and the
  Markov-chain convergence Lean horizon.
- [Finite Topology, Maps, Connectedness, And Measure](finite-structures-end-to-end.md):
  follows finite set-family, closure/interior, continuous-map, compactness,
  connectedness, and measure replay.
- [Finite Topology And Measure](finite-topology-measure-end-to-end.md):
  follows finite topology axioms, closure/interior, metric balls,
  sigma-algebra closure, finite additivity, and event-complement replay.
- [Finite Compactness](finite-compactness-end-to-end.md): follows finite
  open-cover replay, subcover replay, minimal-subcover enumeration,
  finite-intersection-family replay, checked Bool/CNF bad-cover rejection, and
  the compactness Lean horizon.
- [Finite Connectedness](finite-connectedness-end-to-end.md): follows finite
  connected-space replay, open-separation replay, clopen-subset disconnection,
  checked bad-connectedness rejection, and the connectedness Lean horizon.
- [Finite Continuous Maps](finite-continuous-maps-end-to-end.md): follows
  finite open-preimage replay, finite continuity checking, homeomorphism
  replay, checked bad-continuity rejection, checked bad-homeomorphism
  rejection, and the continuous-map Lean horizon.
- [Finite Simplicial Homology](finite-simplicial-homology-end-to-end.md):
  follows finite simplicial-complex closure, oriented boundary replay,
  `boundary^2 = 0`, Betti-rank replay, bad-boundary rejection, a
  QF_LIA/Diophantine bad-coefficient certificate, and the homology Lean
  horizon.
- [Finite Dynamics And Euler Replay](finite-dynamics-euler-end-to-end.md):
  follows bounded recurrence traces, finite invariants, threshold
  reachability, explicit Euler replay, finite error tables, and checked
  QF_LRA/Farkas bad Euler-step rejection.
- [Bounded Dynamics And Operators](analysis-dynamics-end-to-end.md): follows
  bounded recurrence, invariant, operator-bound, Chebyshev recurrence, and
  finite Chebyshev-system replay.
- [Finite Chebyshev Systems](finite-chebyshev-systems-end-to-end.md): follows
  exact Vandermonde unisolvence, interpolation, alternating residual signs,
  checked QF_LRA/Farkas duplicate-node determinant rejection, and the
  Chebyshev/Haar/minimax Lean horizon.

## How To Read These Pages

Use the example packs as the executable source of truth. A lesson can explain a
concept, but a resource only graduates when the pack metadata validates and the
witnesses replay.

The recurring pattern is:

1. Pick a finite, exact, or bounded slice.
2. Encode a tiny claim as data.
3. Replay a model, counterexample, or certificate.
4. Name the horizon honestly when the general theorem needs Lean or a broader
   solver route.
