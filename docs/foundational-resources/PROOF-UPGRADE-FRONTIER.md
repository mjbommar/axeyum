# Math Resource Proof Upgrade Frontier

This is the hand-authored execution frontier for turning the current math
curriculum resources from finite replay and proof-gap status into checked
evidence. The generated truth source is
[learner-proof-upgrade-dashboard.md](generated/learner-proof-upgrade-dashboard.md);
this file explains which route to work first, what artifact should be emitted,
and how a pack graduates.

Axeyum's identity stays fixed: untrusted fast search, trusted small checking.
For these resources, prose never upgrades a claim. A pack graduates only when
the original finite obligation is replayed or a proof certificate checks under
the route named in the pack metadata.

## Current Baseline

Generated from the current math resource queue:

- math example packs: 108
- learner-linked packs: 108 focused links
- packs with non-checked proof rows: 97
- non-checked proof rows: 316

Candidate route totals:

| Route | Pack Count | Meaning |
|---|---:|---|
| [Boolean CNF/LRAT](../proof-cookbook/recipes/boolean-cnf-lrat.md) | 16 | Boolean refutations that should carry checked CNF proof objects. |
| [QF_BV bit-blast](../proof-cookbook/recipes/qf-bv-bitblast.md) | 4 | Finite arithmetic/table obligations that should lower through BV/CNF evidence. |
| [QF_LIA Diophantine](../proof-cookbook/recipes/qf-lia-diophantine.md) | 11 | Integer equalities, counts, modular constraints, coefficient convolutions, rank obstructions, and torsion boundary-membership obstructions, including finite graph traversal cost counters. |
| [QF_LRA Farkas](../proof-cookbook/recipes/qf-lra-farkas.md) | 57 | Exact rational infeasibility and linear inequality obligations. |
| [QF_UF/Alethe](../proof-cookbook/recipes/qf-uf-congruence-alethe.md) | 19 | Equality-heavy finite structures and congruence conflicts. |
| [Lean horizon](../proof-cookbook/recipes/lean-horizon-template.md) | 78 | General theorem statements that remain outside bounded SMT replay. |

## Execution Order

### 0. Classify `needs-proof-route` (Current Queue Done)

Classified targets:

- [descriptive-statistics-v0](../../artifacts/examples/math/descriptive-statistics-v0/)
- [finite-probability-v0](../../artifacts/examples/math/finite-probability-v0/)

Classification:

- descriptive-statistics satisfiable witness rows remain finite-model replay;
  future impossible exact-rational statistic constraints use QF_LRA/Farkas, and
  the first inconsistent integer margin/count row now has a resource-backed
  QF_LIA/Diophantine regression for the bad contingency total;
- finite-probability satisfiable witness rows remain finite-model replay;
  future impossible normalization, nonnegativity, conditioning, or Bayes-rule
  constraints use QF_LRA/Farkas;
- keep satisfiable witness rows on finite-model replay, with model replay as
  the checked evidence;
- keep statistical inference, sampling, and continuous probability outside
  proof status until a separate numerical-honesty or Lean route exists.

Graduation:

- both packs have explicit proof-cookbook recipe links in `source_refs`;
- each non-checked expected-result row is either still honestly replay-only or
  has a named certificate route;
- pack validators and foundational dashboard generation pass.

The current generated queue has no `needs-proof-route` rows. Reopen this step
only when new packs enter the dashboard without an upgrade recipe.

### 1. Boolean CNF/LRAT

First targets:

- [graph-coloring-v0](../../artifacts/examples/math/graph-coloring-v0/) (first
  DIMACS-backed DRAT/LRAT regression landed for triangle non-2-colorability)
- [finite-sets-v0](../../artifacts/examples/math/finite-sets-v0/)
  (solver-reuse promotion landed for malformed distributive-law rejection:
  source-linked DIMACS artifact, DRAT emission, LRAT elaboration, and
  independent checks)
- [proof-methods-patterns-v0](../../artifacts/examples/math/proof-methods-patterns-v0/)
  (solver-reuse promotion landed for contradiction/refutation: source-linked
  DIMACS artifact, DRAT emission, LRAT elaboration, and independent checks)
- [proof-methods-refutation-v0](../../artifacts/examples/math/proof-methods-refutation-v0/)
  (solver-reuse promotion landed for `PHP(3,2)`: source-linked pigeonhole
  DIMACS artifact, DRAT emission, LRAT elaboration, and independent checks)
- [counting-v0](../../artifacts/examples/math/counting-v0/)
  (solver-reuse promotion landed for `pigeonhole-3-2-unsat`: source-linked
  PHP(3,2) DIMACS artifact, DRAT emission, LRAT elaboration, and independent
  checks)
- [logic-basics-v0](../../artifacts/examples/math/logic-basics-v0/)
  (solver-reuse promotion landed for `tiny-cnf-refutation`: source-linked
  DIMACS artifact, DRAT emission, LRAT elaboration, and independent checks)
- [finite-predicate-v0](../../artifacts/examples/math/finite-predicate-v0/)
  (solver-reuse promotion landed for `forall-implies-exists-finite`:
  source-linked finite quantifier-expansion DIMACS artifact, DRAT emission,
  LRAT elaboration, and independent checks)
- [finite-cardinality-v0](../../artifacts/examples/math/finite-cardinality-v0/)
  (solver-reuse promotion landed for `no-injection-four-to-three`: source-linked
  4-into-3 injective-function DIMACS artifact, DRAT emission, LRAT elaboration,
  and independent checks)
- [graph-matching-v0](../../artifacts/examples/math/graph-matching-v0/)
  (solver-reuse promotion landed for `triangle-no-perfect-matching`:
  source-linked `K3` exact-cover DIMACS artifact, DRAT emission, LRAT
  elaboration, and independent checks)
- [graph-reachability-v0](../../artifacts/examples/math/graph-reachability-v0/)
  (solver-reuse promotion landed for `disconnected-no-path`: source-linked
  bounded reachability fixed-point DIMACS artifact, DRAT emission, LRAT
  elaboration, and independent checks)
- [graph-cut-v0](../../artifacts/examples/math/graph-cut-v0/)
  (solver-reuse promotion landed for `one-edge-cut-rejected`: source-linked
  bounded post-removal reachability DIMACS artifact, DRAT emission, LRAT
  elaboration, and independent checks)
- [graph-d-separation-v0](../../artifacts/examples/math/graph-d-separation-v0/)
  (solver-reuse promotion landed for `chain-conditioned-blocks`: source-linked
  conditioned non-collider blocking DIMACS artifact, DRAT emission, LRAT
  elaboration, and independent checks)
- [finite-compactness-v0](../../artifacts/examples/math/finite-compactness-v0/)
  (solver-reuse promotion landed for `bad-open-cover-rejected`: source-linked
  finite open-cover DIMACS artifact, DRAT emission, LRAT elaboration, and
  independent checks)
- [finite-connectedness-v0](../../artifacts/examples/math/finite-connectedness-v0/)
  (solver-reuse promotion landed for `bad-connected-claim-rejected`:
  source-linked finite connectedness DIMACS artifact, DRAT emission, LRAT
  elaboration, and independent checks)
- [finite-topology-v0](../../artifacts/examples/math/finite-topology-v0/)
  (solver-reuse promotion landed for `bad-empty-open-rejected`: source-linked
  missing-empty-set DIMACS artifact, DRAT emission, LRAT elaboration, and
  independent checks)
- [finite-order-lattices-v0](../../artifacts/examples/math/finite-order-lattices-v0/)
  (solver-reuse promotion landed for `bad-top-element-rejected`: source-linked
  Boolean-lattice top-element DIMACS artifact, DRAT emission, LRAT elaboration,
  and independent checks)

Secondary targets:

- pigeonhole/counting rows are now represented by proof-methods refutation and
  counting, and topology/order/set-family Boolean rows are now represented by
  finite compactness, finite connectedness, finite topology, and finite
  order/lattices; pick the next Boolean CNF target only when the finite encoding
  is source-level obvious and not better expressed as finite replay.

Expected artifact:

- a deterministic CNF encoding for the finite refutation;
- a checked DRAT or LRAT certificate for the concrete CNF;
- a lesson note that separates graph/set/pigeonhole encoding trust from proof
  checking of the generated CNF.

Validation:

```sh
cargo test -p axeyum-cnf drat
cargo test -p axeyum-cnf lrat
cargo test -p axeyum-cnf --test math_resource_boolean_routes boolean_resource_route_rejects_tampered_drat_and_lrat
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sets-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-patterns-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/counting-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/logic-basics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-cardinality-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-matching-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-reachability-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-cut-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-d-separation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-compactness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-connectedness-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-topology-v0
cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_refutation_php_3_2_emits_checked_drat_and_lrat
cargo test -p axeyum-cnf --test math_resource_boolean_routes counting_pigeonhole_3_2_emits_checked_drat_and_lrat
cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_topology_bad_empty_open_emits_checked_drat_and_lrat
./scripts/check-foundational-resources.sh
```

Graduation:

- every upgraded unsat row links to a concrete proof artifact or generation
  recipe;
- corrupted or missing certificates are rejected by tests;
- the learner page names the trust boundary: encoder plus search are not the
  trusted core; the certificate checker is.

### 2. QF_LRA/Farkas

First targets:

- [rationals-lra-v0](../../artifacts/examples/math/rationals-lra-v0/)
  (source-linked solver-reuse promotion landed for fixed trichotomy and
  order-transitivity refutations)
- [linear-algebra-rational-v0](../../artifacts/examples/math/linear-algebra-rational-v0/)
  (source-linked solver-reuse promotion landed for the singular inconsistent
  system)
- [linear-optimization-v0](../../artifacts/examples/math/linear-optimization-v0/)
  (source-linked solver-reuse promotion landed for the objective-threshold
  conflict)
- [convexity-rational-v0](../../artifacts/examples/math/convexity-rational-v0/)
  (source-linked solver-reuse promotion landed for the bad midpoint-convexity
  row)
- [finite-concentration-v0](../../artifacts/examples/math/finite-concentration-v0/)
  (source-linked solver-reuse promotion landed for the bad finite tail-bound
  row)
- [finite-probability-v0](../../artifacts/examples/math/finite-probability-v0/)
  (resource-backed Farkas regressions landed for the bad normalization row and
  the bad Bayes-posterior row)
- [finite-measure-v0](../../artifacts/examples/math/finite-measure-v0/)
  (resource-backed Farkas regression landed for the bad complement-measure row
  after exact finite-measure replay computes the event and total measures)
- [finite-measure-monotonicity-v0](../../artifacts/examples/math/finite-measure-monotonicity-v0/)
  (resource-backed Farkas regression landed for the bad subset-measure row
  after exact finite-measure replay computes the subset and superset measures)
- [finite-integration-v0](../../artifacts/examples/math/finite-integration-v0/)
  (resource-backed Farkas regression landed for the bad expectation row after
  exact finite weighted-sum replay computes the integral)
- [calculus-riemann-sum-v0](../../artifacts/examples/math/calculus-riemann-sum-v0/)
  (source-linked Farkas regression landed for the bad exact
  polynomial-integral row after antiderivative replay computes the integral)
- [calculus-algebraic-shadow-v0](../../artifacts/examples/math/calculus-algebraic-shadow-v0/)
  (source-linked Farkas regression landed for the bad derivative-value row
  after exact polynomial derivative replay computes the derivative at a point)
- [complex-plane-transforms-v0](../../artifacts/examples/math/complex-plane-transforms-v0/)
  (source-linked Farkas regression landed for the bad unit-square real-part
  row after exact real-pair replay computes `i^2 = -1`)
- [complex-algebraic-v0](../../artifacts/examples/math/complex-algebraic-v0/)
  (source-linked Farkas regression landed for the bad norm-squared row after
  exact real-pair replay computes `|3 + 4i|^2 = 25`)
- [multivariable-calculus-rational-v0](../../artifacts/examples/math/multivariable-calculus-rational-v0/)
  (source-linked Farkas regression landed for the bad gradient-component row
  after exact bivariate polynomial derivative replay computes the gradient)
- [sequence-limit-shadow-v0](../../artifacts/examples/math/sequence-limit-shadow-v0/)
  (source-linked Farkas regression landed for the bounded Cauchy-tail
  no-counterexample row after exact finite replay computes the maximum pairwise
  distance)
- [bounded-monotone-sequence-v0](../../artifacts/examples/math/bounded-monotone-sequence-v0/)
  (source-linked Farkas regression landed for the bad upper-bound row after
  exact finite-prefix replay computes the offending sequence value)
- [finite-recurrence-prefix-v0](../../artifacts/examples/math/finite-recurrence-prefix-v0/)
  (source-linked Farkas regression landed for the bad finite recurrence value
  after exact prefix replay computes `F_6 = 8`)
- [finite-root-finding-v0](../../artifacts/examples/math/finite-root-finding-v0/)
  (source-linked Farkas regression landed for the bad Newton-step row after
  exact root-finding replay computes the next iterate `17/12`)
- [finite-separation-v0](../../artifacts/examples/math/finite-separation-v0/)
  (source-linked Farkas regression landed for the bad separator row after
  exact convex-hull/separator replay computes the outside score `4`)
- [finite-kkt-v0](../../artifacts/examples/math/finite-kkt-v0/)
  (source-linked Farkas regression landed for the bad stationarity row after
  exact constrained-quadratic KKT replay computes stationarity residual `-1`
  and stationarity error `1`)
- [finite-active-set-qp-v0](../../artifacts/examples/math/finite-active-set-qp-v0/)
  (source-linked Farkas regression landed for the bad free-gradient row after
  exact active-face replay computes stationarity error `2`)
- [finite-sdp-v0](../../artifacts/examples/math/finite-sdp-v0/)
  (source-linked Farkas regression landed for the bad objective row after exact
  two-by-two SDP replay computes objective value `1` and objective error `1`)
- [finite-gradient-descent-v0](../../artifacts/examples/math/finite-gradient-descent-v0/)
  (source-linked Farkas regression landed for the bad decrease row after exact
  quadratic descent replay computes decrease `11/4` and decrease error `3/4`)
- [finite-line-search-v0](../../artifacts/examples/math/finite-line-search-v0/)
  (source-linked Farkas regression landed for the bad Armijo row after exact
  line-search replay computes rejected-step violation `1`)
- [finite-wolfe-line-search-v0](../../artifacts/examples/math/finite-wolfe-line-search-v0/)
  (source-linked Farkas regression landed for the bad curvature row after exact
  Wolfe replay computes curvature violation `2`)
- [finite-projected-gradient-v0](../../artifacts/examples/math/finite-projected-gradient-v0/)
  (source-linked Farkas regression landed for the bad projection row after
  exact projected-gradient replay rejects `3/2` for the interval `[0,1]`)
- [finite-proximal-gradient-v0](../../artifacts/examples/math/finite-proximal-gradient-v0/)
  (source-linked Farkas regression landed for the bad proximal point row after
  exact L1 soft-threshold replay computes residual `-3/2` for the malformed
  point)
- [finite-product-measure-v0](../../artifacts/examples/math/finite-product-measure-v0/)
  (resource-backed Farkas regression landed for the bad product-probability
  row after exact finite product replay computes the product mass)
- [finite-random-variables-v0](../../artifacts/examples/math/finite-random-variables-v0/)
  (resource-backed Farkas regression landed for the bad pushforward-distribution
  row after exact finite random-variable replay computes the outcome mass)
- [finite-martingales-v0](../../artifacts/examples/math/finite-martingales-v0/)
  (resource-backed Farkas regression landed for the bad martingale row after
  exact finite filtration replay computes the up-block conditional expectation)
- [finite-markov-chain-v0](../../artifacts/examples/math/finite-markov-chain-v0/)
  (resource-backed Farkas regression landed for the bad stochastic row)
- [finite-hitting-times-v0](../../artifacts/examples/math/finite-hitting-times-v0/)
  (source-linked solver-reuse promotion landed for the bad expected-time row)
- [least-squares-regression-v0](../../artifacts/examples/math/least-squares-regression-v0/)
  (resource-backed Farkas regression landed for the bad coefficient row)
- [real-analysis-rational-v0](../../artifacts/examples/math/real-analysis-rational-v0/)
  (resource-backed Farkas regression landed for the bad linear-delta row)
- [metric-continuity-v0](../../artifacts/examples/math/metric-continuity-v0/)
  (resource-backed Farkas regression landed for the finite metric-space
  bad-delta row)
- [finite-conditional-expectation-v0](../../artifacts/examples/math/finite-conditional-expectation-v0/)
  (source-linked solver-reuse promotion landed for the bad high-block table)
- [finite-stochastic-kernels-v0](../../artifacts/examples/math/finite-stochastic-kernels-v0/)
  (resource-backed Farkas regression landed for the bad kernel-row
  normalization conflict)
- [finite-euler-method-v0](../../artifacts/examples/math/finite-euler-method-v0/)
  (source-linked solver-reuse promotion landed for the bad fixed-step transition)
- [orientation-area-geometry-v0](../../artifacts/examples/math/orientation-area-geometry-v0/)
  (resource-backed Farkas regression landed for the bad fixed-orientation row)
- [numerical-linear-algebra-v0](../../artifacts/examples/math/numerical-linear-algebra-v0/)
  (resource-backed Farkas regression landed for the bad residual-bound row)
- [random-matrix-finite-v0](../../artifacts/examples/math/random-matrix-finite-v0/)
  (resource-backed Farkas regression landed for the bad trace-square moment
  row)
- [affine-geometry-v0](../../artifacts/examples/math/affine-geometry-v0/)
  (resource-backed Farkas regression landed for the bad distance-preservation
  row)
- [coordinate-geometry-v0](../../artifacts/examples/math/coordinate-geometry-v0/)
  (source-linked Farkas regression landed for the bad squared-distance row
  after exact coordinate replay computes the squared distance)
- [finite-circle-geometry-v0](../../artifacts/examples/math/finite-circle-geometry-v0/)
  (source-linked Farkas regression landed for the bad radius row after exact
  coordinate replay computes the squared radius)
- [finite-inversion-geometry-v0](../../artifacts/examples/math/finite-inversion-geometry-v0/)
  (source-linked Farkas regression landed for the bad inverse-coordinate row
  after exact inversion replay computes the inverse x-coordinate)
- [finite-cyclic-geometry-v0](../../artifacts/examples/math/finite-cyclic-geometry-v0/)
  (source-linked Farkas regression landed for the bad diagonal-intersection row
  after exact cyclic-configuration replay computes the intersection
  x-coordinate)
- [finite-operator-v0](../../artifacts/examples/math/finite-operator-v0/)
  (source-linked Farkas regression landed for the bad operator-bound row after
  exact matrix/operator replay computes the image infinity norm)
- [inner-product-spaces-rational-v0](../../artifacts/examples/math/inner-product-spaces-rational-v0/)
  (resource-backed Farkas regression landed for the bad negative-norm row)
- [spectral-linear-algebra-v0](../../artifacts/examples/math/spectral-linear-algebra-v0/)
  (resource-backed Farkas regression landed for the bad eigenpair row)
- [matrix-invariants-v0](../../artifacts/examples/math/matrix-invariants-v0/)
  (resource-backed Farkas regression landed for the bad characteristic
  polynomial row)
- [finite-chebyshev-systems-v0](../../artifacts/examples/math/finite-chebyshev-systems-v0/)
  (resource-backed Farkas regression landed for the duplicate-node determinant
  conflict)
- [polynomial-factorization-rational-v0](../../artifacts/examples/math/polynomial-factorization-rational-v0/)
  (resource-backed Farkas regression landed for the fixed irreducible-quadratic
  discriminant conflict after exact replay computes `D = -4`)
- [reals-rcf-shadow-v0](../../artifacts/examples/math/reals-rcf-shadow-v0/)
  (resource-backed Farkas regression landed for the fixed
  negative-discriminant no-real-root conflict after exact polynomial replay
  computes `D = -4`)

Secondary targets:

- first secondary QF_LRA/Farkas target set covered; finite Chebyshev-system
  determinant replay now contributes a functional-analysis/numerical-analysis
  exact-linear regression, metric-continuity now contributes a topology /
  epsilon-delta exact-linear regression, and finite stochastic kernels now
  contribute a probability/statistics transition-row normalization regression.
  Finite integration now contributes a measure-theory expectation regression,
  calculus algebraic shadows now contribute a real-analysis/numerical-analysis
  derivative-value regression, calculus Riemann sums now contribute a
  real-analysis/numerical-analysis polynomial-integral regression, and complex
  algebraic plus complex plane transforms now contribute real-pair algebra
  exact-linear regressions,
  finite product measure contributes a product-probability exact-linear
  regression where the nonlinear product itself is replayed before Farkas checks
  the final contradictory masses, and finite random variables contribute a
  pushforward-distribution regression with the same replay-then-Farkas boundary.
  Finite martingales now add the stochastic-process version of that pattern:
  replay a conditional expectation from a finite filtration, then let Farkas
  check the contradictory martingale equality. Finite measure now contributes
  the base measure-table version of that pattern: replay the event and total
  measures, then let Farkas check the false complement-additivity claim.
  Polynomial factorization now contributes the algebra version of the same
  pattern: replay the discriminant exactly, then let Farkas check the final
  nonnegative-discriminant conflict.
  The RCF-shadow pack now contributes the real-algebra version of that same
  boundary: replay the fixed quadratic discriminant, then let Farkas check the
  nonnegative-discriminant contradiction while keeping general SOS/CAD/RCF
  proof as a horizon.
  Coordinate geometry now contributes the geometry version of the
  replay-then-Farkas boundary: exact replay computes the squared distance, then
  Farkas checks the final bad-distance equality conflict.
  Finite cyclic geometry now contributes the cyclic-configuration version of
  that boundary: exact replay computes circle membership, diagonal midpoints,
  and angle dot products, then Farkas checks the final bad-intersection
  equality conflict.
  Finite operators now contribute the functional-analysis version of that
  boundary: exact replay computes the matrix image and infinity norm, then
  Farkas checks the final bad-bound inequality conflict.
  Finite root finding now contributes the numerical-analysis version of that
  boundary: exact replay computes the bisection/Newton data and the next
  iterate, then Farkas checks the final bad-step equality conflict.
  Finite separation now contributes the convex-optimization version of that
  boundary: exact replay computes convex weights, separator scores, and the
  tight face, then Farkas checks the final bad-separator inequality conflict.
  Finite KKT now contributes the active-set/stationarity version of that
  boundary: exact replay computes the derivative, multiplier equation, and
  complementary-slackness product, then Farkas checks the final bad-stationarity
  error conflict.
  Finite SDP now contributes the primal/dual-slack version of that boundary:
  exact replay computes two-by-two PSD minors, trace/objective arithmetic,
  slack PSD, and zero gap, then Farkas checks the final bad-objective error
  conflict.
  Finite gradient descent now contributes the algorithm-step version of that
  boundary: exact replay computes the gradient, step update, objective
  decrease, and descent-bound slack, then Farkas checks the final bad-decrease
  error conflict.

Expected artifact:

- an `UnsatFarkas` certificate for infeasible exact-rational systems;
- exact-rational replay for satisfiable witnesses and equality identities;
- Lean reconstruction only for covered generated modules.

Validation:

```sh
cargo test -p axeyum-solver --test evidence lra_unsat_evidence_carries_a_recheckable_farkas_certificate
cargo test -p axeyum-solver --test evidence tampered_farkas_evidence_fails_its_own_check
cargo test -p axeyum-solver --test math_resource_lra_routes qf_lra_resource_route_rejects_tampered_farkas_certificate
cargo test -p axeyum-solver --test math_resource_lra_routes coordinate_geometry_bad_distance_squared_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_cyclic_geometry_bad_diagonal_intersection_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_operator_bad_operator_bound_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_root_finding_bad_newton_step_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_separation_bad_separator_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_kkt_bad_stationarity_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes finite_gradient_descent_bad_decrease_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test math_resource_lra_routes complex_algebraic_bad_norm_squared_artifact_emits_checked_farkas
cargo test -p axeyum-solver --test lean_crosscheck certified_lra_interpolant_both_farkas_certs_checked_by_real_lean
./scripts/check-foundational-resources.sh
```

Graduation:

- infeasible linear systems carry independently checked rational multipliers;
- nonlinear or general-analysis claims stay replay-only or Lean-horizon unless
  the row has been reduced to a linear certificate with explicit lowering
  evidence;
- polynomial-factorization rows state whether the checked object is exact
  coefficient/division/GCD replay, a QF_LRA discriminant conflict, or general
  factorization theory in the Lean-horizon lane;
- RCF-shadow rows state whether the checked object is exact rational replay, a
  fixed algebraic certificate shape, a QF_LRA discriminant conflict, or a
  broader SOS/CAD/RCF horizon;
- dashboards show fewer QF_LRA/Farkas replay-only rows.

### 3. QF_UF/Alethe

First targets:

- [equivalence-classes-v0](../../artifacts/examples/math/equivalence-classes-v0/)
  (resource-backed QF_UF/Alethe regression landed for quotient-map congruence;
  the route-anatomy lesson now follows this same source artifact through
  zero-trust `UnsatAletheProof` checking and truncated-proof rejection)
- [relations-functions-v0](../../artifacts/examples/math/relations-functions-v0/)
  (resource-backed QF_UF/Alethe regression landed for function single-valuedness)
- [finite-groups-v0](../../artifacts/examples/math/finite-groups-v0/)
  (resource-backed QF_UF/Alethe regression landed for binary-operation congruence)
- [function-composition-v0](../../artifacts/examples/math/function-composition-v0/)
  (resource-backed QF_UF/Alethe regression landed for composition application)
- [finite-algebra-homomorphisms-v0](../../artifacts/examples/math/finite-algebra-homomorphisms-v0/)
  (resource-backed QF_UF/Alethe regression landed for homomorphism preservation)
- [finite-monoids-v0](../../artifacts/examples/math/finite-monoids-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad associativity conflict)
- [finite-order-lattices-v0](../../artifacts/examples/math/finite-order-lattices-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad antisymmetry
  conflict; the separate bad top-element set-family conflict is promoted
  through the Boolean CNF/LRAT route above)
- [finite-permutation-groups-v0](../../artifacts/examples/math/finite-permutation-groups-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad nonbijection conflict)
- [finite-vector-spaces-v0](../../artifacts/examples/math/finite-vector-spaces-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad subspace-closure conflict)
- [finite-dual-spaces-v0](../../artifacts/examples/math/finite-dual-spaces-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad covector-additivity conflict)
- [finite-modules-v0](../../artifacts/examples/math/finite-modules-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad submodule scalar-closure conflict)
- [finite-ideals-v0](../../artifacts/examples/math/finite-ideals-v0/)
  (resource-backed QF_UF/Alethe regressions landed for the bad ideal
  additive-closure conflict and quotient-ring representative congruence)
- [finite-tensor-products-v0](../../artifacts/examples/math/finite-tensor-products-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad bilinear left-additivity conflict)
- [finite-group-actions-v0](../../artifacts/examples/math/finite-group-actions-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad identity-action conflict)
- [finite-continuous-maps-v0](../../artifacts/examples/math/finite-continuous-maps-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad preimage-membership conflict)
- [finite-quotient-topology-v0](../../artifacts/examples/math/finite-quotient-topology-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad
  quotient-open conflict after finite quotient-preimage replay)
- [finite-specialization-order-v0](../../artifacts/examples/math/finite-specialization-order-v0/)
  (resource-backed QF_UF/Alethe regression landed for the false `T0`
  specialization antisymmetry conflict)
- [finite-simplicial-cohomology-v0](../../artifacts/examples/math/finite-simplicial-cohomology-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad F2
  coboundary-value conflict)
- [finite-universal-coefficient-shadow-v0](../../artifacts/examples/math/finite-universal-coefficient-shadow-v0/)
  (resource-backed QF_UF/Alethe regression landed for the bad
  `H^1 = 0` group-identification conflict after finite Hom/Ext replay)

Secondary targets:

- initial module/ideal/tensor equality-heavy secondary set is covered, including
  the finite-ideals quotient representative congruence row and the finite
  group-action identity row; the topology lane now has small preimage-membership,
  quotient-open-status, specialization-antisymmetry, cohomology coboundary-value, and finite
  universal-coefficient group-identity EUF certificates.
  Pick the next equality-heavy pack only when it exposes a small fixed EUF
  certificate.

Expected artifact:

- an Alethe proof for the congruence conflict or functional-consistency step;
- zero-trust or explicitly accounted trust-step evidence;
- finite model replay for satisfiable structure-table witnesses.

Validation:

```sh
cargo test -p axeyum-solver --test math_resource_uf_routes
cargo test -p axeyum-solver --test math_resource_uf_routes qf_uf_resource_route_rejects_tampered_alethe_certificate
cargo test -p axeyum-solver --test math_resource_uf_routes equivalence_classes_quotient_map_congruence_emits_checked_alethe
cargo test -p axeyum-solver --test math_resource_uf_routes finite_quotient_topology_bad_open_emits_checked_alethe
cargo test -p axeyum-solver --test math_resource_uf_routes finite_specialization_order_bad_t0_antisymmetry_emits_checked_alethe
cargo test -p axeyum-solver --test math_resource_uf_routes finite_simplicial_cohomology_bad_coboundary_value_emits_checked_alethe
cargo test -p axeyum-solver --test math_resource_uf_routes finite_universal_coefficient_bad_h1_zero_emits_checked_alethe
cargo test -p axeyum-solver --test evidence qf_ufbv_unsat_carries_a_zero_trust_alethe_certificate
cargo test -p axeyum-solver --test evidence qf_uf_declared_sort_equality_unsat_carries_zero_trust_alethe_certificate
cargo test -p axeyum-solver --test lean_crosscheck qf_uf_declared_sort_equality_checks_in_real_lean
cargo test -p axeyum-solver --test lean_crosscheck qf_ufbv_refutation_checks_in_real_lean
./scripts/check-foundational-resources.sh
```

Graduation:

- the proof route derives the congruence step rather than trusting an
  Ackermannized rewrite silently;
- pack metadata distinguishes finite algebra-table replay from the general
  algebra theorem horizon;
- learner pages show how the finite witness relates to the broader structure.

### 4. QF_LIA/Diophantine

First targets:

- [modular-arithmetic-v0](../../artifacts/examples/math/modular-arithmetic-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the nonunit inverse
  obstruction; the route-anatomy lesson now follows this same source artifact
  through `UnsatDiophantine` checking and contradiction-row tamper rejection)
- [exact-statistical-tests-v0](../../artifacts/examples/math/exact-statistical-tests-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the bad binomial
  tail-count row)
- [finite-simplicial-homology-v0](../../artifacts/examples/math/finite-simplicial-homology-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the bad boundary
  coefficient row)
- [finite-chain-complex-torsion-v0](../../artifacts/examples/math/finite-chain-complex-torsion-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the bad torsion
  generator row after exact Smith/torsion replay isolates `2*k = 1`)
- [induction-patterns-v0](../../artifacts/examples/math/induction-patterns-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the finite
  even-product parity obstruction)
- [descriptive-statistics-v0](../../artifacts/examples/math/descriptive-statistics-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the bad
  contingency-table total row)
- [generating-functions-v0](../../artifacts/examples/math/generating-functions-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the bad finite
  Cauchy-product coefficient row)
- [polynomial-identities-v0](../../artifacts/examples/math/polynomial-identities-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the false
  rational-root row)
- [integer-lia-v0](../../artifacts/examples/math/integer-lia-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the
  `2*x + 4*y = 3` gcd divisibility obstruction)
- [cardinality-principles-v0](../../artifacts/examples/math/cardinality-principles-v0/)
  (resource-backed QF_LIA/Diophantine regression landed for the
  overlap-additivity count contradiction after finite replay computes
  `|A union B| = 4` but the malformed disjoint-additivity row claims `6`)

Related checked integer-arithmetic solver-reuse promotion:

- [induction-obligations-v0](../../artifacts/examples/math/induction-obligations-v0/)
  (resource-backed `UnsatArithDpll` regression landed for the bounded
  bad-step count row after finite replay computes zero prefix-sum step
  counterexamples; this is a bounded-count LIA refutation, not a
  Diophantine-equality certificate)
- [graph-search-runtime-v0](../../artifacts/examples/math/graph-search-runtime-v0/)
  (resource-backed `UnsatArithDpll` regression landed for the bad finite DFS
  cost-bound row; this is a Boolean-structured LIA refutation, not a
  Diophantine-equality certificate)
- [natural-arithmetic-v0](../../artifacts/examples/math/natural-arithmetic-v0/)
  (resource-backed `UnsatArithDpll` regression landed for the bad bounded
  negative-domain row; this is a bounded-domain LIA refutation, not a
  Diophantine-equality certificate)

Reference packs already on the route:

- [gcd-bezout-v0](../../artifacts/examples/math/gcd-bezout-v0/)
  (source-linked solver-reuse promotion landed for the fixed Diophantine gcd
  obstruction)
- [number-theory-v0](../../artifacts/examples/math/number-theory-v0/)

Expected artifact:

- an `UnsatDiophantine` certificate for integer equality systems;
- integer-interval Lean reconstruction for covered inequality slices;
- finite replay for rows that are count or coefficient enumeration rather than
  a solver-form LIA contradiction.
- an `UnsatArithDpll` certificate for bounded-domain or bounded-count
  inequality contradictions.

Validation:

```sh
cargo test -p axeyum-solver diophantine
cargo test -p axeyum-solver certificate_tamper_is_rejected
cargo test -p axeyum-solver --test math_resource_lia_routes qf_lia_resource_route_rejects_tampered_diophantine_certificate
cargo test -p axeyum-solver --test math_resource_lia_routes modular_nonunit_inverse_emits_checked_diophantine_evidence
cargo test -p axeyum-solver --test math_resource_lia_routes finite_chain_complex_torsion_bad_generator_emits_checked_diophantine_evidence
cargo test -p axeyum-solver --test int_inequality_lean_reconstruct
cargo test -p axeyum-solver --test math_resource_lia_routes
./scripts/check-foundational-resources.sh
```

Graduation:

- upgraded rows record the normalized integer system and the divisibility
  obstruction;
- modular examples do not claim proof status until they emit solver-form
  evidence or an explicitly checked finite table;
- homology rank rows state whether the checked object is integer linear
  algebra, finite boundary replay, or the general homology Lean horizon.
- induction-obligation rows state whether the checked object is finite
  obligation replay, a QF_LIA bad-step count contradiction, or the full
  induction-schema Lean horizon.
- generating-function rows state whether the checked object is finite
  coefficient replay, a QF_LIA coefficient contradiction, or a general
  generating-function Lean horizon.
- polynomial-identity rows state whether the checked object is coefficient or
  factor replay, a QF_LIA false-root contradiction, or a general
  polynomial-theory Lean horizon.
- cardinality-principle rows state whether the checked object is finite count
  replay, a QF_LIA count contradiction, or an infinite-cardinality Lean horizon.

### 5. QF_BV Bit-Blast

First targets:

- [finite-rings-v0](../../artifacts/examples/math/finite-rings-v0/)
  (resource-backed QF_BV/DRAT regressions landed for the bad distributivity and
  bad multiplicative-identity rows)
- [finite-fields-v0](../../artifacts/examples/math/finite-fields-v0/)
  (resource-backed QF_BV/DRAT regressions landed for the composite-modulus
  no-inverse row and the bad prime-field inverse-candidate row; the
  route-anatomy lesson follows these source artifacts through DIMACS/DRAT
  checking and truncated-proof rejection)
- [graph-coloring-v0](../../artifacts/examples/math/graph-coloring-v0/)
  (resource-backed QF_BV/DRAT regression landed for the one-bit triangle
  two-coloring obstruction)
- [number-theory-v0](../../artifacts/examples/math/number-theory-v0/)
  (resource-backed QF_BV/DRAT regression landed for the modulo-7 quadratic
  nonresidue row)
- [finite-simplicial-cup-products-v0](../../artifacts/examples/math/finite-simplicial-cup-products-v0/)
  (resource-backed QF_BV/DRAT regression landed for the one-bit F2
  cup-product value conflict)

Secondary targets:

- first QF_BV bit-blast target set plus the bounded number-theory residue
  promotion are covered; pick the next fixed-width pack only when the BV
  encoding teaches a distinct finite-domain claim rather than duplicating a
  cleaner CNF/LRA/LIA route.

Expected artifact:

- model replay against original terms for satisfiable rows;
- checked DRAT evidence for generated CNF in unsat rows;
- an explicit trust-step ledger for bit-blast/Tseitin lowering until Lean
  reconstruction covers the original formula.

Validation:

```sh
cargo test -p axeyum-solver --test math_resource_bv_routes
cargo test -p axeyum-solver --test math_resource_bv_routes qf_bv_resource_route_rejects_tampered_drat_certificate
cargo test -p axeyum-solver --test math_resource_bv_routes finite_fields_composite_nonfield_emits_checked_drat
cargo test -p axeyum-solver --test math_resource_bv_routes finite_simplicial_cup_product_bad_value_emits_checked_bv_drat
cargo test -p axeyum-solver --test evidence unsat_evidence_carries_a_recheckable_drat_certificate
cargo test -p axeyum-solver --test evidence qf_bv_drat_unsat_reports_bitblast_tseitin_sat_steps
./scripts/check-foundational-resources.sh
```

Graduation:

- SAT rows replay lifted models on the source-level finite algebra term;
- unsat rows carry checked CNF evidence and do not overclaim Lean kernel
  coverage for the lowering;
- BV routes are used only where fixed finite width is part of the educational
  claim.

### 6. Lean Horizon Families

First theorem families:

- induction schemas beyond bounded base/step obligations;
- real limits, epsilon-delta continuity, compactness, connectedness, and
  integration;
- finite shadows of measure, probability, martingales, stochastic kernels, and
  hitting times where the general theorem is countable or limiting;
- general algebra and topology statements;
- Chebyshev spaces, operator theory, complex analysis, and functional-analysis
  claims.

Expected artifact:

- a Lean module with no `sorry`;
- a concrete check command beside the graduated resource;
- an axiom audit for exported theorem statements.

Graduation:

- finite shadows continue to validate through their example-pack checks;
- the unbounded theorem stays `lean-horizon` until the Lean command exists and
  passes;
- a Lean file depending on `sorryAx` does not graduate.

## Per-Pack Definition Of Done

A proof upgrade is complete only when all of these are true:

- `metadata.json` names the route in `source_refs` and the relevant
  graduation criteria;
- every upgraded expected-result row has explicit evidence status;
- route-specific tests pass or a generated resource validator checks the
  emitted artifact;
- the learner page states what is trusted and what remains a horizon;
- `python3 scripts/validate-foundational-example-pack.py <pack>` passes;
- `./scripts/check-foundational-resources.sh` regenerates dashboards cleanly;
- `./scripts/check-links.sh` passes.

## Non-Goals

- Do not turn every replay-only row into a proof-object row. SAT witnesses and
  finite-model replay are valid checked evidence when the claim is satisfiable
  or explicitly finite.
- Do not promote general analysis, topology, probability, algebra, or
  functional-analysis theorems from finite shadows to proved results without a
  Lean artifact.
- Do not hide lowering trust behind a solver verdict. If a route depends on
  bit-blasting, CNF encoding, table generation, or abstraction, name the trusted
  and untrusted parts in metadata and lessons.

## Maintenance

Regenerate the mechanical view before choosing the next proof-upgrade target:

```sh
./scripts/check-foundational-resources.sh
```

Then compare this plan with
[proof-gap-dashboard.md](generated/proof-gap-dashboard.md) and
[learner-proof-upgrade-dashboard.md](generated/learner-proof-upgrade-dashboard.md).
When route counts move materially, update this frontier in the same commit as
the pack upgrade so future agents do not mine stale priorities.
