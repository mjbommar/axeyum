# Archived: Process/documentation lane (through 2026-07-06)

Archived from STATUS.md by the task-#27 truncation; the live head stays in STATUS.md.

## Process/documentation lane (2026-06-27) — `WIP`

- **Finite policy-iteration resource landed.**
  `finite-policy-iteration-v0` now pairs with the value-iteration pack to
  show two algorithms reaching one committed optimum on the same fixed
  three-state discounted MDP: it substitutes each committed policy's value
  vector back into its fixed-point equation for an exact zero residual —
  `(2, 2/3, 0)` for the deliberately suboptimal `(b, b, a)` (a genuine
  linear solve, since `s2` feeds back into `s1` and `s2`), `(2, 3, 0)`,
  then `(5/2, 3, 0)` — replays two greedy improvement rounds and the
  termination-by-stability round at `(a, a, a)`, and checks the
  componentwise monotone improvement ending at the exact optimum shared
  with `finite-value-iteration-v0`; rejects the malformed policy-evaluation
  claim `1/2` against exact `2/3`; and routes that scalar conflict through
  a source-linked QF_LRA/Farkas row. The focused learner page,
  probability/statistics and dynamics query guides, stochastic-kernel,
  value-iteration, policy-iteration, exact-vs-floating, and QF_LRA/Farkas
  bridge rows, validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed finite trace
  separate from the policy-improvement theorem in general, termination and
  optimality theorems, average-reward/continuous MDP theory, stochastic
  approximation, and floating-point dynamic programming. The public summary
  now reports 137 concept rows, 173 packs, 1131 expected checks, 399
  checked rows, 596 replay-only rows, 136 Lean-horizon rows, and 173
  promoted solver-reuse packs.

- **Finite value-iteration resource landed.**
  `finite-value-iteration-v0` now gives the probability, dynamics, and
  optimization lanes a dynamic-programming trace — a new proof shape next to
  the committed-optimum SVM pair and the iterative perceptron trace: it
  replays a fixed three-state, two-action discounted MDP with `gamma = 1/2`
  from the zero value vector, every Bellman backup
  `Q(s, a) = r + gamma * P . V` and greedy maximum across three iterations,
  a greedy-policy switch at `s1` from the myopic to the far-sighted action,
  the exact Bellman fixed point `(5/2, 3, 0)` reproduced by a full backup,
  and the sup-norm contraction steps `3, 1/2, 0`; rejects the malformed
  Bellman-backup claim `2` against exact `5/2`; and routes that scalar
  conflict through a source-linked QF_LRA/Farkas row. All rewards,
  probabilities, and the discount are rational, so the whole trace is exact
  arithmetic and the fixed point is reached exactly — no epsilon threshold.
  The focused learner page, probability/statistics and dynamics query
  guides, stochastic-kernel, value-iteration, exact-vs-floating, and
  QF_LRA/Farkas bridge rows, validator, resource smoke queries, generated
  dashboards, and `math_resource_lra_routes` regression keep this fixed
  finite trace separate from the Banach fixed-point theorem,
  value-iteration convergence in general, optimality/uniqueness theorems,
  stochastic approximation, and floating-point dynamic programming. At
  that landing, the public summary reported 136 concept rows, 172 packs,
  1124 expected checks, 398 checked rows, 591 replay-only rows, 135
  Lean-horizon rows, and 172 promoted solver-reuse packs.

- **Finite hard-margin SVM resource landed.**
  `finite-hard-margin-svm-v0` now gives the statistics, optimization, and
  linear-algebra lanes a committed-optimum primal-dual pair — a new proof
  shape next to the iterative perceptron trace and the closed-form
  ridge/LDA classifier packs: it replays a six-point linearly separable
  training set with the committed maximum-margin hyperplane
  `w = (1/2, 1/2)`, `b = -1`, every functional margin
  `1, 1, 2, 3/2, 2, 2` with the support vectors exactly on the margin, the
  KKT stationarity, multiplier-balance, and complementary-slackness
  identities, and the zero primal-dual objective gap `1/4 = 1/4`; rejects
  the malformed maximum-margin bias claim `-1/2` against exact `-1`; and
  routes that scalar conflict through a source-linked QF_LRA/Farkas row.
  All coordinates, weights, multipliers, margins, and objectives are
  rational, so the whole primal-dual pair is exact arithmetic; the
  geometric margin (which divides by the irrational norm `sqrt(2)`) stays
  explicitly out of scope. The focused learner page, probability/statistics
  query guide, probability-mass-table, SVM, exact-vs-floating, and
  QF_LRA/Farkas bridge rows, validator, resource smoke queries, generated
  dashboards, and `math_resource_lra_routes` regression keep this fixed
  finite replay separate from strong duality, KKT sufficiency,
  maximum-margin optimality, soft-margin/kernel variants, statistical
  generalization, and floating-point training behavior. At that landing,
  the public summary reported 135 concept rows, 171 packs, 1117 expected
  checks, 397 checked rows, 586 replay-only rows, 134 Lean-horizon rows,
  and 171 promoted solver-reuse packs.

- **Finite perceptron resource landed.**
  `finite-perceptron-v0` now gives the statistics, probability, and
  linear-algebra lanes an iterative learning-algorithm trace — a new proof
  shape next to the closed-form (ridge/LDA), instance-based (kNN), and
  split-based (Gini/entropy) classifier packs: it replays a four-point
  linearly separable training set in augmented coordinates from the zero
  weight vector, every presented dot-product score and mistake condition,
  the two mistake updates ending at weights `(-1, 3, 0)`, and a
  strict-margin convergence pass with functional margins `5, 5, 7, 7`;
  rejects the malformed first-weight-coordinate claim `1` against exact
  `-1`; and routes that scalar conflict through a source-linked
  QF_LRA/Farkas row. All data and updates are integers, so the whole trace
  is exact arithmetic; geometric margins (which divide by the irrational
  norm `sqrt(10)`) stay explicitly out of scope. The focused learner page,
  probability/statistics query guide, probability-mass-table, perceptron,
  exact-vs-floating, and QF_LRA/Farkas bridge rows, validator, resource
  smoke queries, generated dashboards, and `math_resource_lra_routes`
  regression keep this fixed finite trace separate from the Novikoff
  mistake bound, convergence theorems, kernel/averaged/voted variants,
  statistical generalization, and floating-point training behavior. At
  that landing, the public summary reported 134 concept rows, 170 packs,
  1110 expected checks, 396 checked rows, 581 replay-only rows, 133
  Lean-horizon rows, and 170 promoted solver-reuse packs.

- **Finite k-nearest-neighbors resource landed.**
  `finite-k-nearest-neighbors-v0` now gives the statistics, probability, and
  discrete/counting lanes a distance-based classifier example: it replays a
  six-point two-class rational training set with two query points and
  `k = 3`, every squared Euclidean distance (squaring keeps the arithmetic
  rational while preserving the ranking), strict rank gaps `2 < 18` and
  `5 < 13` so no tie policy is needed, the neighbor sets, and the `3-0`
  majority votes; rejects the malformed squared-distance claim `16` against
  exact `18`; and routes that scalar conflict through a source-linked
  QF_LRA/Farkas row. The validator rejects neighbor sets without a strict
  rank gap, so the pack cannot silently smuggle in a tie-breaking policy.
  The focused learner page, probability/statistics query guide,
  probability-mass-table, nearest-neighbor, exact-vs-floating, and
  QF_LRA/Farkas bridge rows, validator, resource smoke queries, generated
  dashboards, and `math_resource_lra_routes` regression keep this fixed
  finite replay separate from nearest-neighbor consistency, Bayes-risk
  bounds, curse-of-dimensionality behavior, metric/weighting/tie policy,
  statistical generalization, and floating-point distance behavior. At that
  landing, the public summary reported 133 concept rows, 169 packs, 1103
  expected checks, 395 checked rows, 576 replay-only rows, 132 Lean-horizon
  rows, and 169 promoted solver-reuse packs.

- **Finite entropy/information-gain resource landed.**
  `finite-entropy-information-gain-v0` now gives the statistics, probability,
  and discrete/counting lanes the entropy-based sibling of the decision-tree
  Gini pack: it replays an eight-row training table whose root and split
  nodes all have class proportions in `{0, 1/2, 1}`, so every `log2` value is
  an integer and every entropy is an exact rational number of bits — root
  entropy `1`, the three-child `color` split weighted entropy `1/2` with
  information gain `1/2`, the `shape` split weighted entropy `1` with gain
  `0`, and the best-split comparison; rejects the malformed weighted-entropy
  claim `3/4`; and routes that scalar conflict through a source-linked
  QF_LRA/Farkas row. The validator rejects any non-dyadic node proportion, so
  the pack cannot silently overclaim entropy arithmetic that would need an
  irrational logarithm. The focused learner page, probability/statistics
  query guide, probability-mass-table, entropy/information-gain,
  decision-tree-Gini, exact-vs-floating, and QF_LRA/Farkas bridge rows,
  validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this dyadic finite replay
  separate from non-dyadic entropy, log-loss and mutual-information variants,
  greedy-optimality, pruning, threshold policy, statistical generalization,
  continuous feature thresholds, and floating-point logarithm behavior. At
  that landing, the public summary reported 132 concept rows, 168 packs,
  1096 expected checks, 394 checked rows, 571 replay-only rows, 131
  Lean-horizon rows, and 168 promoted solver-reuse packs.

- **Finite decision-tree Gini split resource landed.**
  `finite-decision-tree-gini-v0` now gives the statistics, probability, and
  discrete/counting lanes a compact exact training-table example: it replays
  eight classified rows, two binary feature domains, class totals, root Gini
  impurity `1/2`, the `color` split weighted impurity `3/8`, the `shape` split
  weighted impurity `1/2`, and the best-split comparison; rejects the malformed
  weighted-Gini claim `1/2`; and routes that scalar conflict through a
  source-linked QF_LRA/Farkas row. The focused learner page,
  probability/statistics query guide, probability-mass-table,
  finite decision-tree Gini, exact-vs-floating, and QF_LRA/Farkas bridge rows,
  validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed finite split replay
  separate from greedy-tree optimality, pruning, threshold policy,
  entropy/information-gain variants, statistical generalization, continuous
  feature thresholds, and floating-point tree-training behavior. At that
  landing, the public summary reported 131 concept rows, 167 packs, 1089
  expected checks, 393 checked rows, 566 replay-only rows, 130 Lean-horizon
  rows, and 167 promoted solver-reuse packs.

- **Finite calibration/Brier probabilistic-classifier resource landed.**
  `finite-calibration-brier-v0` now gives the statistics and probability lanes
  a compact exact probabilistic-classifier example: it replays six rational
  forecast probabilities, class totals, the fixed `p < 1/2` / `p >= 1/2`
  calibration-bin summaries, expected calibration error `1/10`, and Brier
  score `71/300`; rejects the malformed Brier-score claim `1/5`; and routes
  that scalar conflict through a source-linked QF_LRA/Farkas row. The focused
  learner page, probability/statistics query guide, probability-mass-table,
  finite classifier-metrics, finite calibration/Brier, exact-vs-floating, and
  QF_LRA/Farkas bridge rows, validator, resource smoke queries, generated
  dashboards, and `math_resource_lra_routes` regression keep this fixed finite
  replay separate from binning-policy optimality, model calibration,
  proper-scoring-rule theorems, confidence intervals, continuous
  score-distribution theory, statistical generalization, and floating-point
  classifier behavior. At that landing, the public summary reported 130
  concept rows, 166 packs, 1082 expected checks, 392 checked rows, 561
  replay-only rows, 129 Lean-horizon rows, and 166 promoted solver-reuse packs.

- **Finite precision-recall classifier-ranking resource landed.**
  `finite-precision-recall-v0` now gives the statistics and probability lanes a
  compact exact ranking-metric example: it replays six rational classifier
  scores, descending score order, class totals, the `score >= 7/10` threshold
  precision/recall/F1 point, the precision-recall curve, and average precision
  `34/45`; rejects the malformed average-precision claim `3/4`; and routes
  that scalar conflict through a source-linked QF_LRA/Farkas row. The focused
  learner page, probability/statistics query guide, probability-mass-table,
  exact-vs-floating, finite classifier-metrics, finite ROC/AUC, finite
  precision-recall, and QF_LRA/Farkas bridge rows, validator, resource smoke
  queries, generated dashboards, and `math_resource_lra_routes` regression
  keep this fixed tie-free finite replay separate from threshold policy,
  calibration, confidence intervals, interpolation/tie conventions,
  continuous score-distribution theory, statistical generalization, and
  floating-point classifier-metric behavior. At that landing, the public
  summary reported 129 concept rows, 165 packs, 1075 expected checks, 391
  checked rows, 556 replay-only rows, 128 Lean-horizon rows, and 165 promoted
  solver-reuse packs.

- **Finite ROC/AUC classifier-ranking resource landed.**
  `finite-roc-auc-v0` now gives the statistics and probability lanes a compact
  exact score-ranking example: it replays six rational classifier scores, the
  descending score order, class totals, the `score >= 7/10` threshold operating
  point, TPR/FPR/precision/specificity rates, the ROC staircase, pairwise AUC,
  and trapezoid area; rejects the malformed AUC claim `3/4` versus exact `2/3`;
  and routes that scalar conflict through a source-linked QF_LRA/Farkas row.
  The focused learner page, probability/statistics query guide,
  probability-mass-table, exact-vs-floating, finite classifier-metrics, finite
  ROC/AUC, and QF_LRA/Farkas bridge rows, validator, resource smoke queries,
  generated dashboards, and `math_resource_lra_routes` regression keep this
  fixed tie-free finite replay separate from threshold policy, calibration,
  confidence intervals, general tie conventions, continuous score-distribution
  theory, statistical generalization, and floating-point classifier-metric
  behavior. At that landing, the public summary reported 128 concept rows, 164
  packs, 1068 expected checks, 390 checked rows, 551 replay-only rows, 127
  Lean-horizon rows, and 164 promoted solver-reuse packs.

- **Finite confusion-matrix classifier-metrics resource landed.**
  `finite-confusion-matrix-v0` now gives the statistics and probability lanes
  a compact exact classifier-evaluation example: it replays eight
  actual/predicted rows, TP/FP/TN/FN counts, class totals, accuracy,
  precision, recall/sensitivity, specificity, negative predictive value,
  false-positive/false-negative rates, balanced accuracy, F1, and Jaccard;
  rejects the malformed precision claim `3/4` versus exact `2/3`; and routes
  that scalar conflict through a source-linked QF_LRA/Farkas row. The focused
  learner page, probability/statistics query guide, probability-mass-table,
  exact-vs-floating, finite classifier-metrics, and QF_LRA/Farkas bridge rows,
  validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed finite replay separate
  from calibration, threshold selection, ROC/AUC, confidence intervals,
  statistical generalization, multiclass conventions, and floating-point
  classifier-metric behavior. At that landing, the public summary reported 127 concept rows,
  163 packs, 1061 expected checks, 389 checked rows, 546 replay-only rows, 126
  Lean-horizon rows, and 163 promoted solver-reuse packs.

- **Finite Naive Bayes classifier resource landed.**
  `finite-naive-bayes-classifier-v0` now gives the statistics and probability
  lanes a compact exact classifier example: it replays a six-row binary-feature
  training table, class priors, Laplace-smoothed likelihoods, class scores,
  posterior probabilities, and the positive decision; rejects the malformed
  positive-posterior claim `2/3` versus exact `9/13`; and routes that scalar
  conflict through a source-linked QF_LRA/Farkas row. The focused learner page,
  probability/statistics query guide, probability-mass-table,
  exact-vs-floating, finite Naive Bayes, and QF_LRA/Farkas bridge rows,
  validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed finite replay separate
  from conditional-independence validity, Bayes optimality, calibration,
  statistical consistency, model selection, multiclass generality, and
  floating-point classifier behavior. At that landing, the public summary reported 126
  concept rows, 162 packs, 1054 expected checks, 388 checked rows, 541
  replay-only rows, 125 Lean-horizon rows, and 162 promoted solver-reuse packs.

- **Finite k-means clustering resource landed.**
  `finite-k-means-clustering-v0` now gives the statistics, linear-algebra,
  optimization/convexity, numerical-analysis, rational, and real-analysis
  lanes a compact exact clustering example: it replays a four-point rational
  sample, fixed two-cluster assignment, exact centroids, residuals, squared
  distances, WCSS, global centroid, total scatter, and between-cluster scatter;
  rejects the malformed centroid-coordinate claim `-1/2` versus exact `-1`;
  and routes that scalar conflict through a source-linked QF_LRA/Farkas row.
  The focused learner page, statistics/matrix/optimization/numerical query
  guides, finite k-means, residual-bound, inner-product/projection,
  exact-vs-floating, and QF_LRA/Farkas bridge rows, validator, resource smoke
  queries, generated dashboards, and `math_resource_lra_routes` regression
  keep this fixed finite replay separate from Lloyd convergence, global
  optimality, clustering consistency, randomized initialization, floating-point
  k-means implementations, and statistical generalization. The public summary
  at landing reported 125 concept rows, 161 packs, 1047 expected checks, 387
  checked rows, 536 replay-only rows, 124 Lean-horizon rows, and 161 promoted
  solver-reuse packs.
- **Finite principal-components resource landed.**
  `finite-principal-components-v0` now gives the statistics, linear-algebra,
  optimization/convexity, numerical-analysis, rational, and real-analysis
  lanes a compact exact PCA example: it replays a four-row rational sample,
  mean-zero centering, centered Gram and covariance matrices, principal and
  secondary eigenpairs, projected scores, one-component reconstruction,
  residual energy, and explained-variance ratio `4/5`; rejects the malformed
  principal-eigenvalue claim `3/2` versus exact `2`; and routes that scalar
  conflict through a source-linked QF_LRA/Farkas row. The focused learner page,
  statistics/matrix/optimization/analysis query guides, finite-PCA,
  random-matrix/covariance, eigenpair, inner-product/projection,
  exact-vs-floating, and QF_LRA/Farkas bridge rows, validator, resource smoke
  queries, generated dashboards, and `math_resource_lra_routes` regression
  keep this fixed finite replay separate from PCA/SVD optimality, best-rank
  approximation, estimator consistency, randomized algorithms, perturbation
  theory, floating-point PCA implementations, and statistical generalization.
  The public summary at landing reported 124 concept rows, 160 packs, 1040
  expected checks, 386 checked rows, 531 replay-only rows, 123 Lean-horizon
  rows, and 160 promoted solver-reuse packs.
- **Finite linear discriminant resource landed.**
  `finite-linear-discriminant-v0` now gives the statistics, linear-algebra,
  optimization/convexity, numerical-analysis, rational, and real-analysis
  lanes a compact exact classification example: it replays two finite rational
  classes, class means, centered rows, within-class scatter, the Fisher
  direction `w = [0, 3/2]`, projected scores, midpoint threshold `9/4`,
  finite training margins, and the finite Fisher ratio; rejects the malformed
  direction claim `wy = 1` versus exact `3/2`; and routes that two-equation
  linear conflict through a source-linked QF_LRA/Farkas row. The focused
  learner page, statistics/matrix/optimization/analysis query guides,
  finite-linear-discriminant, inner-product/projection, exact-vs-floating,
  convexity, and QF_LRA/Farkas bridge rows, validator, resource smoke queries,
  generated dashboards, and `math_resource_lra_routes` regression keep this
  fixed finite training-set replay separate from Fisher LDA optimality,
  Gaussian classifier assumptions, Bayes risk, multiclass or regularized LDA,
  statistical generalization, floating-point classifiers, and numerical
  stability. The public summary at landing reported 123 concept rows, 159
  packs, 1033 expected checks, 385 checked rows, 526 replay-only rows, 122
  Lean-horizon rows, and 159 promoted solver-reuse packs.
- **Finite ridge regression resource landed.**
  `finite-ridge-regression-v0` now gives the statistics, linear-algebra,
  optimization/convexity, numerical-analysis, rational, and real-analysis
  lanes a compact exact regularized-regression example: it replays the fixed
  design matrix `[[1,0],[1,1],[1,2]]`, response `[1,2,4]`, `lambda = 1`,
  regularized normal matrix `X^T X + I`, ridge coefficients
  `[4/5, 19/15]`, fitted values, residuals, RSS, coefficient penalty,
  regularized objective, coefficient shrinkage, and objective comparison
  against ordinary least squares; rejects the malformed regularized
  coefficient claim `beta0 = 1` versus exact `4/5`; and routes that linear
  conflict through a source-linked QF_LRA/Farkas row. The focused learner
  page, statistics/matrix/optimization/analysis query guides, residual-bound,
  inner-product/projection, exact-vs-floating, and convexity bridge rows,
  validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed exact ridge replay
  separate from general ridge optimality, regularization paths, model
  selection, cross-validation, statistical guarantees, rank-deficient
  generality, floating-point linear algebra, and numerical stability. The
  public summary at landing reported 122 concept rows, 158 packs, 1026 expected
  checks, 384 checked rows, 521 replay-only rows, 121 Lean-horizon rows, and
  158 promoted solver-reuse packs.
- **Finite Steffensen method resource landed.**
  `finite-steffensen-method-v0` now gives the real-analysis,
  sequences-and-limits, rational, and numerical-analysis lanes a compact exact
  fixed-point acceleration example: it replays Steffensen acceleration for
  `g(x) = (x + 1)/2` from `x0 = 0` to exact accelerated value `1`, replays a
  second affine row `g(x) = 1 + (x - 1)/3` from `x0 = 4` to exact accelerated
  value `1`, and checks the fixed half-step residual improvement `0 < 1/8`;
  rejects the malformed accelerated-value claim `3/2` versus exact `1`; and
  routes that scalar conflict through a source-linked QF_LRA/Farkas row. The
  focused learner page, analysis/numerical query guide, exact-vs-floating and
  sequence-tail-shadow bridge rows, validator, resource smoke queries,
  generated dashboards, and `math_resource_lra_routes` regression keep this
  fixed exact Steffensen replay separate from fixed-point existence, general
  convergence acceleration, denominator-safety, nonlinear-map theory,
  floating-point implementation correctness, and numerical stability. The
  public summary at landing reported 122 concept rows, 158 packs, 1026 expected checks,
  384 checked rows, 521 replay-only rows, 121 Lean-horizon rows, and 158
  promoted solver-reuse packs.
- **Finite Aitken acceleration resource landed.**
  `finite-aitken-acceleration-v0` now gives the real-analysis,
  sequences-and-limits, rational, and numerical-analysis lanes a compact exact
  sequence-acceleration example: it replays Aitken's delta-squared value
  `1` from `[2, 3/2, 5/4]`, the harmonic-row accelerated value `5/4` from
  `[2, 3/2, 4/3]`, and the fixed residual improvement `1/4 < 1/3`; rejects
  the malformed accelerated-value claim `3/2` versus exact `1`; and routes
  that scalar conflict through a source-linked QF_LRA/Farkas row. The focused
  learner page, analysis/numerical query guide, exact-vs-floating and
  sequence-tail-shadow bridge rows, validator, resource smoke queries,
  generated dashboards, and `math_resource_lra_routes` regression keep this
  fixed exact Aitken replay separate from general convergence acceleration,
  denominator-safety, fixed-point theory, floating-point implementation
  correctness, and numerical stability. The current public summary is
  recorded in the latest process-lane bullet above.
- **Finite secant method resource landed.**
  `finite-secant-method-v0` now gives the real-analysis, calculus, polynomial,
  rational, and numerical-analysis lanes a compact exact secant-method example:
  it replays the `x^2 - 2` secant step from `1,2` to `4/3`, the follow-up step
  from `4/3,3/2` to `24/17`, and the fixed residual decrease
  `2/289 < 1/4`; rejects the malformed first next-value claim `3/2` versus
  exact `4/3`; and routes that scalar conflict through a source-linked
  QF_LRA/Farkas row. The focused learner page, analysis/numerical query guide,
  exact-vs-floating and bounded-theorem-shadow bridge rows, validator, resource
  smoke queries, generated dashboards, and `math_resource_lra_routes`
  regression keep this fixed exact secant replay separate from general
  convergence order, denominator-safety, bracketing/globalization,
  floating-point implementation correctness, and numerical stability. The
  current public summary is recorded in the latest process-lane bullet above.
- **Finite Romberg extrapolation resource landed.**
  `finite-romberg-extrapolation-v0` now gives the real-analysis, calculus,
  polynomial, and numerical-analysis lanes a compact exact
  Romberg/Richardson extrapolation example: it replays one-panel and two-panel
  composite trapezoid values for `x^2` and `x^4` on `[0,1]`, computes
  `(4*T(h/2)-T(h))/3`, records exact quadratic error cancellation and a
  quartic residual, and rejects the malformed extrapolated-value claim `1/4`
  versus exact `1/3` through a source-linked QF_LRA/Farkas row. The focused
  learner page, rational-real algebra page, calculus theorem-boundary page,
  analysis/numerical query guide, integration and exact-vs-floating bridge
  rows, validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed exact extrapolation
  replay separate from general Richardson/Romberg convergence, asymptotic
  error expansions, adaptive quadrature, floating-point quadrature
  correctness, and numerical stability. The current public summary is
  recorded in the latest process-lane bullet above.
- **Finite cubic spline interpolation resource landed.**
  `finite-cubic-spline-interpolation-v0` now gives the real-analysis,
  calculus, and numerical-analysis lanes a compact natural cubic spline
  assembly example: it replays two cubic pieces through knots `0, 1, 2`,
  sample values `0, 1, 0`, natural endpoint second derivatives, C1/C2
  continuity at the interior knot, and exact midpoint values `11/16` on both
  subintervals. It rejects the malformed spline value `3/4` versus exact
  `11/16` through a source-linked QF_LRA/Farkas row. The focused learner page,
  rational-real algebra page, calculus theorem-boundary page,
  analysis/numerical query guide, derivative and polynomial bridge rows,
  validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed exact spline replay
  separate from general spline existence/uniqueness, convergence, error,
  shape-preservation, knot-selection, and floating-point spline-evaluation
  theory. The current public summary is recorded in the latest process-lane
  bullet above.
- **Finite cubic Hermite interpolation resource landed.**
  `finite-cubic-hermite-interpolation-v0` now gives the real-analysis,
  calculus, and numerical-analysis lanes a compact endpoint value/slope
  interpolation example: it replays Hermite basis values, interval-length
  scaling, endpoint value constraints, endpoint slope constraints, and exact
  polynomial values for a smoothstep row, a unit-interval quadratic row, and a
  nonunit interval quadratic row. It rejects the malformed Hermite claim `2`
  versus exact `7/4` through a source-linked QF_LRA/Farkas row. The focused
  learner page, rational-real algebra page, calculus theorem-boundary page,
  analysis/numerical query guide, derivative and polynomial bridge rows,
  validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed exact Hermite replay
  separate from Hermite interpolation uniqueness, divided-difference
  equivalence, error formulas, spline assembly, monotonicity,
  shape-preservation, and floating-point Hermite-evaluation theory. The current
  public summary is recorded in the latest process-lane bullet above.
- **Finite Taylor polynomial resource landed.**
  `finite-taylor-polynomials-v0` now gives the real-analysis, calculus, and
  numerical-analysis lanes a compact exact Taylor-polynomial example: it
  replays symbolic derivative values, factorials, Taylor coefficients, basis
  powers, exact polynomial values for quadratic and cubic rows, and one
  degree-1 truncation with exact remainder `1/4`. It rejects the malformed
  exact Taylor claim `6` versus exact `25/4` through a source-linked
  QF_LRA/Farkas row. The focused learner page, rational-real algebra page,
  calculus theorem-boundary page, analysis/numerical query guide, derivative
  and polynomial bridge rows, validator, resource smoke queries, generated
  dashboards, and `math_resource_lra_routes` regression keep this fixed exact
  Taylor replay separate from Taylor theorem, remainder-bound, analytic
  convergence, radius-of-convergence, smoothness, multivariable Taylor, and
  floating-point Taylor-evaluation theory. The current public summary is
  recorded in the latest process-lane bullet above.
- **Finite difference derivative resource landed.**
  `finite-difference-derivatives-v0` now gives the real-analysis and
  numerical-analysis lanes a compact exact finite-difference derivative
  example: it checks a forward first-difference row for `1+3*x`, a central
  first-difference row for `1+2*x+x^2`, and a central second-difference row
  for the same quadratic. It rejects the malformed finite-difference claim `5`
  versus exact `4` through a source-linked QF_LRA/Farkas row. The focused
  learner page, rational-real algebra page, calculus theorem-boundary page,
  analysis/numerical query guide, derivative and polynomial bridge rows,
  validator, resource smoke queries, generated dashboards, and
  `math_resource_lra_routes` regression keep this fixed exact stencil replay
  separate from Taylor-error, convergence-order, stability,
  boundary-condition, PDE-discretization, automatic-differentiation, and
  floating-point finite-difference theory. The current public summary is
  recorded in the latest process-lane bullet above.
- **Finite barycentric interpolation resource landed.**
  `finite-barycentric-interpolation-v0` now gives the real-analysis and
  numerical-analysis lanes a compact exact barycentric interpolation example:
  it checks barycentric weights, regular numerator/denominator terms,
  interpolation values for `1+2*x` and `x^2`, and an explicit node-hit row. It
  then rejects the malformed barycentric claim `5` versus exact `4` through a
  source-linked QF_LRA/Farkas row. The focused learner page, rational-real
  algebra page, calculus theorem-boundary page, analysis/numerical query guide,
  polynomial replay bridge, validator, resource smoke queries, and
  `math_resource_lra_routes` regression keep this fixed exact interpolation
  replay separate from barycentric/Lagrange/Newton equivalence, interpolation
  uniqueness, error estimates, node-choice conditioning, Runge phenomena,
  spline theory, floating-point interpolation correctness, and numerical
  stability. The public summary now reports 122 concept rows, 149 packs, 972
  expected checks, 375 checked rows, 485 replay-only rows, 112 Lean-horizon
  rows, and 149 promoted solver-reuse packs.
- **Finite divided-differences resource landed.**
  `finite-divided-differences-v0` now gives the real-analysis and
  numerical-analysis lanes a compact exact Newton interpolation example: it
  checks divided-difference tables, Newton coefficients, basis products, terms,
  and interpolation values for `1+x^2` at nodes `0,1,2` and `x^3` at nodes
  `0,1,2,3`. It then rejects the malformed interpolation claim `9` versus
  exact `10` through a source-linked QF_LRA/Farkas row. The focused learner
  page, rational-real algebra page, calculus theorem-boundary page,
  analysis/numerical query guide, polynomial replay bridge, validator, resource
  smoke queries, and `math_resource_lra_routes` regression keep this fixed
  exact interpolation replay separate from general interpolation uniqueness,
  divided-difference identities, error estimates, node-choice conditioning,
  spline theory, floating-point interpolation correctness, and numerical
  stability. At landing, the public summary reported 122 concept rows, 148 packs, 966
  expected checks, 374 checked rows, 481 replay-only rows, 111 Lean-horizon
  rows, and 148 promoted solver-reuse packs.
- **Finite Simpson-rule resource landed.**
  `finite-simpson-rule-v0` now gives the real-analysis and numerical-analysis
  lanes a compact exact quadrature example: it checks single-panel
  Simpson-rule nodes `[0, 1, 2]`, weights `[1, 4, 1]`, sample values,
  weighted sums, Simpson values `4` and `14/3`, and exact polynomial
  integrals for `x^3` and `1+x^2` on `[0,2]`. It then rejects the malformed
  cubic quadrature claim `7/2` versus exact `4` through a source-linked
  QF_LRA/Farkas row. The focused learner page, calculus theorem-boundary page,
  analysis/numerical query guide, integration-horizon bridge, validator,
  resource smoke queries, and `math_resource_lra_routes` regression keep this
  fixed exact Simpson replay separate from general Simpson-rule exactness,
  composite/adaptive quadrature convergence, error bounds, floating-point
  quadrature correctness, and numerical stability. At landing, the public
  summary reported 122 concept rows, 147 packs, 960 expected checks, 373
  checked rows, 477 replay-only rows, 110 Lean-horizon rows, and 147 promoted
  solver-reuse packs.
- **Finite BDF2 method resource landed.**
  `finite-bdf2-method-v0` now gives the differential-equations,
  numerical-analysis, and real-analysis lanes a compact exact implicit
  two-step multistep example: it checks `y' = -y`, `y(0)=1`, step size
  `h=1/2`, times `[0, 1/2, 1, 3/2]`, backward-Euler starter `y_1=2/3`,
  states `[1, 2/3, 5/12, 1/4]`, derivatives
  `[-1, -2/3, -5/12, -1/4]`, endpoint derivatives `[-5/12, -1/4]`, zero
  implicit residuals, and strict finite monotone decay. It then rejects the
  malformed first multistep claim `1/3` versus exact `5/12` through a
  source-linked QF_LRA/Farkas row. The focused learner page, dynamics and
  analysis/numerical query guides, finite dynamics/time-stepping bridge,
  validator, resource smoke queries, and `math_resource_lra_routes` regression
  keep this fixed exact implicit multistep replay separate from general BDF2
  order, convergence, zero-stability, nonlinear endpoint-solve correctness,
  variable-step correctness, floating-point time-stepping, and PDE theory.
  After that increment, the public summary reported 122 concept rows, 146
  packs, 955 expected checks, 372 checked rows, 474 replay-only rows, 109
  Lean-horizon rows, and 146 promoted solver-reuse packs.
- **Finite Adams-Bashforth method resource landed.**
  `finite-adams-bashforth-method-v0` now gives the differential-equations,
  numerical-analysis, and real-analysis lanes a compact exact explicit
  two-step multistep example: it checks `y' = 2t`, `y(0)=0`, step size
  `h=1/2`, times `[0, 1/2, 1, 3/2]`, exact starter `y_1=1/4`, states
  `[0, 1/4, 1, 9/4]`, derivatives `[0, 1, 2]`, Adams-Bashforth slopes
  `[3/2, 5/2]`, and zero error against `y=t^2`. It then rejects the malformed
  first multistep claim `3/4` versus exact `1` through a source-linked
  QF_LRA/Farkas row. The focused learner page, dynamics and analysis/numerical
  query guides, finite dynamics/time-stepping bridge, validator, resource
  smoke queries, and `math_resource_lra_routes` regression keep this fixed
  exact multistep replay separate from general Adams-Bashforth order,
  convergence, stability regions, variable-step correctness, floating-point
  time-stepping, and PDE theory. After that increment, the public summary
  reported 122 concept rows, 145 packs, 950 expected checks, 371 checked rows,
  471 replay-only rows, 108 Lean-horizon rows, and 145 promoted solver-reuse
  packs.
- **Finite Crank-Nicolson method resource landed.**
  `finite-crank-nicolson-method-v0` now gives the differential-equations,
  numerical-analysis, and real-analysis lanes a compact exact implicit
  trapezoid time-stepping example: it checks `y' = -y`, `y(0)=1`, step size
  `h=1/2`, times `[0, 1/2, 1, 3/2]`, states
  `[1, 3/5, 9/25, 27/125]`, start derivatives `[-1, -3/5, -9/25]`,
  endpoint derivatives `[-3/5, -9/25, -27/125]`, averaged derivatives
  `[-4/5, -12/25, -36/125]`, zero implicit residuals, decay ratio `3/5`,
  and bounds `0 <= state <= 1`. It then rejects the malformed first-step
  claim `1/2` versus exact `3/5` through a source-linked QF_LRA/Farkas row.
  The focused learner page, dynamics and analysis/numerical query guides,
  finite dynamics/time-stepping bridge, validator, resource smoke queries, and
  `math_resource_lra_routes` regression keep this fixed exact implicit
  trapezoid replay separate from general Crank-Nicolson order, convergence,
  A-stability, stiffness behavior, nonlinear solve correctness,
  adaptive-step control, floating-point time-stepping, and PDE theory. After
  that increment, the public summary reported 122 concept rows, 144 packs, 945
  expected checks, 370 checked rows, 468 replay-only rows, 107 Lean-horizon
  rows, and 144 promoted solver-reuse packs.
- **Finite Backward Euler method resource landed.**
  `finite-backward-euler-method-v0` now gives the differential-equations,
  numerical-analysis, and real-analysis lanes a compact exact implicit
  time-stepping example: it checks `y' = -y`, `y(0)=1`, step size `h=1/2`,
  times `[0, 1/2, 1, 3/2]`, states `[1, 2/3, 4/9, 8/27]`, endpoint
  derivatives `[-2/3, -4/9, -8/27]`, zero implicit residuals, decay ratio
  `2/3`, and bounds `0 <= state <= 1`. It then rejects the malformed
  first-step claim `1/2` versus exact `2/3` through a source-linked
  QF_LRA/Farkas row. The focused learner page, dynamics and
  analysis/numerical query guides, finite dynamics/time-stepping bridge,
  validator, resource smoke queries, and `math_resource_lra_routes`
  regression keep this fixed exact implicit-step replay separate from general
  backward Euler convergence, A-stability, stiffness behavior, nonlinear
  solve correctness, adaptive-step control, floating-point time-stepping, and
  PDE theory. After that increment the public summary reported 122 concept rows, 143 packs,
  940 expected checks, 369 checked rows, 465 replay-only rows,
  106 Lean-horizon rows, and 143 promoted solver-reuse packs.
- **Finite Heun method resource landed.**
  `finite-heun-method-v0` now gives the differential-equations,
  numerical-analysis, and real-analysis lanes a compact exact explicit
  trapezoidal RK2 example: it checks `y' = 2t`, `y(0)=0`, step size `h=1/2`,
  times `[0, 1/2, 1, 3/2]`, states `[0, 1/4, 1, 9/4]`, stage derivatives
  `[0, 1, 2]`, predictor states `[0, 3/4, 2]`, endpoint derivatives
  `[1, 2, 3]`, averaged derivatives `[1/2, 3/2, 5/2]`, exact solution
  `[0, 1/4, 1, 9/4]`, and zero absolute error. It then rejects the malformed
  first-step claim `1/2` versus exact `1/4` through a source-linked
  QF_LRA/Farkas row. The focused learner page, dynamics and analysis/numerical
  query guides, finite dynamics/time-stepping bridge, validator, resource smoke
  queries, and `math_resource_lra_routes` regression keep this fixed exact
  time-stepping replay separate from general Runge-Kutta order theory,
  consistency, convergence, stability-region, stiffness, and adaptive-step
  theorems. After that increment the public summary reported 122 concept rows, 142 packs,
  935 expected checks, 368 checked rows, 462 replay-only rows,
  105 Lean-horizon rows, and 142 promoted solver-reuse packs.
- **Finite Runge-Kutta midpoint resource landed.**
  `finite-runge-kutta-midpoint-v0` now gives the differential-equations,
  numerical-analysis, and real-analysis lanes a compact exact RK2 midpoint
  example: it checks `y' = 2t`, `y(0)=0`, step size `h=1/2`, times
  `[0, 1/2, 1, 3/2]`, states `[0, 1/4, 1, 9/4]`, stage derivatives
  `[0, 1, 2]`, midpoint times `[1/4, 3/4, 5/4]`, midpoint states
  `[0, 1/2, 3/2]`, midpoint derivatives `[1/2, 3/2, 5/2]`, exact solution
  `[0, 1/4, 1, 9/4]`, and zero absolute error. It then rejects the malformed
  first-step claim `1/2` versus exact `1/4` through a source-linked
  QF_LRA/Farkas row. The focused learner page, dynamics and analysis/numerical
  query guides, finite dynamics/time-stepping bridge, validator, resource smoke
  queries, and `math_resource_lra_routes` regression keep this fixed exact
  time-stepping replay separate from general Runge-Kutta order theory,
  consistency, convergence, stability-region, stiffness, and adaptive-step
  theorems. After that increment the public summary reported 122 concept rows,
  141 packs, 929 expected checks, 367 checked rows, 458 replay-only rows,
  104 Lean-horizon rows, and 141 promoted solver-reuse packs.
- **Finite GMRES residual-shadow resource landed.**
  `finite-gmres-residual-shadow-v0` now gives the linear-algebra,
  numerical-analysis, functional-operator, and optimization lanes a compact
  exact one-step Krylov residual-minimization example: it checks
  `A=[[2,1],[1,2]]`, `b=[1,0]`, `x0=[0,0]`, the initial residual
  `r0=[1,0]`, Krylov direction `A*r0=[2,1]`, exact GMRES coefficient
  `alpha=2/5`, approximate solution `[2/5,0]`, residual `[1/5,-2/5]`,
  residual orthogonality to `A*r0`, and residual-norm decrease from `1` to
  `1/5`. It then rejects the malformed claim `alpha=1/2` through a
  source-linked QF_LRA/Farkas row. The focused learner page, matrix,
  numerical-analysis, and functional-operator query guides, residual-bound,
  finite-operator/Krylov, and inner-product/projection bridges, validator,
  resource smoke queries, and `math_resource_lra_routes` regression keep this
  finite exact replay separate from general GMRES convergence, restart,
  preconditioner, breakdown, nonnormal, and floating-point stability schemas.
  After that increment the public summary reported 122 concept rows, 140 packs,
  923 expected checks, 366 checked rows, 454 replay-only rows,
  103 Lean-horizon rows, and 140 promoted solver-reuse packs.
- **Finite Cauchy-Riemann shadow resource landed.**
  `finite-cauchy-riemann-shadow-v0` now gives the complex-analysis and
  real-analysis lanes a compact exact polynomial partial-derivative example:
  it checks `f(z)=z^2` at `z=1+2i`, the real-pair value `-3+4i`, component
  polynomials `u=x^2-y^2` and `v=2xy`, partials `u_x=2`, `u_y=-4`, `v_x=4`,
  `v_y=2`, the fixed equalities `u_x=v_y` and `u_y=-v_x`, and the derivative
  `f'(1+2i)=2+4i`. It then rejects the malformed claim
  `real(f'(1+2i)) = 3` through a source-linked QF_LRA/Farkas row. The focused
  learner page, complex-analysis theorem boundary, analysis/numerical query
  guide, complex real-pair and derivative-shadow bridges, validator, resource
  smoke queries, and `math_resource_lra_routes` regression keep this finite
  replay separate from general holomorphicity and Cauchy-Riemann theorem
  schemas. After that increment the public summary reported 122 concept rows, 139 packs, 915
  expected checks, 365 checked rows, 448 replay-only rows, 102 Lean-horizon
  rows, and 139 promoted solver-reuse packs.
- **Finite interval-arithmetic shadow resource landed.**
  `finite-interval-arithmetic-shadow-v0` now gives the real-analysis and
  numerical-analysis lanes a compact exact rational interval-arithmetic example:
  it checks `X = Y = [1, 10001/10000]`, endpoint-wise interval sum/product,
  interval widths, and the second-order product-width excess
  `width(X) * width(Y) = 1/100000000`. It then rejects the malformed upper-bound
  shortcut `product_upper <= 5001/5000` against exact
  `product_upper = 100020001/100000000` through a source-linked QF_LRA/Farkas
  row. The focused learner page, rational/real and analysis/numerical query
  guides, rational-interval and exact-vs-floating bridges, validator, and
  `math_resource_lra_routes` regression keep exact rational interval replay
  separate from general interval-analysis soundness, dependency handling,
  outward-rounded floating-point endpoints, QF_FP semantics, and numerical
  stability theorems. The public summary after that increment reported 122
  concept rows, 138 packs, 908 expected checks, 364 checked rows, 443
  replay-only rows, 101 Lean-horizon rows, and 138 promoted solver-reuse packs.
- **Finite rounding-shadow resource landed.**
  `finite-rounding-shadow-v0` now gives the real-analysis and
  numerical-analysis lanes a compact exact-vs-rounded arithmetic example: it
  checks `x = 1`, `y = 1/10000`, `exact_delta = (x + y) - x = 1/10000`, and
  a fixed three-decimal rounding-grid transcript where
  `round3(x + y) - round3(x) = 0`. It then isolates the malformed equality
  claim `exact_delta = rounded_delta` as a source-linked QF_LRA/Farkas row.
  The focused learner page, rational/real and analysis/numerical query guides,
  exact-vs-floating bridge, validator, and `math_resource_lra_routes`
  regression keep fixed rational rounding replay separate from IEEE
  floating-point semantics, rounding-mode theory, accumulation-error bounds,
  and numerical-stability theorems. The public summary now reports 122 concept
  rows, 137 packs, 901 expected checks, 363 checked rows, 438 replay-only rows,
  100 Lean-horizon rows, and 137 promoted solver-reuse packs.
- **Finite shifted QR step resource landed.**
  `finite-shifted-qr-step-v0` now gives the linear-algebra,
  numerical-analysis, and functional-analysis/operator lanes an exact rational
  shifted QR-step shadow: it checks `mu = 1`,
  `A0 - mu*I = Q*R`, `A1 = R*Q + mu*I`, and `A1 = Q^T*A0*Q`
  for `Q = [[3/5,4/5],[-4/5,3/5]]`, `R = [[5,2],[0,1]]`,
  `A0 = [[4,2],[-4,0]]`, and
  `A1 = [[12/5,26/5],[-4/5,8/5]]`, then replays trace and determinant
  preservation and isolates the malformed next-step entry claim
  `A1[1,1] = 2` versus exact `8/5` as a source-linked QF_LRA/Farkas row.
  The focused learner page, matrix/numerical and functional/operator query
  guides, eigenpair and exact-vs-floating bridges, validator, and
  `math_resource_lra_routes` regression keep fixed finite shifted-QR replay
  separate from shift-selection theory, deflation, QR convergence, Schur
  theorem reconstruction, loss-of-orthogonality analysis, and floating-point
  eigensolver stability. The public summary now reports 122 concept rows,
  137 packs, 901 expected checks, 363 checked rows, 438 replay-only rows,
  100 Lean-horizon rows, and 137 promoted solver-reuse packs.
- **Finite QR iteration step resource landed.**
  `finite-qr-iteration-step-v0` now gives the linear-algebra,
  numerical-analysis, and functional-analysis/operator lanes an exact rational
  unshifted QR-step shadow: it checks
  `Q = [[3/5,4/5],[-4/5,3/5]]`, `R = [[5,2],[0,1]]`,
  `A0 = Q*R = [[3,2],[-4,-1]]`,
  `A1 = R*Q = Q^T*A0*Q = [[7/5,26/5],[-4/5,3/5]]`,
  trace preservation, and determinant preservation, then isolates the
  malformed next-step entry claim `A1[0,0] = 2` versus exact `7/5` as a
  source-linked QF_LRA/Farkas row. The focused learner page, matrix/numerical
  and functional/operator query guides, eigenpair and exact-vs-floating bridges,
  validator, and `math_resource_lra_routes` regression keep fixed finite
  QR-step replay separate from QR-iteration convergence, shifted/deflated
  variants, Schur theorem reconstruction, loss-of-orthogonality analysis, and
  floating-point eigensolver stability. The public summary now reports
  122 concept rows, 137 packs, 901 expected checks, 363 checked rows,
  438 replay-only rows, 100 Lean-horizon rows, and 137 promoted solver-reuse
  packs.
- **Finite polar decomposition resource landed.**
  `finite-polar-decomposition-v0` now gives the linear-algebra,
  numerical-analysis, and functional-analysis/operator lanes an exact rational
  polar shadow: it checks
  `U = [[3/5,4/5],[-4/5,3/5]]`, `P = [[2,0],[0,5]]`,
  `A = U*P = [[6/5,4],[-8/5,3]]`, `U^T*U = I`, `U*P = A`,
  `A^T*A = P^2`, trace/diagonal-sum replay, and determinant/product replay,
  then isolates the malformed diagonal claim `P[1,1] = 4` versus exact `5`
  as a source-linked QF_LRA/Farkas row. The focused learner page,
  matrix/numerical query guides, eigenpair and exact-vs-floating bridges,
  validator, and `math_resource_lra_routes` regression keep fixed finite
  polar replay separate from the polar theorem, partial-isometry variants,
  square-root functional calculus, iterative algorithms, perturbation bounds,
  and floating-point stability. The public summary now reports 122 concept rows,
  137 packs, 901 expected checks, 363 checked rows, 438 replay-only rows,
  100 Lean-horizon rows, and 137 promoted solver-reuse packs.
- **Finite real Schur decomposition resource landed.**
  `finite-real-schur-decomposition-v0` now gives the linear-algebra,
  numerical-analysis, and functional-analysis/operator lanes an exact rational
  real-Schur shadow: it checks
  `Q = [[3/5,4/5],[-4/5,3/5]]`, `T = [[1,2],[0,4]]`,
  `A = Q*T*Q^T = [[97/25,54/25],[4/25,28/25]]`, `Q^T*Q = I`,
  `A*Q = Q*T`, trace/diagonal-sum replay, and determinant/diagonal-product
  replay, then isolates the malformed superdiagonal claim `T[0,1] = 3`
  versus exact `2` as a source-linked QF_LRA/Farkas row. The focused learner
  page, matrix/numerical query guides, eigenpair and exact-vs-floating bridges,
  validator, and `math_resource_lra_routes` regression keep fixed finite
  real-Schur replay separate from the general real/complex Schur theorem,
  eigenvalue ordering, QR-iteration convergence, perturbation bounds, and
  floating-point stability. The public summary now reports 122 concept rows,
  137 packs, 901 expected checks, 363 checked rows, 438 replay-only rows,
  100 Lean-horizon rows, and 137 promoted solver-reuse packs.
- **Finite orthogonal diagonalization resource landed.**
  `finite-orthogonal-diagonalization-v0` now gives the linear-algebra,
  numerical-analysis, and functional-analysis/operator lanes an exact rational
  spectral-theorem shadow: it checks a rational orthogonal matrix
  `Q = [[3/5,4/5],[-4/5,3/5]]`, `D = diag(1,4)`,
  `A = Q*D*Q^T = [[73/25,36/25],[36/25,52/25]]`,
  `Q^T*Q = I`, both column eigenpairs, `trace(A) = 5`, and
  `det(A) = 4`, then isolates the malformed eigenvalue claim
  `lambda_1 = 5` versus exact `4` as a source-linked QF_LRA/Farkas row. The
  focused learner page, matrix/numerical query guides, eigenpair and
  exact-vs-floating bridges, validator, and `math_resource_lra_routes`
  regression keep fixed finite spectral replay separate from the spectral
  theorem, diagonalization criteria, multiplicity theory, perturbation bounds,
  eigensolver convergence, and floating-point stability. The public summary
  now reports 122 concept rows, 137 packs, 901 expected checks, 363 checked
  rows, 438 replay-only rows, 100 Lean-horizon rows, and 137 promoted
  solver-reuse packs.
- **Finite LDLT decomposition resource landed.**
  `finite-ldlt-decomposition-v0` now gives the linear-algebra,
  numerical-analysis, and optimization lanes an exact rational
  positive-definite factorization transcript: it checks
  `A = [[4,2],[2,3]]`, `L = [[1,0],[1/2,1]]`,
  `D = [[4,0],[0,2]]`, `L*D*L^T = A`, determinant/product replay
  `det(A) = product(diag(D)) = 8`, positive leading minors `[4,8]`,
  triangular solve replay for `b = [6,5]`, and solution `[1,1]`, then
  isolates the malformed diagonal-entry claim `D[1,1] = 3` versus exact `2`
  as a source-linked QF_LRA/Farkas row. The focused learner page,
  matrix/numerical query guides, concept bridges, validator, and
  `math_resource_lra_routes` regression keep fixed finite LDLT replay separate
  from LDLT existence, pivoting strategy correctness, indefinite variants,
  sparse algorithms, conditioning, and floating-point stability. The public
  summary now reports 122 concept rows, 131 packs, 858 expected checks, 357
  checked rows, 407 replay-only rows, 94 Lean-horizon rows, and 131 promoted
  solver-reuse packs.
- **Finite pivoted-LU decomposition resource landed.**
  `finite-pivoted-lu-decomposition-v0` now gives the linear-algebra,
  numerical-analysis, and optimization lanes an exact row-swapped rational
  factorization transcript: it checks `A = [[1,2],[3,4]]`,
  `P = [[0,1],[1,0]]`, `P*A = [[3,4],[1,2]]`,
  `L = [[1,0],[1/3,1]]`, `U = [[3,4],[0,2/3]]`,
  determinant-sign accounting `det(P) * det(A) = product(pivots) = 2`,
  triangular solve replay for `b = [3,7]`, and solution `[1,1]`, then
  isolates the malformed pivot-sign claim `det(P) = +1` versus exact `-1` as
  a source-linked QF_LRA/Farkas row. The focused learner page,
  matrix/numerical query guides, concept bridges, validator, and
  `math_resource_lra_routes` regression keep fixed finite pivoted-LU replay
  separate from pivot-selection correctness, rank-deficient behavior, sparse
  pivoting, growth-factor bounds, conditioning, and floating-point stability.
  The public summary now reports 122 concept rows, 131 packs, 858 expected
  checks, 357 checked rows, 407 replay-only rows, 94 Lean-horizon rows, and
  131 promoted solver-reuse packs.
- **Finite LU-decomposition resource landed.**
  `finite-lu-decomposition-v0` now gives the linear-algebra and
  numerical-analysis lanes an exact rational factorization transcript: it
  checks `A = [[2,1],[4,5]]`, `L = [[1,0],[2,1]]`,
  `U = [[2,1],[0,3]]`, `L*U = A`, determinant pivot product `6`,
  forward/back substitution for `b = [5,17]`, and solution `[4/3,7/3]`,
  then isolates the malformed multiplier claim `l21 = 3` versus exact `2` as
  a source-linked QF_LRA/Farkas row. The focused learner page, matrix/numerical
  query guides, concept bridges, validator, and `math_resource_lra_routes`
  regression keep fixed finite LU replay separate from general LU existence,
  pivoting correctness, rank-deficient variants, sparse algorithms,
  conditioning, and floating-point stability.
- **Finite Gram-Schmidt resource landed.**
  `finite-gram-schmidt-v0` now gives the linear-algebra,
  numerical-analysis, and operator-theory lanes an exact rational
  orthogonalization transcript: it checks `a1 = [3,4]`, `a2 = [1,0]`,
  `q1 = [3/5,4/5]`, `r12 = 3/5`, residual `[16/25,-12/25]`,
  `q2 = [4/5,-3/5]`, upper-triangular `R`, orthonormality, and
  `Q*R = A`, then isolates the malformed projection coefficient claim
  `r12 = 4/5` versus exact `3/5` as a source-linked QF_LRA/Farkas row. The
  focused learner page, matrix/operator query guides, concept bridges,
  validator, and `math_resource_lra_routes` regression keep fixed finite
  Gram-Schmidt replay separate from general Gram-Schmidt/QR correctness,
  rank-deficient variants, conditioning, and floating-point stability. The
  public summary now reports 122 concept rows, 131 packs, 858 expected checks,
  357 checked rows, 407 replay-only rows, 94 Lean-horizon rows, and 131
  promoted solver-reuse packs.
- **Finite Householder-reflection resource landed.**
  `finite-householder-reflection-v0` now gives the linear-algebra,
  numerical-analysis, and operator-theory lanes an exact rational reflection
  transcript: it checks `v = [2,1]`, `v^T*v = 5`,
  `H = [[-3/5,-4/5],[-4/5,3/5]]`, `H^T = H`, `H^T*H = I`,
  `H*[3,4] = [-5,0]`, `H^2 = I`, determinant `-1`, and norm preservation,
  then isolates the malformed top-left entry claim `H[0,0] = -4/5` versus
  exact `-3/5` as a source-linked QF_LRA/Farkas row. The focused learner page,
  matrix/operator query guides, concept bridges, validator, and
  `math_resource_lra_routes` regression keep fixed finite Householder replay
  separate from general Householder/QR algorithms, pivoting, conditioning, and
  floating-point stability.
- **Finite Givens-rotation resource landed.**
  `finite-givens-rotation-v0` now gives the linear-algebra,
  numerical-analysis, and operator-theory lanes an exact rational orthogonal
  transform transcript: it checks `c = 3/5`, `s = 4/5`, the rotation
  `G = [[3/5,4/5],[-4/5,3/5]]`, `G^T*G = I`, `G*[3,4] = [5,0]`,
  inverse reconstruction with `G^T`, determinant `1`, and norm preservation,
  then isolates the malformed sine coefficient claim `s = 3/5` versus exact
  `4/5` as a source-linked QF_LRA/Farkas row. The focused learner page,
  matrix/operator query guides, concept bridges, validator, and
  `math_resource_lra_routes` regression keep fixed finite Givens replay
  separate from general QR algorithms, pivoting, conditioning, and
  floating-point stability.
- **Finite Lanczos-iteration resource landed.**
  `finite-lanczos-iteration-v0` now gives the linear-algebra,
  numerical-analysis, and operator-theory lanes an exact rational symmetric
  Krylov/tridiagonal transcript: it checks `A = [[2,1],[1,2]]`, `q1 = [1,0]`,
  `alpha1 = 2`, residual `[0,1]`, `beta1 = 1`, `q2 = [0,1]`,
  `alpha2 = 2`, exact termination residual, orthonormality, and the exact
  relation `A*Q = Q*T`, then isolates the malformed off-diagonal coefficient
  claim `beta1 = 2` versus exact `1` as a source-linked QF_LRA/Farkas row.
  The focused learner page, matrix/operator query guides, concept bridges,
  validator, and `math_resource_lra_routes` regression keep fixed finite
  Lanczos replay separate from general Lanczos convergence, Ritz-value theory,
  breakdown/restart behavior, finite-precision orthogonality, and
  floating-point stability.
- **Finite Arnoldi-iteration resource landed.**
  `finite-arnoldi-iteration-v0` now gives the linear-algebra,
  numerical-analysis, and operator-theory lanes an exact rational
  Krylov/Hessenberg transcript: it checks `A = [[1,2],[3,4]]`, `q1 = [1,0]`,
  the first projection and residual, `h21 = 3`, `q2 = [0,1]`, the second
  projection column, orthonormality, and the exact relation `A*Q = Q*H`, then
  isolates the malformed subdiagonal coefficient claim `h21 = 2` versus exact
  `3` as a source-linked QF_LRA/Farkas row. The focused learner page,
  matrix/operator query guides, concept bridges, validator, and
  `math_resource_lra_routes` regression keep fixed finite Arnoldi replay
  separate from general Arnoldi/GMRES convergence, Ritz-value theory,
  restart/reorthogonalization strategies, and floating-point stability.
- **Finite Conjugate-gradient resource landed.**
  `finite-conjugate-gradient-v0` now gives the linear-algebra,
  numerical-analysis, and optimization lanes an exact rational SPD solve
  transcript: it checks `A = [[4,1],[1,3]]`, `b = [1,2]`, residuals, two CG
  step sizes, Fletcher-Reeves `beta`, residual orthogonality, A-conjugacy, and
  the exact solution `[1/11,7/11]`, then isolates the malformed first step-size
  claim `1/3` versus exact `1/4` as a source-linked QF_LRA/Farkas row. The
  focused learner page, matrix/optimization query guides, concept bridges,
  validator, and `math_resource_lra_routes` regression keep fixed finite CG
  replay separate from general convergence, Krylov minimization,
  preconditioning, roundoff, and floating-point stability.
- **Finite Power-iteration resource landed.**
  `finite-power-iteration-v0` now gives the linear-algebra,
  numerical-analysis, and operator-theory lanes an exact rational spectral
  iteration shadow: it checks `A = diag(2,1)`, two power steps
  `[1,1] -> [2,1] -> [4,1]`, `l1` normalization `[4/5,1/5]`, Rayleigh
  quotient `9/5`, residual `[2/5,-4/5]`, and the dominant eigenpair shadow
  `2,[1,0]`, then isolates the malformed second-iterate coordinate claim
  `3` versus exact `4` as a source-linked QF_LRA/Farkas row. The focused
  learner page, matrix index, concept bridges, query guide, validator, and
  `math_resource_lra_routes` regression keep fixed finite iteration replay
  separate from convergence, spectral-gap assumptions,
  residual-to-eigenvalue error theorems, deflation, block iteration,
  conditioning, and floating-point eigensolver stability.
- **Finite Gaussian-elimination resource landed.**
  `finite-gaussian-elimination-v0` now gives the linear-algebra,
  numerical-analysis, and optimization lanes an exact rational elimination
  transcript: it checks the pivot multiplier, augmented row replacement,
  determinant pivot product, and back-substitution for
  `[[2,1],[4,5]] x = [5,17]`, then isolates the malformed eliminated RHS
  claim `7 = 8` as a source-linked QF_LRA/Farkas row. The focused learner page,
  matrix index, concept bridge, query guide, validator, and
  `math_resource_lra_routes` regression keep fixed transcript replay separate
  from general Gaussian-elimination correctness, pivoting, rank-revealing,
  sparse fill-in, conditioning, and floating-point stability theorems.
- **Finite Schur-complement resource landed.**
  `finite-schur-complement-v0` now gives the linear-algebra,
  numerical-analysis, optimization, and statistics lanes an exact rational
  block-matrix shadow: it checks `A = [[4,2],[2,3]]`, the one-by-one leading
  block inverse, `S = D - C*B^-1*C^T = 2`, determinant factorization,
  two-sided inverse replay, a positive-definite shadow, and a
  conditional-variance shadow, then isolates a malformed scalar claim
  `S = 3/2` as a source-linked QF_LRA/Farkas row. The focused learner page and
  query guides keep exact block replay separate from general Schur-complement,
  block-inverse, Gaussian-elimination, pivoting, SDP, statistical-conditioning,
  and numerical-stability theorems.
- **Finite Jordan-chain resource landed.**
  `finite-jordan-chain-v0` now gives the linear-algebra,
  numerical-analysis, and functional/operator lanes an exact rational
  non-diagonalizable matrix shadow: it checks `A = [[2,1],[0,2]]`,
  `N = A - 2I`, `A*v1 = 2*v1`, `N*v2 = v1`, `N^2 = 0`, and `P*J*P^-1 = A`,
  then isolates a malformed nilpotent-component claim as a source-linked
  QF_LRA/Farkas row. The focused learner page and query guides keep exact
  generalized-eigenvector replay separate from Jordan normal form,
  diagonalizability, multiplicity theorems, and numerical eigensolver claims.
  The public summary then reported 121 concept rows, 119 packs, 762 expected
  checks, 345 checked rows, 335 replay-only rows, 82 Lean-horizon rows, and 119
  promoted solver-reuse packs.
- **Finite singular-value shadow resource landed.**
  `finite-singular-value-shadow-v0` now gives the linear-algebra,
  numerical-analysis, and functional/operator lanes an exact rational SVD
  shadow: it checks `A^T A` for `A = [[3,0],[0,1]]`, singular-vector
  equations, `U*Sigma*V^T = A`, `||A||_2 = 3`, `||A||_F^2 = 10`, and
  `kappa_2(A) = 3`, then isolates the malformed upper-bound claim
  `sigma_max(A) <= 2` as a source-linked QF_LRA/Farkas row. The focused learner
  page and query guides keep exact rational singular-value replay separate from
  the general SVD theorem, perturbation theory, pseudospectra, rank-revealing
  algorithms, and floating-point SVD stability. The public summary then reported
  121 concept rows, 118 packs, 755 expected checks, 344 checked rows,
  330 replay-only rows, 81 Lean-horizon rows, and 118 promoted solver-reuse
  packs.
- **Finite condition-number resource landed.**
  `finite-condition-number-v0` now gives the linear-algebra,
  numerical-analysis, and functional/operator lanes an exact rational
  conditioning shadow: it checks a diagonal matrix inverse, infinity norms,
  `kappa_infinity(A) = 6`, a perturbation-bound equality case, replay-only bad
  condition-number rejection, and a source-linked QF_LRA/Farkas row for the
  malformed upper-bound claim `kappa_infinity(A) <= 5`. The focused learner
  page and query guides keep exact rational conditioning separate from
  algorithmic stability, singular-value conditioning, pseudospectra, and
  floating-point roundoff. The public summary then reported 121 concept rows,
  117 packs, 747 expected checks, 343 checked rows, 324 replay-only rows, 80
  Lean-horizon rows, and 117 promoted solver-reuse packs.
- **Finite Newton step resource landed.**
  `finite-newton-step-v0` now gives the calculus, linear-algebra,
  optimization, and numerical-analysis lanes an exact two-variable Newton-step
  replay: it checks the fixed quadratic's gradient, Hessian, positive leading
  minors, Hessian inverse, Newton direction, stationary next point, and
  objective decrease, then isolates the malformed next-coordinate claim as a
  source-linked QF_LRA/Farkas row. The focused learner page keeps Newton
  convergence, globalization, trust-region methods, conditioning, and
  floating-point Newton algorithms in theorem or numerical-honesty lanes. The
  public summary then reported 121 concept rows, 116 packs, 740 expected
  checks, 342 checked rows, 319 replay-only rows, 79 Lean-horizon rows, and
  116 promoted solver-reuse packs.
- **Finite covariance matrix resource landed.**
  `finite-covariance-matrix-v0` now gives the statistics, probability, and
  linear-algebra lanes an exact finite-sample covariance replay: it checks the
  rational sample mean vector, centered rows, centered Gram matrix, population
  covariance matrix, and two-by-two positive-semidefinite shadow, then isolates
  the malformed off-diagonal covariance entry as a source-linked
  QF_LRA/Farkas row. The focused learner page keeps statistical inference,
  covariance-estimator consistency, PCA theorem claims, random-matrix
  asymptotics, and floating-point covariance algorithms in theorem or
  numerical-honesty lanes.
- **Finite Cholesky decomposition resource landed.**
  `finite-cholesky-decomposition-v0` now gives the matrix-computation,
  numerical-linear-algebra, and optimization lanes an exact rational Cholesky
  factorization replay: it checks lower-triangular `L`, positive diagonal
  entries, `L*L^T = A`, and two-by-two leading principal minors, then isolates
  the malformed bottom-right product entry as a source-linked QF_LRA/Farkas
  row. The focused learner page keeps Cholesky existence, uniqueness
  conventions, algorithm correctness, conditioning, and floating-point
  stability in theorem or numerical-honesty lanes. That Cholesky landing is now
  superseded by the covariance counters in the current summary above.
- **Finite QR decomposition resource landed.**
  `finite-qr-decomposition-v0` now gives the matrix-computation and numerical
  linear-algebra lanes an exact rational QR factorization replay: it checks
  `Q^T Q = I`, upper-triangular `R`, and `Q*R = A`, then isolates the
  malformed bottom-right product entry as a source-linked QF_LRA/Farkas row.
  The focused learner page keeps QR existence, uniqueness conventions,
  Gram-Schmidt/Householder correctness, conditioning, and floating-point
  stability in theorem or numerical-honesty lanes. That QR landing is now
  superseded by the Cholesky counters in the current summary above.
- **Finite Walsh-Hadamard transform resource landed.**
  `finite-walsh-hadamard-transform-v0` now gives the linear-algebra and
  functional-analysis lanes an exact order-4 Walsh-Hadamard transform replay:
  it checks orthogonality, `Hx`, inverse reconstruction, and Parseval scaling,
  then isolates the malformed second coefficient claim as a source-linked
  QF_LRA/Farkas row. The focused learner page keeps fast-transform algorithms,
  Fourier-analysis generalizations, and infinite-dimensional orthogonal
  expansions in the Lean-horizon lane. The public summary then reported 121
  concept rows, 112 packs, 713 expected checks, 338 checked rows, 300
  replay-only rows, 75 Lean-horizon rows, and 112 promoted solver-reuse packs.
- **Finite DAG topological-order QF_LIA promotion landed.**
  `finite-dag-topological-order-v0` now has
  `qf-lia-bad-topological-edge-order`, a source-linked SMT-LIB artifact and
  focused `math_resource_lia_routes` regression for the final finite
  edge-order contradiction `2 < 1`. Solver reuse is promoted only for that
  checked arithmetic-evidence row; the finite replay rows still own vertex
  coverage, edge-position checking, and cycle-obstruction replay, and
  topological-sort algorithm correctness remains Lean-horizon work. The public
  summary then reported 121 concept rows, 111 packs, 706 expected checks, 337
  checked rows, 295 replay-only rows, 74 Lean-horizon rows, and 111 promoted
  solver-reuse packs, with no non-benchmark-horizon math pack remaining.
- **Finite shortest-path QF_LRA/Farkas promotion landed.**
  `finite-shortest-path-v0` now has
  `qf-lra-bad-shorter-distance-potential-bound`, a source-linked SMT-LIB
  artifact and focused `math_resource_lra_routes` regression for the final
  finite potential-bound contradiction `5 <= 4`. Solver reuse is promoted only
  for that checked `UnsatFarkas` row; the finite replay rows still own
  path-length, edge-relaxation, and potential-certificate arithmetic, and
  arbitrary-graph shortest-path correctness remains Lean-horizon work. Current
  public resource totals are recorded in the latest process-lane entry above.
- **Finite flow/cut QF_LRA/Farkas promotion landed.**
  `finite-flow-cut-v0` now has `qf-lra-bad-flow-value-cut-bound`, a
  source-linked SMT-LIB artifact and focused `math_resource_lra_routes`
  regression for the final finite cut-bound contradiction `4 <= 3`. Solver
  reuse is promoted only for that checked `UnsatFarkas` row; the finite replay
  rows still own capacity, conservation, and cut-capacity arithmetic, and the
  arbitrary-network max-flow/min-cut theorem remains Lean-horizon work. Current
  public resource totals are recorded in the latest process-lane entry above.
- **Chain-complex torsion theorem-boundary resource landed.**
  `chain-complex-torsion-theorem-boundary.md` now separates
  `finite-chain-complex-torsion-v0` finite free abelian chain-complex replay,
  one-entry Smith diagonal/torsion replay, torsion-generator replay, checked
  bad-boundary divisibility replay, and checked QF_LIA/Diophantine `2*k = 1`
  evidence from general Smith normal form, finitely-generated-abelian-group
  classification, quotient-module, universal-coefficient, Ext/Tor,
  exact-sequence, chain-homotopy, and topological-invariance claims. The
  theorem-horizon, topology/homology, consumer, learner, matrix, and
  smoke-query docs now expose the boundary through pack-specific
  horizon-frontier and checked-row queries.
- **Conditional-expectation theorem-boundary resource landed.**
  `conditional-expectation-theorem-boundary.md` now separates
  `finite-conditional-expectation-v0` finite partition averages,
  total-expectation replay, nested-partition tower replay, conditional
  variance decomposition, and checked QF_LRA/Farkas bad high-block,
  total-expectation, tower, and variance rows from Radon-Nikodym,
  general conditional expectation, regular conditional probability,
  martingale, and stopping-time claims. The theorem-horizon, probability,
  measure, consumer, learner, and smoke-query docs now expose the boundary
  through pack-specific horizon-frontier and checked-row queries.
- **Monoid/permutation theorem-boundary resource landed.**
  `monoid-permutation-theorem-boundary.md` now separates
  `finite-monoids-v0` exact transformation-monoid replay, unit/idempotent
  recomputation, replay-only bad associativity rejection, and checked
  QF_UF/Alethe associativity evidence plus `finite-permutation-groups-v0`
  `S3` composition, cycle/sign, natural-action, replay-only bad
  nonbijection, and checked QF_UF/Alethe injectivity evidence from general
  semigroup, monoid, Cayley, conjugacy, Sylow, and representation-theory
  claims. The theorem-horizon, algebra/discrete learner, algebra query,
  consumer, and smoke-query docs now expose both packs through
  pack-specific horizon-frontier and checked-row queries.
- **Group-action theorem-boundary resource landed.**
  `group-action-theorem-boundary.md` now separates
  `finite-group-actions-v0` exact action-law replay, orbit/stabilizer
  recomputation, Burnside fixed-point averaging, replay-only bad
  identity/compatibility rejection, and checked QF_UF/Alethe
  identity-action/action-compatibility evidence from arbitrary
  group-action, orbit-stabilizer, Burnside/Cauchy-Frobenius, quotient-action,
  Sylow-action, class-equation, representation-theory, and transported
  structure claims. The theorem-horizon, algebra/discrete learner, algebra
  query, consumer, and smoke-query docs now expose the finite group-action
  boundary through pack-specific checked-row and horizon-frontier queries.
- **Fubini/Tonelli theorem-boundary resource landed.**
  `fubini-tonelli-theorem-boundary.md` now separates
  `finite-product-measure-v0` exact Cartesian-product table replay, rectangle
  probabilities, marginal replay, finite direct/iterated-sum replay, and
  checked bad product-probability/bad marginal QF_LRA/Farkas evidence from
  general product-measure construction, Fubini, Tonelli, section
  measurability, sigma-finite hypotheses, and almost-everywhere theorem
  claims. The theorem-horizon, measure/probability, learner-map, and
  smoke-query docs now expose the finite-product-measure boundary through
  pack-specific checked-row and horizon-frontier queries.
- **Lebesgue-integration theorem-boundary resource landed.**
  `lebesgue-integration-theorem-boundary.md` now separates
  `finite-integration-v0` exact simple-function integral replay,
  indicator-integral replay, finite linearity replay, replay-only bad
  expectation rejection, and checked `qf-lra-bad-expectation` QF_LRA/Farkas
  evidence from Lebesgue integration, monotone/dominated convergence,
  Fubini/Tonelli, almost-everywhere, product-measure, and stochastic-integration
  theorem claims. The theorem-horizon, measure/probability, learner-map, and
  smoke-query docs now expose the finite-integration boundary through
  pack-specific checked-row and horizon-frontier queries.
- **Convexity theorem-boundary resource landed.**
  `convexity-theorem-boundary.md` now separates `convexity-rational-v0` exact
  midpoint Jensen replay, finite second-difference checks, affine-threshold
  replay, and checked bad midpoint/bad threshold QF_LRA/Farkas rows from
  Jensen, convexity-equivalence, separation, duality, KKT/SDP, first-order
  optimality, nonsmooth, and convergence theorem claims. The theorem-horizon,
  optimization/convexity, learner-map, and smoke-query docs now expose the
  convexity boundary through pack-specific checked-row and horizon-frontier
  queries.
- **Calculus theorem-boundary resource landed.**
  `calculus-theorem-boundary.md` now separates
  `calculus-algebraic-shadow-v0`, `calculus-riemann-sum-v0`, and
  `multivariable-calculus-rational-v0` exact polynomial derivative,
  product-rule, tangent, finite Riemann-sum, antiderivative, gradient,
  Jacobian, Hessian, and scoped QF_LRA/Farkas evidence from differentiability,
  MVT, integrability, FTC, inverse/implicit-function, change-of-variables, and
  manifold-calculus theorem claims. The analysis/numerical, dynamics,
  theorem-horizon, learner-index, rational-real, linear-algebra, and
  smoke-query docs now expose the boundary through pack-specific checked-row
  and horizon-frontier queries.
- **Orientation/area theorem-boundary resource landed.**
  `orientation-area-geometry-theorem-boundary.md` now separates
  `orientation-area-geometry-v0` exact signed-area/orientation,
  affine-area-scaling, and barycentric replay plus scoped QF_LRA/Farkas
  evidence from oriented-geometry, affine-volume, determinant/Jacobian,
  change-of-variables, differential/manifold, higher-dimensional, and
  numerical-geometry theorem claims. The geometry, theorem-horizon,
  learner-index, rational-real, linear-algebra, and smoke-query docs now expose
  the boundary through pack-specific checked-row and horizon-frontier queries.
- **Rigid-configuration theorem-boundary resource landed.**
  `rigid-configuration-geometry-theorem-boundary.md` now separates
  `rigid-configuration-geometry-v0` exact triangle distance-table,
  translation-isometry, and congruent-triangle replay plus scoped
  QF_LRA/Farkas evidence from graph rigidity, rigid-motion classification,
  synthetic-rigidity, higher-dimensional, manifold, and numerical-geometry
  theorem claims. The geometry, theorem-horizon, learner-index, rational-real,
  linear-algebra, and smoke-query docs now expose the boundary through
  pack-specific checked-row and horizon-frontier queries.
- **Incidence-geometry theorem-boundary resource landed.**
  `incidence-geometry-theorem-boundary.md` now separates
  `incidence-geometry-v0` exact line-equation, non-parallel intersection, and
  point-on-line replay plus scoped QF_LRA/Farkas evidence from projective
  duality, named configuration, synthetic-incidence, algebraic-incidence, and
  numerical-geometry theorem claims. The geometry, theorem-horizon,
  learner-index, rational-real, linear-algebra, and smoke-query docs now
  expose the boundary through pack-specific checked-row and horizon-frontier
  queries.
- **Affine-geometry theorem-boundary resource landed.**
  `affine-geometry-theorem-boundary.md` now separates `affine-geometry-v0`
  exact affine-map, midpoint, collinearity, and fixed distance replay plus
  scoped QF_LRA/Farkas evidence from affine-combination, incidence, ratio,
  projective, synthetic, differential, and numerical-geometry theorem claims.
  The geometry, theorem-horizon, learner-index, rational-real, linear-algebra,
  and smoke-query docs now expose the boundary through pack-specific
  checked-row and horizon-frontier queries.
- **Complex-analysis theorem-boundary resource landed.**
  `complex-analysis-theorem-boundary.md` now separates `complex-algebraic-v0`,
  `complex-plane-transforms-v0`, `polynomial-identities-v0`, and
  `polynomial-factorization-rational-v0` exact complex real-pair, fixed
  transform, displayed root, coefficient, division, GCD, square-free, and
  rational factorization replay plus scoped QF_LRA/Farkas and
  QF_LIA/Diophantine evidence from holomorphic, Cauchy/residue,
  analytic-continuation, conformal-map, algebraic-closure, fundamental theorem
  of algebra, and arbitrary factorization theorem claims. The number-system,
  algebra, rational-real, analysis/numerical, theorem-horizon, learner-index,
  and smoke-query docs now expose the boundary through pack-specific
  checked-row and horizon-frontier queries.

- **Topology theorem-boundary resource landed.**
  `topology-theorem-boundary.md` now separates `finite-topology-v0`,
  `finite-compactness-v0`, `finite-connectedness-v0`,
  `finite-continuous-maps-v0`, `finite-quotient-topology-v0`, and
  `finite-specialization-order-v0` finite open-set, cover, clopen,
  preimage, quotient-fiber, and specialization-order replay plus scoped
  Bool/CNF and QF_UF/Alethe evidence from arbitrary-space compactness,
  connectedness, continuity, homeomorphism-invariance, quotient,
  specialization, metrization, and algebraic-topology theorem claims. The
  topology horizon map, metric-ball index, sets/foundations page,
  theorem-horizon guide, learner index, and smoke-query docs now expose the
  boundary through pack-specific checked-row and horizon-frontier queries.

- **Algebra homomorphism/quotient theorem-boundary resource landed.**
  `algebra-homomorphism-quotient-theorem-boundary.md` now separates
  `finite-algebra-homomorphisms-v0` and `finite-ideals-v0` finite map,
  kernel/image, ideal, quotient, representative-independence, and scoped
  QF_UF/Alethe evidence from general isomorphism, correspondence, quotient,
  localization, Noetherian, and ideal-theory theorem claims. The algebra,
  equality-certificate, theorem-horizon, learner-index, and smoke-query docs
  now expose the boundary through pack-specific checked-row, Alethe-route,
  quotient drilldown, and horizon-frontier queries.

- **Linear-algebra structure theorem-boundary resource landed.**
  `linear-algebra-structure-theorem-boundary.md` now separates
  `finite-vector-spaces-v0`, `finite-dual-spaces-v0`, `finite-modules-v0`,
  and `finite-tensor-products-v0` finite table replay plus scoped
  QF_UF/Alethe closure/additivity evidence from general basis, dimension,
  duality, tensor-product, exact-sequence, module, and homological-algebra
  theorem claims. The linear-algebra, algebra, matrix, theorem-horizon, and
  smoke-query docs now expose the boundary through pack-specific checked-row,
  Alethe-route, and horizon-frontier queries.

- **Cardinality theorem-boundary resource landed.**
  `cardinality-theorem-boundary.md` now separates
  `finite-cardinality-v0` and `cardinality-principles-v0` checked finite
  function/count replay, Boolean/CNF no-injection evidence, and
  QF_LIA/Diophantine overlap-additivity evidence from Cantor
  diagonalization, Cantor-Schroeder-Bernstein, countability, choice, and
  infinite cardinal-arithmetic claims. The foundations/discrete query guide,
  theorem-horizon guide, learner map, and smoke query docs now expose the
  cardinality boundary through checked-row, route-specific, and
  horizon-frontier queries.

- **Graph-search runtime theorem-boundary resource landed.**
  `graph-search-runtime-theorem-boundary.md` now separates
  `graph-search-runtime-v0` checked finite BFS/DFS visited-counter replay,
  shortcut-tail family replay, and checked QF_LIA arithmetic bad-bound evidence
  from asymptotic BFS/DFS runtime, graph-family lower bounds, average-case
  search, heuristic search, parallel search, and benchmark claims. The
  graph/discrete query guide, theorem-horizon guide, learner map, traversal
  index, and smoke query docs now expose the runtime theorem boundary through
  both checked-row and horizon-frontier queries.

- **Graph-coloring certificate trust-boundary resource landed.**
  `graph-coloring-certificate-trust-boundary.md` now separates
  `graph-coloring-v0` replay-only triangle 3-coloring witness, checked
  same-color rejection, Boolean CNF/DRAT/LRAT triangle non-2-colorability
  evidence, and QF_BV/DRAT bit-blast evidence from chromatic-number theorems,
  bipartite-coloring equivalence, planar coloring, coloring algorithms,
  graph-minor claims, and asymptotic claims. The graph/discrete query guide,
  learner map, traversal index, and smoke query docs now expose the coloring
  trust boundary without adding a false theorem horizon row.

- **Graph-reachability certificate trust-boundary resource landed.**
  `graph-reachability-certificate-trust-boundary.md` now separates
  `graph-reachability-v0` checked finite BFS shortest-distance replay,
  deterministic DFS order replay, disconnected no-path CNF/DRAT/LRAT
  refutation, and edge-cut separation replay from BFS/DFS correctness,
  all-pairs/dynamic reachability, graph-family, graph-minor, and asymptotic
  claims. The graph/discrete query guide, learner map, traversal index, and
  smoke query docs now expose the reachability trust boundary without adding a
  false theorem horizon row.

- **Graph-matching certificate trust-boundary resource landed.**
  `graph-matching-certificate-trust-boundary.md` now separates
  `graph-matching-v0` checked finite maximum-matching replay,
  overlapping-edge rejection, augmenting-path replay, and the `K3`
  perfect-matching CNF/DRAT/LRAT refutation from Hall/Tutte theorem coverage,
  Edmonds/blossom, Hopcroft-Karp, Hungarian/weighted matching, flow reductions,
  graph minors, and asymptotic claims. The graph/discrete query guide, learner
  map, traversal index, and smoke query docs now expose the matching trust
  boundary without adding a false theorem horizon row.

- **Graph-cut certificate trust-boundary resource landed.**
  `graph-cut-certificate-trust-boundary.md` now separates `graph-cut-v0`
  checked finite minimum edge-cut replay, one-edge non-cut CNF/DRAT/LRAT
  rejection, minimum internal vertex-cut replay, and one-vertex non-cut replay
  from Menger-style cut theorems, max-flow/min-cut, scalable algorithms,
  spectral cuts, graph-partitioning guarantees, and asymptotic claims. The
  graph/discrete query guide, learner map, traversal index, and smoke query
  docs now expose the graph-cut trust boundary without adding a false theorem
  horizon row.

- **D-separation causal trust-boundary resource landed.**
  `d-separation-causal-trust-boundary.md` now separates
  `graph-d-separation-v0` checked finite active-chain replay, conditioned
  chain/fork blocking, unconditioned-collider blocking, descendant-opened
  collider replay, and source-linked chain/collider Boolean CNF/DRAT/LRAT
  blocker rows from causal identification, do-calculus, probabilistic
  graphical-model semantics, adjustment-set correctness, and statistical
  consistency. The graph/discrete query guide, learner map, probability map,
  and smoke query docs now expose the d-separation trust boundary without
  adding a false Lean-horizon theorem row.

- **Topological-sort theorem-boundary resource landed.**
  `topological-sort-theorem-boundary.md` now separates
  `finite-dag-topological-order-v0` checked finite topological-order replay,
  independent-swap order replay, bad-order rejection, and directed-cycle
  obstruction replay from finite DAG linear-extension, cycle-completeness,
  Kahn/DFS algorithm-correctness, partial-order, and asymptotic-runtime theorem
  claims. The theorem horizon, graph/discrete query guide, learner map, and
  smoke query docs now expose the topological-sort boundary directly.

- **Shortest-path theorem-boundary resource landed.**
  `shortest-path-theorem-boundary.md` now separates
  `finite-shortest-path-v0` checked path-distance replay, potential optimality
  replay, bad-path-distance rejection, and bad-shorter-distance rejection from
  arbitrary-graph shortest-path, negative-cycle, all-pairs,
  algorithm-correctness, data-structure, and asymptotic-runtime theorem
  claims. The theorem horizon, graph/discrete query guide, learner map, and
  smoke query docs now expose the shortest-path boundary directly.

- **Max-flow/min-cut theorem-boundary resource landed.**
  `max-flow-min-cut-theorem-boundary.md` now separates `finite-flow-cut-v0`
  checked finite flow-feasibility replay, saturated-cut optimality replay,
  bad-capacity rejection, and bad-flow-value rejection from arbitrary-network
  max-flow/min-cut, integrality, residual-network, algorithm-correctness,
  min-cost-flow, multi-commodity-flow, LP-duality, and asymptotic-runtime
  theorem claims. The theorem horizon, graph/discrete query guide, learner map,
  and smoke query docs now expose the flow/cut boundary directly.

- **Cyclic-geometry theorem-boundary resource landed.**
  `cyclic-geometry-theorem-boundary.md` now separates
  `finite-cyclic-geometry-v0` exact cyclic-quadrilateral replay,
  diagonal-intersection replay, opposite-angle replay, rational Ptolemy replay,
  and checked bad diagonal/bad angle/bad Ptolemy QF_LRA/Farkas rows from cyclic
  quadrilateral criteria, inscribed-angle theorems, Ptolemy, converse Ptolemy,
  angle-chasing, circle-line correspondence, synthetic-geometry,
  projective-geometry, and numerical-geometry theorem claims. The theorem
  horizon, geometry, learner-map, and smoke query docs now expose the cyclic
  boundary directly.

- **Inversion-geometry theorem-boundary resource landed.**
  `inversion-geometry-theorem-boundary.md` now separates
  `finite-inversion-geometry-v0` exact inverse-image replay,
  inverse-distance-product replay, collinearity replay, and checked bad
  inverse-coordinate/bad inverse-distance-product QF_LRA/Farkas rows from
  inversion involution, circle-line correspondence, angle-preservation,
  power-of-a-point, generalized circle-inversion, synthetic-geometry,
  projective-geometry, and numerical-geometry theorem claims. The theorem
  horizon, geometry, learner-map, and smoke query docs now expose the inversion
  boundary directly.

- **Circle-geometry theorem-boundary resource landed.**
  `circle-geometry-theorem-boundary.md` now separates
  `finite-circle-geometry-v0` exact point-on-circle replay,
  tangent-line/radius perpendicularity replay, chord-midpoint perpendicularity
  replay, circle-line intersection replay, and checked bad-radius/bad
  line-intersection QF_LRA/Farkas rows from tangent, chord,
  power-of-a-point, cyclic, inversion, synthetic-geometry, projective-geometry,
  and numerical-geometry theorem claims. The theorem horizon, geometry,
  learner-map, and smoke query docs now expose the circle boundary directly.

- **Proximal-gradient theorem-boundary resource landed.**
  `proximal-gradient-convergence-theorem-boundary.md` now separates
  `finite-proximal-gradient-v0` exact smooth-gradient replay, trial-step
  replay, L1 soft-threshold prox replay, box-plus-L1 constrained prox replay,
  composite-decrease replay, and checked bad proximal-point/bad
  composite-decrease/bad box-proximal-point QF_LRA/Farkas rows from
  proximal-map theory, subdifferential calculus, nonsmooth convex analysis,
  convergence, rate theorems, stochastic/active-set variants, and
  numerical-stability claims. The theorem horizon, optimization/convexity,
  learner-map, and smoke query docs now expose the proximal-gradient boundary
  directly.

- **Projected-gradient theorem-boundary resource landed.**
  `projected-gradient-convergence-theorem-boundary.md` now separates
  `finite-projected-gradient-v0` exact derivative replay, unconstrained
  trial-step replay, interval-projection replay, projected-descent replay, and
  checked bad projected-point/bad projected-decrease QF_LRA/Farkas rows from
  projection theory, variational-inequality characterizations, convergence,
  rate theorems, active-set identification, projected/proximal/stochastic
  variants, and numerical-stability claims. The theorem horizon,
  optimization/convexity, learner-map, and smoke query docs now expose the
  projected-gradient boundary directly.

- **Wolfe line-search theorem-boundary resource landed.**
  `wolfe-line-search-theorem-boundary.md` now separates
  `finite-wolfe-line-search-v0` exact descent-direction replay, exact
  line-minimizer replay, sufficient-decrease replay, curvature replay, and
  checked bad minimizer/bad sufficient-decrease/bad curvature QF_LRA/Farkas
  rows from Wolfe and strong-Wolfe existence, Zoutendijk-style convergence,
  rate theorems, stochastic/constrained variants, and numerical-stability
  claims. The theorem horizon, optimization/convexity, learner-map, and smoke
  query docs now expose the Wolfe boundary directly.

- **Line-search convergence theorem-boundary resource landed.**
  `line-search-convergence-theorem-boundary.md` now separates
  `finite-line-search-v0` exact descent-direction replay, Armijo trial
  rejection replay, accepted backtracked-step replay, and checked bad Armijo,
  bad descent-direction, and bad accepted-candidate QF_LRA/Farkas rows from
  line-search termination, sufficient-decrease, Wolfe-condition variants,
  convergence rates, stochastic/projected/proximal variants, and numerical
  stability theorem claims. The theorem horizon, optimization/convexity,
  learner-map, and smoke query docs now expose the line-search boundary
  directly.

- **Gradient-descent convergence theorem-boundary resource landed.**
  `gradient-descent-convergence-theorem-boundary.md` now separates
  `finite-gradient-descent-v0` exact quadratic gradient replay, one-step update
  replay, objective-decrease replay, descent-bound slack replay, and checked
  bad decrease/bad step-coordinate/bad descent-bound QF_LRA/Farkas rows from
  descent lemmas, smooth-convex convergence, step-size conditions, stopping
  criteria, convergence rates, stochastic/accelerated variants, and numerical
  stability theorem claims. The theorem horizon, optimization/convexity,
  learner-map, and smoke query docs now expose the gradient-descent boundary
  directly.

- **SDP duality theorem-boundary resource landed.**
  `sdp-duality-theorem-boundary.md` now separates `finite-sdp-v0` finite
  two-by-two PSD replay, trace/objective replay, dual-slack replay, zero
  duality-gap replay, and checked bad objective/bad duality-gap/bad
  slack-entry QF_LRA/Farkas rows from SDP weak duality, strong duality, Slater
  conditions, cone KKT/complementary slackness, convergence, and numerical
  stability theorem claims. The theorem horizon, optimization/convexity,
  learner-map, and smoke query docs now expose the SDP boundary directly.

- **Active-set method theorem-boundary resource landed.**
  `active-set-method-theorem-boundary.md` now separates
  `finite-active-set-qp-v0` finite unconstrained minimizer replay,
  active-face candidate replay, active-set KKT replay, inactive-slack replay,
  degenerate active-bound replay, and checked bad inactive-slack/bad
  free-gradient/bad degenerate-multiplier QF_LRA/Farkas rows from active-set
  correctness, finite termination, anti-cycling, degeneracy handling,
  convergence, warm-start, and numerical-stability theorem claims. The theorem
  horizon, optimization/convexity, learner-map, and smoke query docs now expose
  the active-set boundary directly.

- **KKT sufficiency theorem-boundary resource landed.**
  `kkt-sufficiency-theorem-boundary.md` now separates `finite-kkt-v0`
  finite constrained-quadratic grid replay, exact stationarity replay,
  complementary-slackness replay, and checked bad stationarity/bad
  complementarity QF_LRA/Farkas rows from KKT necessity, KKT sufficiency,
  constraint qualifications, duality, sensitivity, SDP/KKT specialization,
  and optimization-convergence theorem claims. The theorem horizon,
  optimization/convexity, learner-map, and smoke query docs now expose the KKT
  boundary directly.

- **Hyperplane-separation theorem-boundary resource landed.**
  `hyperplane-separation-theorem-boundary.md` now separates
  `finite-separation-v0` exact convex-combination replay, separating-hyperplane
  score replay, supporting-face replay, and checked bad convex-combination/bad
  separator QF_LRA/Farkas rows from general convex separation, Farkas duality,
  Hahn-Banach, cone/SDP duality, KKT sufficiency, and optimization theorem
  claims. The theorem horizon, optimization/convexity, learner-map, and smoke
  query docs now expose the separation boundary directly.

- **Root-finding convergence theorem-boundary resource landed.**
  `root-finding-convergence-theorem-boundary.md` now separates
  `finite-root-finding-v0` exact bisection replay, Newton-step replay,
  residual-decrease replay, and checked bad Newton-step/bad bisection-width
  QF_LRA/Farkas rows from root-existence, uniqueness, bisection convergence,
  Newton convergence, convergence-rate, error-bound, and floating-point
  stability theorem claims. The theorem horizon, analysis/numerical,
  optimization/convexity, learner-map, and smoke query docs now expose the
  root-finding boundary directly.

- **Recurrence/asymptotic theorem-boundary resource landed.**
  `recurrence-asymptotic-theorem-boundary.md` now separates
  `finite-recurrence-prefix-v0` finite Fibonacci prefix replay, affine
  recurrence replay, companion-matrix state replay, and checked bad
  Fibonacci-value/bad affine-step QF_LRA/Farkas rows from
  induction-over-all-`n`, closed-form, asymptotic-growth, convergence, and
  stability theorem claims. The theorem horizon, analysis/numerical,
  foundations/discrete, learner-map, and smoke query docs now expose the
  recurrence boundary directly.

- **Stochastic-kernel theorem-boundary resource landed.**
  `stochastic-kernel-theorem-boundary.md` now separates
  `finite-stochastic-kernels-v0` finite row-normalization replay,
  pushforward distributions, joint disintegration, kernel composition, and
  checked bad kernel-row/bad composition QF_LRA/Farkas rows from regular
  conditional probability, disintegration, measurable Markov-kernel, and
  stochastic-process theorem claims. The theorem horizon,
  probability/statistics, measure-theory, dynamics, learner-map, and smoke
  query docs now expose the stochastic-kernel boundary directly.

- **Random-variable theorem-boundary resource landed.**
  `random-variable-theorem-boundary.md` now separates
  `finite-random-variables-v0` finite total-function replay, pushforward
  distributions, expectation-through-pushforward replay, independence checks,
  and checked bad pushforward/bad expectation QF_LRA/Farkas rows from
  measurable-function, distribution-law, convergence, conditional-expectation,
  and continuous-random-variable theorem claims. The theorem horizon,
  probability/statistics, measure-theory, learner-map, and smoke query docs now
  expose the random-variable boundary directly.

- **Martingale theorem-boundary resource landed.**
  `martingale-theorem-boundary.md` now separates
  `finite-martingales-v0` finite filtration/adaptedness replay,
  martingale equalities, square-submartingale inequalities, bounded stopping,
  checked bad stopped-expectation and bad martingale QF_LRA/Farkas rows from
  martingale convergence, optional-stopping, Doob-inequality,
  stochastic-integration, and continuous-time theorem claims. The theorem
  horizon, probability/statistics, measure-theory, learner-map, and smoke
  query docs now expose the martingale boundary directly.

- **Hitting-time theorem-boundary resource landed.**
  `hitting-time-theorem-boundary.md` now separates
  `finite-hitting-times-v0` finite first-hit distribution replay, survival
  mass, absorption-probability equations, expected hitting-time equations, and
  checked QF_LRA/Farkas bad survival-mass/expected-time rows from recurrence,
  transience, optional-stopping, mixing, continuous-time Markov-process, and
  potential-theory theorem targets. The probability/statistics learner path,
  analysis/topology learner path, dynamics query guide,
  probability/statistics query guide, theorem-horizon query guide, and
  foundational smoke gate now expose the hitting-specific horizon row next to
  the checked finite shadows. This is a learner/query-depth increment over an
  existing promoted pack; public resource counts do not change.

- **Monotone-convergence theorem-boundary resource landed.**
  `monotone-convergence-theorem-boundary.md` now separates
  `bounded-monotone-sequence-v0` finite monotone-prefix replay, finite prefix
  supremum, finite tail-gap replay, and checked QF_LRA/Farkas bad
  upper-bound/tail-gap rows from arbitrary bounded monotone real sequence
  convergence, convergence to supremum, and real-completeness theorem targets.
  The analysis/topology learner path, real-completeness boundary,
  analysis/calculus horizon map, theorem-horizon query guide, analysis/numerical
  query guide, and foundational smoke gate now expose the monotone-specific
  horizon row next to the checked finite shadows. This is a learner/query-depth
  increment over an existing promoted pack; public resource counts do not
  change.

- **Euler-method theorem-boundary resource landed.**
  `euler-method-theorem-boundary.md` now separates finite explicit-Euler
  transition replay, exact finite error tables, finite invariants, and checked
  QF_LRA/Farkas bad-step/error rows from continuous ODE existence/uniqueness,
  convergence, stability, stiffness, floating-point, and PDE theorem targets.
  The analysis/topology learner path, dynamics query guide, analysis/numerical
  query guide, theorem-horizon query guide, and foundational smoke gate now
  expose the ODE horizon row next to the checked finite Euler shadows. This is
  a learner/query-depth increment over an existing promoted pack; public
  resource counts do not change.

- **Concentration theorem-boundary resource landed.**
  `concentration-theorem-boundary.md` now separates finite Markov,
  Chebyshev, union-bound, bad-tail, and bad-union replay from Chernoff,
  Hoeffding, martingale concentration, limit-theorem, and
  asymptotic-statistics targets. The probability/statistics learner path,
  theorem-horizon query guide, probability/statistics query guide, and
  foundational smoke gate now expose the concentration-specific horizon row
  next to its checked finite QF_LRA/Farkas shadows. This is a
  learner/query-depth increment over an existing promoted pack; public
  resource counts do not change.

- **Chebyshev theorem-boundary resource landed.**
  `chebyshev-theorem-boundary.md` now separates finite Chebyshev recurrence,
  Vandermonde, interpolation, and alternating-residual replay from Haar-space,
  minimax, alternation, compactness, and function-space theorem targets. The
  Chebyshev/operator learner index, theorem-horizon query guide, functional
  operator query guide, and foundational smoke gate now expose the
  Chebyshev-specific horizon row next to its checked finite QF_LRA/Farkas
  shadows. This is a learner/query-depth increment over existing promoted
  packs; public resource counts do not change.

- **Finite Bayes learner/query resource landed.**
  `finite-bayes-update-end-to-end.md` now follows the existing promoted
  `finite-probability-v0` Bayes rows through exact rational posterior replay
  (`2/13`), malformed posterior rejection (`1/5`), and the checked
  QF_LRA/Farkas bad-posterior route. Probability query docs and the
  foundational smoke gate now expose Bayes-specific row queries. This is a
  learner/query-depth increment over an existing pack, so public resource
  counts do not change.

- **Finite DAG topological-order graph resource landed.**
  `finite-dag-topological-order-v0` adds finite DAG topological-order replay,
  independent-order witness replay, bad-order rejection by a concrete
  backward-edge position, cyclic-graph rejection by directed-cycle replay, and
  a topological-sort theorem horizon. It was introduced as
  `non-benchmark-horizon`; the later
  `qf-lia-bad-topological-edge-order` promotion adds the source LIA artifact
  and checked arithmetic-evidence route for the final edge-order conflict.

- **Finite shortest-path graph resource landed.**
  `finite-shortest-path-v0` adds exact directed weighted path replay,
  potential optimality-certificate replay, malformed path-length rejection,
  claimed-shorter-distance rejection by a finite potential lower bound, and a
  shortest-path theorem horizon. It was introduced as
  `non-benchmark-horizon`; the later
  `qf-lra-bad-shorter-distance-potential-bound` promotion adds the source
  exact-arithmetic artifact and checked Farkas route for the final
  potential-bound conflict.

- **Finite flow/cut graph resource landed.**
  `finite-flow-cut-v0` adds exact directed-flow feasibility replay, saturated
  cut-capacity optimality replay, malformed capacity rejection, malformed
  flow-value rejection by finite cut bound, and a max-flow/min-cut theorem
  horizon. It was introduced as `non-benchmark-horizon`; the later
  `qf-lra-bad-flow-value-cut-bound` promotion adds the source exact-arithmetic
  artifact and checked Farkas route for the final cut-bound conflict.

- **Proof-upgrade curriculum/R5 filters landed.**
  `upgrade-frontier` now accepts `--curriculum-node` and `--solver-reuse`, so
  proof contributors can start from the formal curriculum DAG or the R5
  solver-reuse boundary before inspecting replay-only `unsat` rows and
  same-pack checked-route contrast. The proof-upgrade guide, consumer query
  docs, public data contract, detailed build ledger, and foundational smoke
  gate now exercise the `linear-algebra`/Farkas and promoted/Farkas slices.

- **Coverage-frontier action filter landed.**
  `coverage-frontier --action ...` now filters group-level field, fragment,
  curriculum-node, or decidability worklists by `seed-pack`,
  `add-checked-evidence`, `proof-upgrade`, `proof-review`,
  `theorem-horizon`, or `maintain`. The coverage-frontier guide, consumer
  query docs, public data contract, detailed build ledger, and foundational
  smoke gate now expose the proof-review path so builders can query already
  contrast-covered groups without manually scanning action columns.

- **Coverage-frontier proof-review triage landed.**
  `coverage-frontier` now reuses the pack-level promotion-state logic before
  emitting action labels, so field/fragment/curriculum groups with replay-only
  `unsat` rows and already-covered same-pack route contrast show
  `proof-review` instead of implying an automatic `proof-upgrade`. JSON output
  now includes `proof_upgrade_packs` and `proof_review_packs` samples for
  downstream tooling.

- **Pack-frontier query landed.**
  `scripts/query-foundational-resources.py pack-frontier` now ranks concrete
  packs by checked evidence, replay-only `unsat` pressure, Lean-horizon rows,
  checked-row density, action labels, route-promotion states, and finite-shadow
  state. The guide `docs/foundational-resources/PACK-FRONTIER-QUERIES.md`, the
  public contract, consumer query docs, buildout ledger, and foundational smoke
  gate now expose the drilldown from group-level frontier pressure to exact pack
  worklists without turning those ranks into theorem, benchmark, solver, or
  parity claims.

- **Theorem-horizon shadow-state triage landed.**
  `scripts/query-foundational-resources.py horizon-frontier` now reports and
  filters `shadow_state`: `checked-finite-shadow`,
  `replay-only-finite-shadow`, or `no-finite-shadow`. The theorem-horizon
  query guide, public data contract, detailed build ledger, and foundational
  smoke gate now use this to keep Lean/theorem boundaries paired with their
  finite checked/replay context before a learner or downstream consumer
  displays them.

- **Proof-upgrade promotion-state triage landed.**
  `scripts/query-foundational-resources.py upgrade-frontier` now reports and
  filters `promotion_state`: `no-route-contrast`, `partial-route-contrast`, or
  `covered-by-route-contrast`. The proof-upgrade query guide, route-family
  selector, public data contract, detailed build ledger, and foundational
  smoke gate now use this to inspect genuinely uncovered or partial
  certificate-route families before adding another checked row, keeping
  duplicate proof-shape promotions out of the default path.

- **Foundational coverage-frontier query landed.**
  `scripts/query-foundational-resources.py coverage-frontier` now ranks public
  math-resource coverage groups by checked evidence, replay-only rows,
  replay-only `unsat` rows, Lean-horizon rows, checked-row ratio, action
  hints, and sample packs. The guide
  `docs/foundational-resources/COVERAGE-FRONTIER-QUERIES.md`, the public
  contract, consumer query docs, buildout ledger, and foundational smoke gate
  now cover field, fragment, and topology curriculum-node frontier queries
  while keeping frontier pressure separate from theorem, benchmark,
  solver-performance, and parity claims.

- **Foundational coverage query landed.**
  `scripts/query-foundational-resources.py coverage` now aggregates the public
  math-resource JSON boundary by field, fragment, proof status, expected
  result, solver-reuse status, decidability class, or curriculum node. The
  query reports concept counts, pack counts, expected-check counts,
  result/proof/solver-reuse mixes, proof-cookbook route counts, sample
  concepts, and sample packs, with JSON output for downstream tools. The
  public contract, consumer query guide, and foundational smoke gate now cover
  representative field, fragment, status, result, decidability, and curriculum
  coverage groups while keeping them as discovery views rather than theorem,
  benchmark, or parity claims.

- **Rules/law coverage query landed.**
  `scripts/query-rules-as-code.py coverage` now aggregates the committed
  rules-as-code JSON boundary by domain, fragment, validation route, or proof
  status. The query reports pack counts, expected checks, generated families
  and rows, result/proof/validation counts, fragments, and sample pack ids,
  with JSON output for downstream tools. The rules/law docs and fallback
  check script now smoke-check domain, validation, proof-status, and fragment
  coverage without treating generated rows as legal advice or benchmark data.

- **Theorem-horizon frontier query landed.**
  `scripts/query-foundational-resources.py horizon-frontier` now exposes
  `lean-horizon` rows with finite checked/replay contrast directly from the
  public JSON contract. It reports pack, fields, curriculum nodes, horizon-row
  ids, finite checked and replay counts, sample finite row ids, and pack path,
  with JSON output for downstream tools. The foundational resource gate now
  smoke-checks topology, calculus, and convergence horizon-frontier queries so
  consumers can keep finite shadows separate from theorem, benchmark, and
  parity claims.

- **Proof-upgrade frontier query landed.**
  `scripts/query-foundational-resources.py upgrade-frontier` now exposes
  replay-only `unsat` rows grouped by existing certificate routes directly from
  the public JSON contract. It reports route, pack, field, replay-row ids,
  checked-row contrast, solver-reuse status, and pack path, with JSON output
  for downstream tools. The foundational resource gate now smoke-checks the
  Farkas, Alethe, Diophantine, and QF_BV frontier queries while keeping empty
  Boolean frontier results as a valid "no current candidate" state.

- **Consumer smoke JSON output landed.**
  `scripts/consume-foundational-resources.py --format json` now emits the same
  R6 contract snapshot as the text smoke: schema versions, concept and pack
  counts, expected-result counts, proof-status counts, row-label counts, and
  pack-label counts. The foundational resource gate now checks both text and
  JSON output so downstream tools do not need to parse prose.

- **Library-boundary decision refreshed.**
  `LIBRARY-BOUNDARY-DECISION.md` now reflects the 2026-07-02 R6 state: the
  public data contract, executable label audit, stronger dependency-free
  consumer smoke, current 688-row result/proof mix, row-label counts, and
  pack-label counts. The decision remains unchanged: keep the resources
  in-repo, expose JSON/query surfaces, and defer a crate or repo split until
  repeated external consumers justify a versioned API.

- **Public data contract landed.**
  `PUBLIC-DATA-CONTRACT.md` now names the R6 consumer boundary: the public JSON
  files, stable fields, schema-version expectations, compatibility rules,
  required smoke commands, and display-label counts. The standalone consumer
  smoke now reports schema versions, expected-result counts, proof-status
  counts, row-label counts, and pack-label counts without importing validators,
  generators, or solver crates.

- **Executable claim-label query landed.**
  `scripts/query-foundational-resources.py labels` now derives row and pack
  display labels from public JSON, reporting checked witnesses, checked
  refutations, finite witness replay, finite rejection replay, theorem
  horizons, checked evidence packs, theorem-boundary packs, and mixed-trust
  packs. The foundational resource smoke gate now requires representative
  label rows and pack labels, keeping the display policy executable instead of
  prose-only.

- **Claim-label matrix landed.**
  `CLAIM-LABEL-MATRIX.md` now defines the downstream display policy for
  `expected_result` plus `proof_status` pairs, mapping checked witnesses,
  checked refutations, finite witness replay, finite rejection replay, theorem
  horizons, and mixed pack cards to allowed copy. It keeps checked evidence,
  finite replay, Lean-horizon rows, solver-reuse promotion, benchmark claims,
  and parity claims separate. The public resource summary remains 121 concept
  rows, 75 bridge concepts, 108 packs, 688 expected checks, 322 checked rows,
  295 replay-only rows, and 71 Lean-horizon rows.

- **Checker-tamper matrix landed.**
  `CHECKER-TAMPER-MATRIX.md` now connects malformed source-row discovery to the
  route-specific corrupted-evidence commands for finite replay fixtures,
  Bool/CNF DRAT/LRAT, QF_BV DRAT, QF_LIA/Diophantine, QF_LRA/Farkas, and
  QF_UF/Alethe, while keeping array ROW and Lean-horizon gaps explicit. The
  proof-cookbook recipes now surface the resource-level tamper regressions
  instead of leaving them only in learner pages. The public resource summary
  remains 121 concept rows, 75 bridge concepts, 108 packs, 688 expected checks,
  322 checked rows, 295 replay-only rows, and 71 Lean-horizon rows.

- **Rejection-case query guide landed.**
  `REJECTION-CASE-QUERIES.md` now documents how reviewers and proof
  contributors find checked and replay-only malformed-claim rows, plus
  route-scoped bad-row drilldowns for Farkas, Alethe, QF_BV, Boolean, and
  Diophantine evidence. It explicitly separates public resource-row rejection
  from proof-cookbook checker-tamper regressions. The foundational resource
  smoke script now checks representative rejection-row and route-scoped bad-row
  queries. The public summary remains 121 concept rows, 75 bridge concepts,
  108 packs, 688 expected checks, 322 checked rows, 295 replay-only rows, and
  71 Lean-horizon rows.

- **Fragment-demand query guide landed.**
  `FRAGMENT-DEMAND-QUERIES.md` now documents how solver, proof, benchmark, and
  curriculum contributors query the math-resource corpus by public fragment
  metadata: Bool, QF_BV, QF_LIA, QF_LRA, QF_UF, finite replay, promoted
  solver-reuse packs, and Lean-horizon reconstruction targets. The
  foundational resource smoke script now checks representative fragment-plus-
  field pack and row drilldowns while keeping QF_NRA/NIA as explicit future
  pressure lanes until stable resource rows expose them. The public summary
  remains 121 concept rows, 75 bridge concepts, 108 packs, 688 expected checks,
  322 checked rows, 295 replay-only rows, and 71 Lean-horizon rows.

- **Trust-boundary query guide landed.**
  `TRUST-BOUNDARY-QUERIES.md` now documents status-first consumer queries for
  checked evidence, replay-only finite rows, and Lean-horizon theorem
  boundaries, keeping proof status separate from result status. The
  foundational resource smoke script now checks representative checked,
  replay-only, `not-run`, pack-level, and field-scoped trust-boundary
  drilldowns. The public summary remains 121 concept rows, 75 bridge concepts,
  108 packs, 688 expected checks, 322 checked rows, 295 replay-only rows, and
  71 Lean-horizon rows.

- **Curriculum-node query guide landed.**
  `CURRICULUM-NODE-QUERIES.md` now documents how consumers start from formal
  curriculum nodes such as `sets`, `linear-algebra`, `modular-arithmetic`, and
  `calculus`, then drill into concept rows, packs, checked field/route rows,
  and Lean-horizon boundaries. The foundational resource smoke script now
  checks representative curriculum-node concept, pack, Farkas, QF_BV,
  Diophantine, and Lean-horizon lookups. The public summary remains 121
  concept rows, 75 bridge concepts, 108 packs, 688 expected checks, 322 checked
  rows, 295 replay-only rows, and 71 Lean-horizon rows.

- **Proof-upgrade query guide landed.**
  `PROOF-UPGRADE-QUERIES.md` now documents how proof contributors find
  replay-only UNSAT rows, route-relevant packs with replay rows, checked-row
  contrasts, and Lean-horizon boundaries before promoting another certificate
  row. The foundational resource smoke script now checks representative
  replay-only row queues, route-relevant replay pack queries, and checked
  evidence contrasts. The public summary remains 121 concept rows, 75 bridge
  concepts, 108 packs, 688 expected checks, 322 checked rows, 295 replay-only
  rows, and 71 Lean-horizon rows.

- **Solver-reuse query guide landed.**
  `SOLVER-REUSE-QUERIES.md` now documents how solver, proof, benchmark, and
  fuzzing contributors find promoted packs by solver-reuse status, proof route,
  field, and checked row while keeping educational resources separate from
  theorem, benchmark, and parity claims. The foundational resource smoke script
  now checks promoted-pack lookups for Farkas, Alethe, QF_BV, graph, and
  checked-row drilldowns. The public summary remains 121 concept rows, 75
  bridge concepts, 108 packs, 688 expected checks, 322 checked rows, 295
  replay-only rows, and 71 Lean-horizon rows.

- **Theorem-horizon query guide landed.**
  `THEOREM-HORIZON-QUERIES.md` now documents how consumers find Lean/theorem
  boundary rows by route summary, pack route, field, and topic text without
  treating those rows as checked SMT or replay evidence. The foundational
  resource smoke script now checks representative Lean-horizon route, pack,
  topology, graph, and convergence queries. The public summary remains 121
  concept rows, 75 bridge concepts, 108 packs, 688 expected checks, 322 checked
  rows, 295 replay-only rows, and 71 Lean-horizon rows.

- **Finite countermodel bridge concept landed.**
  The foundational concept atlas now includes
  `bridge_finite_countermodel_replay`, making finite predicate
  countermodels, Boolean no-countermodel searches, proof-pattern
  counterexamples, relation/function table failures, and finite order/lattice
  countermodel rows queryable as one reusable concept. The foundations/discrete
  query guide and foundational-resource smoke script now include the
  concept-scoped checked-row query, and
  `docs/learn/math/finite-countermodel-replay.md` now gives the
  learner-facing trust boundary for the shared pattern.
  `COUNTERMODEL-REPLAY-QUERIES.md` now adds pack-scoped consumer queries for
  Boolean assignments, predicate tables, proof-pattern counterexamples,
  function-table conflicts, and finite order/lattice countermodels while
  keeping proof-route claims separate. The public summary now reports 121
  concept rows, 75 bridge concepts, 108 packs, 688 expected checks, 322 checked
  rows, 295 replay-only rows, and 71 Lean-horizon rows.

- **Finite-separation Farkas rows split landed.**
  `finite-separation-v0` now keeps
  `bad-convex-combination-point-rejected` and `bad-separator-rejected` as
  exact replay rows: they compute point `(1/3, 1/3)`, x-coordinate error
  `1/6`, outside score `4`, and score excess `3` before rejecting malformed
  claims. The checked proof-object paths are now the explicit
  `qf-lra-bad-convex-combination-point` and `qf-lra-bad-separator` rows linked
  to the QF_LRA/Farkas SMT-LIB artifacts and regressions. Focused validation
  and the finite-separation `math_resource_lra_routes` regressions pass; the
  public summary now reports 120 concept rows, 108 packs, 688 expected checks,
  322 checked rows, 295 replay-only rows, and 71 Lean-horizon rows.

- **Finite-root-finding Farkas rows split landed.**
  `finite-root-finding-v0` now keeps `bad-newton-step-rejected` and
  `bad-bisection-width-rejected` as exact replay rows: they compute the Newton
  iterate `17/12`, selected bisection width `1/2`, and width excess `1/6`
  before rejecting malformed claims. The checked proof-object paths are now
  the explicit `qf-lra-bad-newton-step` and
  `qf-lra-bad-bisection-width` rows linked to the QF_LRA/Farkas SMT-LIB
  artifacts and regressions. Focused validation and the finite-root-finding
  `math_resource_lra_routes` regressions pass; the public summary now reports
  120 concept rows, 108 packs, 686 expected checks, 322 checked rows, 293
  replay-only rows, and 71 Lean-horizon rows.

- **Bounded-monotone Farkas rows split landed.**
  `bounded-monotone-sequence-v0` now keeps `bad-upper-bound-rejected` and
  `bad-tail-gap-rejected` as exact replay rows: they compute `a_6 = 6/7`,
  `a_2 = 2/3`, tail gap `1/3`, and tail excess `1/12` before rejecting
  malformed claims. The checked proof-object paths are now the explicit
  `qf-lra-bad-upper-bound` and `qf-lra-bad-tail-gap` rows linked to the
  QF_LRA/Farkas SMT-LIB artifacts and regressions. Focused validation and the
  bounded-monotone `math_resource_lra_routes` regressions pass; the public
  summary now reports 120 concept rows, 108 packs, 684 expected checks, 322
  checked rows, 291 replay-only rows, and 71 Lean-horizon rows.

- **Finite-recurrence Farkas rows split landed.**
  `finite-recurrence-prefix-v0` now keeps `bad-fibonacci-value-rejected` and
  `bad-affine-step-rejected` as exact replay rows: they compute `F_6 = 8`,
  `x_4 = 15`, and transition residual `1` before rejecting malformed claims.
  The checked proof-object paths are now the explicit
  `qf-lra-bad-fibonacci-value` and `qf-lra-bad-affine-step` rows linked to the
  QF_LRA/Farkas SMT-LIB artifacts and regressions. Focused validation and the
  recurrence `math_resource_lra_routes` regressions pass; the public summary
  now reports 120 concept rows, 108 packs, 682 expected checks, 322 checked
  rows, 289 replay-only rows, and 71 Lean-horizon rows.

- **Bounded-dynamics Farkas rows split landed.**
  `bounded-dynamics-v0` now keeps `bad-transition-step-rejected`,
  `bad-threshold-step-rejected`, and `bad-invariant-bound-rejected` as exact
  recurrence replay rows: they compute next state `4`, threshold-step state
  `6`, and terminal/max state `8` before rejecting malformed claims. The
  checked proof-object paths are now the explicit `qf-lra-bad-transition-step`,
  `qf-lra-bad-threshold-step`, and `qf-lra-bad-invariant-bound` rows linked to
  the QF_LRA/Farkas SMT-LIB artifacts and regressions. Focused validation and
  the three bounded-dynamics `math_resource_lra_routes` regressions pass; the
  public summary now reports 120 concept rows, 108 packs, 680 expected checks,
  322 checked rows, 287 replay-only rows, and 71 Lean-horizon rows.

- **Finite Euler-method Farkas rows split landed.**
  `finite-euler-method-v0` now keeps `bad-max-error-bound-rejected`,
  `bad-terminal-error-rejected`, and `bad-euler-step-rejected` as exact finite
  replay rows: they recompute max error `3/4`, terminal error `3/4`, and the
  fixed Euler next state `1/2` before rejecting malformed claims. The checked
  proof-object paths are now the explicit `qf-lra-bad-max-error-bound`,
  `qf-lra-bad-terminal-error`, and `qf-lra-bad-euler-step` rows linked to the
  QF_LRA/Farkas SMT-LIB artifacts and regressions. Focused validation passes.

- **Finite Chebyshev-system Farkas rows split landed.**
  `finite-chebyshev-systems-v0` now keeps
  `bad-duplicate-node-grid-rejected`, `bad-interpolation-sample-rejected`, and
  `bad-alternating-residual-rejected` as exact finite replay rows: they
  recompute determinant `0`, `p(1)=4`, and common residual error `1/2` before
  rejecting the malformed fixed claims. The checked proof-object paths are now
  the explicit `qf-lra-bad-duplicate-node-grid`,
  `qf-lra-bad-interpolation-sample`, and
  `qf-lra-bad-alternating-residual` rows linked to the QF_LRA/Farkas artifacts
  and regressions. Focused validation passes; the public summary now reports
  120 concept rows, 108 packs, 674 expected checks, 322 checked rows, 281
  replay-only rows, and 71 Lean-horizon rows.

- **Finite operator Farkas rows split landed.**
  `finite-operator-v0` now keeps `bad-l1-sum-norm-rejected`,
  `bad-operator-bound-rejected`, and `bad-chebyshev-t3-rejected` as exact
  finite replay rows: they recompute `||u+v||_1 = 5`, `||A*x||_infty = 3`,
  and `T3(1/2) = -1` before rejecting the malformed fixed claims. The checked
  proof-object paths are now the explicit `qf-lra-bad-l1-sum-norm`,
  `qf-lra-bad-operator-bound`, and `qf-lra-bad-chebyshev-t3` rows linked to the
  QF_LRA/Farkas SMT-LIB artifacts and regressions. Focused validation passes;
  the public summary now reports 120 concept rows, 108 packs, 671 expected
  checks, 322 checked rows, 278 replay-only rows, and 71 Lean-horizon rows.

- **Finite Markov-chain Farkas rows split landed.**
  `finite-markov-chain-v0` now keeps `bad-stochastic-row-rejected` and
  `bad-stationary-distribution-rejected` as exact finite replay: they recompute
  the malformed transition row sum as `2/3` instead of accepting `1`, and
  `[1/2,1/2] * P` as `[3/8,5/8]` instead of accepting the claimed first
  coordinate `1/2`. The checked proof-object paths are now the explicit
  `qf-lra-bad-stochastic-row` and
  `qf-lra-bad-stationary-distribution` rows linked to the QF_LRA/Farkas
  SMT-LIB artifacts and regressions. Focused validation passes; the public
  summary now reports 120 concept rows, 108 packs, 668 expected checks,
  322 checked rows, 275 replay-only rows, and 71 Lean-horizon rows.

- **Finite stochastic-kernel Farkas rows split landed.**
  `finite-stochastic-kernels-v0` now keeps `bad-kernel-row-rejected` and
  `bad-kernel-composition-rejected` as exact finite replay: they recompute the
  rainy row sum as `6/5` instead of accepting `1`, and the composed
  rainy-to-early entry as `22/75` instead of accepting `1/3`. The checked
  proof-object paths are now the explicit `qf-lra-bad-kernel-row` and
  `qf-lra-bad-kernel-composition` rows linked to the QF_LRA/Farkas SMT-LIB
  artifacts and regressions. Focused validation passes; the public summary now
  reports 120 concept rows, 108 packs, 668 expected checks, 322 checked rows,
  275 replay-only rows, and 71 Lean-horizon rows.

- **Finite concentration Farkas rows split landed.**
  `finite-concentration-v0` now keeps `bad-concentration-bound-rejected` and
  `bad-union-bound-rejected` as exact finite replay: they recompute
  `P(X >= 2)=1/4` instead of accepting the claimed `1/8`, and
  `P(A union B)=3/4` instead of accepting the claimed `1/2`. The checked
  proof-object paths are now the explicit
  `qf-lra-bad-concentration-bound` and `qf-lra-bad-union-bound` rows linked
  to the existing QF_LRA/Farkas SMT-LIB artifacts and regressions. Focused
  validation passes; the public summary now reports 120 concept rows, 108
  packs, 664 expected checks, 322 checked rows, 271 replay-only rows, and 71
  Lean-horizon rows.

- **Finite hitting-time Farkas rows split landed.**
  `finite-hitting-times-v0` now keeps `bad-survival-mass-rejected` and
  `bad-expected-time-rejected` as exact finite replay: they recompute
  `P(T > 4)=5/16` instead of `1/4` and the malformed start-state
  expected-time equation right-hand side `7/2` instead of `3`. The checked
  proof-object paths are now the explicit `qf-lra-bad-survival-mass` and
  `qf-lra-bad-expected-time` rows linked to the existing QF_LRA/Farkas
  SMT-LIB artifacts and regressions. Focused validation passes; the public
  summary now reports 120 concept rows, 108 packs, 662 expected checks, 322
  checked rows, 269 replay-only rows, and 71 Lean-horizon rows.

- **Finite martingale Farkas rows split landed.**
  `finite-martingales-v0` now keeps `bad-stopped-expectation-rejected` and
  `bad-martingale-rejected` as exact finite replay: they recompute
  `E[M_tau]=0` instead of `1/2` and the up-block conditional expectation
  `3/2` instead of `1`. The checked proof-object paths are now the explicit
  `qf-lra-bad-stopped-expectation` and `qf-lra-bad-martingale` rows linked to
  the existing QF_LRA/Farkas SMT-LIB artifacts and regressions. Focused
  validation passes; the public summary now reports 120 concept rows, 108
  packs, 660 expected checks, 322 checked rows, 267 replay-only rows, and 71
  Lean-horizon rows.

- **Finite random-variable Farkas rows split landed.**
  `finite-random-variables-v0` now keeps `bad-pushforward-rejected` and
  `bad-expectation-through-pushforward-rejected` as exact finite replay: they
  recompute `P(X = long) = 1/4` instead of `1/2` and `E[X] = 20` instead of
  `25`. The checked proof-object paths are now the explicit
  `qf-lra-bad-pushforward` and
  `qf-lra-bad-expectation-through-pushforward` rows linked to the existing
  QF_LRA/Farkas SMT-LIB artifacts and regressions. Focused validation passes;
  the public summary now reports 120 concept rows, 108 packs, 658 expected
  checks, 322 checked rows, 265 replay-only rows, and 71 Lean-horizon rows.

- **Finite integration expectation Farkas row split landed.**
  `finite-integration-v0` now keeps `bad-expectation-rejected` as exact
  finite replay: it recomputes the three-atom simple-function integral as
  `5/2` while the malformed row claims `3`. The checked proof-object path is
  now the explicit `qf-lra-bad-expectation` row linked to the existing
  QF_LRA/Farkas SMT-LIB artifact and regression. Focused validation passes;
  the public summary now reports 120 concept rows, 108 packs, 656 expected
  checks, 322 checked rows, 263 replay-only rows, and 71 Lean-horizon rows.

- **Descriptive statistics variance Farkas row split landed.**
  `descriptive-statistics-v0` now keeps `bad-variance-rejected` as exact
  finite-sample replay: it recomputes mean `5/2`, second moment `15/2`,
  `mean^2 = 25/4`, and population variance `5/4` while the malformed row
  claims `3/2`. The checked proof-object path is now the explicit
  `qf-lra-bad-variance` row linked to the existing QF_LRA/Farkas SMT-LIB
  artifact and regression. Focused validation passes; the public summary now
  reports 120 concept rows, 108 packs, 655 expected checks, 322 checked rows,
  262 replay-only rows, and 71 Lean-horizon rows.

- **Linear algebra LU Farkas row split landed.**
  `linear-algebra-rational-v0` now keeps `bad-lu-product-entry-rejected` as
  exact LU replay: it computes `(L*U)[1,1]=3` while the malformed row claims
  `4`. The checked proof-object path is now the explicit
  `qf-lra-bad-lu-product-entry` row linked to the existing QF_LRA/Farkas
  SMT-LIB artifact and regression. Focused validation passes, and the
  row-scoped Farkas lookup returns the product-entry row.

- **Finite measure complement Farkas row split landed.**
  `finite-measure-v0` now keeps `bad-complement-measure-rejected` as exact
  finite replay: it computes `mu(A)=1/3`, `mu(A^c)=2/3`, and `mu(U)=1` while
  the malformed row claims `mu(A^c)=1/2`. The checked proof-object path is now
  the explicit `qf-lra-bad-complement-measure` row linked to the existing
  QF_LRA/Farkas SMT-LIB artifact and regression. Focused validation passes, and
  the row-scoped Farkas lookup returns the complement row.

- **Finite group-action Alethe rows split landed.**
  `finite-group-actions-v0` now keeps malformed identity-action and
  compatibility-table rejections as exact finite replay, and exposes the
  proof-object checks as the explicit `qf-uf-bad-identity-action` and
  `qf-uf-bad-action-compatibility` rows. Focused validation passes; the public
  summary now reports 120 concept rows, 108 packs, 652 expected checks, 322
  checked rows, 259 replay-only rows, and 71 Lean-horizon rows.

- **Finite monoid associativity Alethe row split landed.**
  `finite-monoids-v0` now keeps the malformed associativity-table rejection as
  exact finite replay and exposes the QF_UF/Alethe proof-object check as the
  explicit `qf-uf-bad-monoid-associativity` row. The replay row computes
  `(b*b)*b = a` and `b*(b*b) = b`; the source SMT-LIB artifact separately
  checks the fixed malformed associativity equality `(b*b)*b = b*(b*b)`
  against `a != b`. Focused validation passes; the public summary now reports
  120 concept rows, 108 packs, 650 expected checks, 322 checked rows, 257
  replay-only rows, and 71 Lean-horizon rows.

- **Finite permutation injectivity Alethe row split landed.**
  `finite-permutation-groups-v0` now keeps the malformed self-map rejection as
  exact finite replay and exposes the QF_UF/Alethe proof-object check as the
  explicit `qf-uf-bad-nonbijection-injectivity` row. The replay row computes
  `bad(1)=1`, `bad(2)=1`, and a missing image `2`; the source SMT-LIB
  artifact separately checks the fixed malformed injectivity claim
  `bad(1) != bad(2)`. Focused validation passes; the public summary now
  reports 120 concept rows, 108 packs, 649 expected checks, 322 checked rows,
  256 replay-only rows, and 71 Lean-horizon rows.

- **Finite ideal additive-closure Alethe row split landed.**
  `finite-ideals-v0` now keeps the malformed `{0,2}` ideal rejection as exact
  finite replay and exposes the QF_UF/Alethe proof-object check as the
  explicit `qf-uf-bad-ideal-additive-closure` row. The replay row computes
  `2 + 2 = 4` in `Z/6Z` and checks that `4` is absent from the claimed subset;
  the source SMT-LIB artifact separately checks the fixed
  additive-closure membership contradiction. Focused validation passes; the
  public summary now reports 120 concept rows, 108 packs, 648 expected checks,
  322 checked rows, 255 replay-only rows, and 71 Lean-horizon rows.

- **Rules/law workflow-reachability pack landed.**
  `workflow-reachability-v0` adds the state-machine rules shape: finite
  transition replay, generated two-step reachability rows, terminal-state
  rows, and source-linked Bool/QF_LIA checked artifacts for no-skip,
  terminal-absorbing, and implementation-equivalence obligations. The
  rules/law JSON layer now reports 7 packs, 1,037 bounded sample rows, 1,942
  generated query rows, 27 checked obligations, and 9 replayed witness rows.

- **Finite order-lattice antisymmetry Alethe row split landed.**
  `finite-order-lattices-v0` now keeps the malformed partial-order rejection
  as exact finite replay and exposes the QF_UF/Alethe proof-object check as the
  explicit `qf-uf-bad-partial-order-antisymmetry` row. The replay row computes
  `x <= y`, `y <= x`, and `x != y`; the source SMT-LIB artifact separately
  checks the fixed antisymmetry equality contradiction `x = y` against
  `x != y`. Focused validation passes; the public summary now reports 120
  concept rows, 108 packs, 647 expected checks, 322 checked rows, 254
  replay-only rows, and 71 Lean-horizon rows.

- **Finite tensor-product left-additivity Alethe row split landed.**
  `finite-tensor-products-v0` now keeps the malformed bilinear-map rejection as
  exact finite replay and exposes the QF_UF/Alethe proof-object check as the
  explicit `qf-uf-bad-bilinear-left-additivity` row. The replay row computes
  `10 + 01 = 11`, `beta(11,1) = 00`, and
  `beta(10,1)+beta(01,1)=11`; the source SMT-LIB artifact separately checks
  the fixed additivity equality contradiction
  `beta(10+01,1) = beta(10,1)+beta(01,1)`. Focused validation passes; the
  public summary now reports 120 concept rows, 108 packs, 646 expected checks,
  321 checked rows, 254 replay-only rows, and 71 Lean-horizon rows.

- **Finite dual-space covector-additivity Alethe row split landed.**
  `finite-dual-spaces-v0` now keeps the malformed covector rejection as exact
  finite replay and exposes the QF_UF/Alethe proof-object check as the explicit
  `qf-uf-bad-covector-additivity` row. The replay row computes
  `10 + 01 = 11`, `f(11) = 1`, and `f(10)+f(01)=0`; the source SMT-LIB
  artifact separately checks the fixed additivity equality contradiction
  `f(10+01) = f(10)+f(01)`. Focused validation passes; the public summary now
  reports 120 concept rows, 108 packs, 645 expected checks, 320 checked rows,
  254 replay-only rows, and 71 Lean-horizon rows.

- **Finite vector-space additive-closure Alethe row split landed.**
  `finite-vector-spaces-v0` now keeps the malformed `{00,10,01}` subspace
  rejection as exact finite replay and exposes the QF_UF/Alethe proof-object
  check as the explicit `qf-uf-bad-subspace-addition-closure` row. The replay
  row computes `10 + 01 = 11` in `F2^2` and rejects the subset because `11` is
  absent; the source SMT-LIB artifact separately checks the membership
  contradiction `in_subset(add(10,01)) = present` against `in_subset(11) =
  absent`. Focused validation and the existing
  `finite_vector_spaces_bad_subspace_emits_checked_alethe` regression pass; the
  public summary now reports 120 concept rows, 108 packs, 644 expected checks,
  319 checked rows, 254 replay-only rows, and 71 Lean-horizon rows.

- **Finite module scalar-closure Alethe row split landed.**
  `finite-modules-v0` now keeps the malformed `{0,1}` submodule rejection as
  exact finite replay and exposes the QF_UF/Alethe proof-object check as the
  explicit `qf-uf-bad-submodule-scalar-closure` row. The replay row computes
  `2*1 = 2` in the regular `Z/4Z` module and rejects the subset because `2` is
  absent; the source SMT-LIB artifact separately checks the membership
  contradiction `in_subset(smul(2,1)) = present` against `in_subset(2) =
  absent`. Focused validation and the existing
  `finite_modules_bad_submodule_emits_checked_alethe` regression pass; the
  public summary now reports 120 concept rows, 108 packs, 643 expected checks,
  318 checked rows, 254 replay-only rows, and 71 Lean-horizon rows.

- **Finite continuous-map preimage Alethe row split landed.**
  `finite-continuous-maps-v0` now exposes the hidden preimage-membership
  artifact as a first-class checked row,
  `qf-uf-bad-preimage-membership`. The finite replay row still owns the
  topological failure that `preimage({u}) = {0}` is not Sierpinski-open; the
  QF_UF/Alethe row separately checks the malformed table that excludes `0`
  despite `f(0)=u` and `u in {u}`. Focused validation and the existing
  `finite_continuous_maps_bad_preimage_emits_checked_alethe` regression pass;
  the public summary now reports 120 concept rows, 108 packs, 642 expected
  checks, 317 checked rows, 254 replay-only rows, and 71 Lean-horizon rows.

- **Finite simplicial homology boundary-square row landed.**
  `finite-simplicial-homology-v0` now promotes the false
  `boundary(boundary([a,b,c]))` coefficient row through exact finite replay and
  QF_LIA/Diophantine evidence. The replay row expands the first boundary,
  checks the `[b]` vertex contributions `-1 + 1 = 0`, and rejects the malformed
  claim that the coefficient is `1`; the SMT-LIB artifact isolates the same
  conflict as `coeff_b = 0` and `coeff_b = 1`. Focused validation and the new
  `finite_simplicial_bad_boundary_square_coefficient_emits_checked_diophantine_evidence`
  regression pass; the public summary now reports 120 concept rows, 108 packs,
  642 expected checks, 317 checked rows, 254 replay-only rows, and 71
  Lean-horizon rows.

- **Finite conditional-variance decomposition row landed.**
  `finite-conditional-expectation-v0` now replays the finite law of total
  variance for the four-atom conditioning table:
  `Var(X)=35/4`, `E[Var(X|G)]=5/2`, and `Var(E[X|G])=25/4`. The malformed row
  claims total variance `9` and is source-linked to a QF_LRA/Farkas SMT-LIB
  artifact plus the shared `math_resource_lra_routes` regression. This adds a
  distinct conditional-moment proof shape without claiming Radon-Nikodym,
  regular conditional probabilities, martingale convergence, or
  measure-theoretic conditional expectation.

- **Grant allocation rules/law pack landed.**
  `grant-allocation-v0` adds the fifth rules-as-code pack, reusing exact
  rational allocation shares, budget balance, minimum-share floors,
  administrative caps, finite rational replay, and source-linked QF_LRA/Farkas
  checked fixtures. The generated rules query dashboard now reports 5 packs,
  1,007 bounded sample rows, 1,766 generated query rows, 22 checked rows, and 7
  replayed rows.

- **Algebra equality-certificate boundary landed.**
  [`algebra-equality-certificate-boundary.md`](docs/learn/math/algebra-equality-certificate-boundary.md)
  now makes the finite algebra promotion rule explicit: table replay owns the
  concrete finite structure, while QF_UF/Alethe rows are added only for isolated
  equality, congruence, closure, representative, preservation, identity-action,
  action-compatibility, or bilinearity certificate shapes. The generated concept atlas now includes
  `bridge_algebra_equality_certificate_boundary`; the public summary reports
  120 concept rows: 23 curriculum nodes, 18 field rows, 74 bridge rows, and 5
  example-family rows.

- **Finite group-action compatibility QF_UF row landed.**
  [`finite-group-actions-v0`](artifacts/examples/math/finite-group-actions-v0/)
  now links `bad-compatibility-rejected` to a source-level QF_UF/Alethe artifact
  for the action law `s.(s.01) = (s*s).01`. The validator recomputes the
  finite-table failure before the shared `math_resource_uf_routes` regression
  emits and checks the Alethe certificate, keeping orbit-stabilizer and
  Burnside/Cauchy-Frobenius theorem claims in the Lean-horizon lane.

- **Real-completeness theorem-boundary page landed.**
  [`real-completeness-theorem-boundary.md`](docs/learn/math/real-completeness-theorem-boundary.md)
  now expands the analysis/calculus horizon map's real-completeness row into a
  concrete dependency ledger. It links rational interval replay, finite
  sequence-tail and Cauchy-tail rows, bounded monotone-prefix checks, metric
  continuity, RCF shadows, and finite compactness to copyable checked-row
  queries and replay commands, while keeping least-upper-bound completeness,
  Cauchy completeness, monotone convergence, Heine-Borel, and uniform
  continuity in the no-`sorry` Lean-horizon lane.

- **Matrix-corpus source-artifact regression pass landed.**
  Five existing exact-rational matrix/statistics Farkas rows now prove the
  committed SMT-LIB artifacts directly instead of duplicating constraints inline:
  least-squares bad coefficients, numerical residual bound, finite random-matrix
  trace-square moment, spectral bad eigenpair, and matrix-invariants bad
  characteristic polynomial. The pack validators now pin the exact artifact
  paths plus artifact-backed regression names. The inner-product negative-norm
  row remains on the existing inline Farkas route because the current SMT-LIB
  parser/evidence path rejects that strict-inequality artifact; the pack still
  validates and the limitation is explicit in the route choice.

- **Graph d-separation collider CNF route landed.**
  `graph-d-separation-v0` now promotes `collider-unconditioned-blocks` through a
  source-linked DIMACS artifact for the finite DAG `a -> b <- c` with empty
  conditioning. The validator pins the exact graph, path enumeration, DIMACS
  header, and clauses; the shared Boolean resource regression emits DRAT,
  elaborates it to LRAT, and checks both proof objects independently. This
  closes the graph-depth queue item with a distinct learner-readable
  collider-specific Boolean proof shape; public check counts stay at 634 because
  this upgrades an existing checked row rather than adding a new row.

- **Finite probability total-variation row landed.**
  `finite-probability-v0` now has exact replay for total variation between two
  normalized three-atom distributions: atomwise differences `1/6, 0, 1/6`,
  `l1 = 1/3`, and `TV = 1/6`. The malformed row claims `TV = 1/4` and is routed
  through source-linked QF_LRA/Farkas evidence plus the shared
  `math_resource_lra_routes` regression. For that increment, the public summary
  reported
  119 concept rows, 108 non-template packs, 634 expected checks, 310 checked
  rows, 253 replay-only rows, and 71 Lean-horizon rows.

- **Proof-route learner snippets landed.**
  [`proof-route-learner-snippets.md`](docs/learn/math/proof-route-learner-snippets.md)
  now gives reusable learner-facing trust-boundary snippets for Boolean
  CNF/LRAT, QF_LRA/Farkas, QF_UF/Alethe, QF_LIA/Diophantine, and QF_BV/DRAT
  rows. The comprehensive resource queue now treats the route-snippet refresh
  as landed, with future proof-route work focused on distinct finite-table,
  graph, algebra, arithmetic, and bit-width promotions rather than duplicate
  checked rows.

- **Proof-route family selector landed.**
  [`PROOF-ROUTE-FAMILY-SELECTION.md`](docs/foundational-resources/PROOF-ROUTE-FAMILY-SELECTION.md)
  now picks one representative replay-heavy family per active proof route
  (Boolean CNF/LRAT, QF_BV, QF_LIA/Diophantine, QF_LRA/Farkas, QF_UF/Alethe,
  and Lean horizon), records the current checked-row representative, and states
  when another compact negative row is worth promoting. The comprehensive
  resource queue now treats the family-selection step as landed.

- **Learner coverage audit landed.**
  [`LEARNER-COVERAGE-AUDIT.md`](docs/foundational-resources/LEARNER-COVERAGE-AUDIT.md)
  records the mechanical R3 learner-spine check for the current math inventory:
  108 non-template packs, 108 focused-lesson links, and no path-only,
  index-only, or missing learner buckets. The comprehensive resource queue now
  treats learner coverage as audited and moves the next commit-sized work back
  to proof-route depth.

- **Rules/law trust-boundary learner page landed.**
  [`docs/learn/rules-law-trust-boundary.md`](docs/learn/rules-law-trust-boundary.md)
  now walks through the current eligibility, authorization, tax/benefit, and
  procurement packs from human-authored source rule to formal model, replayed
  witness, checked obligation, and explicit legal/theorem horizon. It links
  the crosswalk, pattern matrix, and query guide, and records the next-pack rule:
  add another rule pack only for a distinct proof shape or repeated consumer
  need.

- **Rules/law pattern matrix landed.**
  [`RULES-LAW-PATTERN-MATRIX.md`](docs/foundational-resources/RULES-LAW-PATTERN-MATRIX.md)
  now maps finite predicates, exclusions, role/tenant relations, thresholds,
  caps, deadlines, monotonicity, version transitions, precedence, and bounded
  implementation-equivalence patterns back to math concept rows, proof routes,
  current rule packs, generated query families, and copyable commands. The
  `just rules-as-code` smoke gate now also exercises monotonicity lookup,
  adjacent-family lookup, and quality-monotonicity generated rows without
  adding a premature rule ontology or legal/benchmark claims.

- **Rules/law query surface landed.**
  [`RULES-LAW-QUERIES.md`](docs/foundational-resources/RULES-LAW-QUERIES.md)
  and `scripts/query-rules-as-code.py` now expose the rules-as-code JSON
  boundary through copyable summary, pack, checked-obligation,
  generated-family, and bounded-row queries. `just rules-as-code` now also
  smoke-checks summary counts, procurement pack lookup, checked procurement
  obligations, quality-score generated families, and late-submission generated
  rows, while preserving the no-legal-advice/no-benchmark boundary.

- **Procurement scoring rules/law pack landed.**
  `procurement-scoring-v0` now adds the fourth rules-as-code pack, reusing
  finite predicate exclusions, bid caps, encoded submission deadlines,
  small-business bonus-threshold witnesses, score monotonicity, and bounded
  implementation-equivalence checks. Five source-linked Bool/QF_LIA obligations
  now emit certified evidence through the shared
  `rules_as_code_examples` regression: debarment exclusion, late submission,
  bid-cap enforcement, score monotonicity, and implementation equivalence. The
  generated rules query dashboard reported 4 packs, 882 bounded sample rows,
  1,626 generated query rows, 17 checked rows, and 6 replayed rows for that
  increment.

- **Polynomial coefficient/factor bridge row landed.**
  The generated concept atlas now includes
  `bridge_polynomial_coefficient_factor_replay`, grouping fixed coefficient
  tuples, division and factor witnesses, coefficient windows, root-finding
  steps, derivative shadows, and polynomial geometry obligations under one
  reusable concept. Concept-scoped Diophantine and Farkas queries now return
  checked rows from polynomial identities, rational factorization, generating
  functions, root finding, calculus shadows, and rational geometry while
  keeping general factorization, algebraic closure, root distribution, and
  generating-function convergence in the proof-horizon lane. For that increment,
  the public summary reported 119 concept rows: 23 curriculum nodes, 18 field rows, 73 bridge
  concepts, and 5 example-family rows; pack and check counts remain 108 packs,
  632 expected checks, 309 checked rows, 252 replay-only rows, and 71
  Lean-horizon rows.

- **Bounded-family/asymptotic bridge row landed.**
  The generated concept atlas now includes
  `bridge_bounded_family_asymptotic_boundary`, grouping finite BFS/DFS runtime
  counters, finite recurrence prefixes, fixed coefficient windows, bounded
  dynamics traces, and finite Euler error rows under one reusable concept.
  The row makes existing checked LIA and Farkas rows queryable by concept while
  keeping asymptotic runtime, closed-form recurrence, convergence-rate, and
  limiting theorem claims in the Lean-horizon lane. For that increment, the
  public summary reported 118 concept rows: 23 curriculum nodes, 18 field rows, 72 bridge
  concepts, and 5 example-family rows; pack and check counts remain 108 packs,
  632 expected checks, 309 checked rows, 252 replay-only rows, and 71
  Lean-horizon rows.

- **Analysis bridge-concept rows landed.**
  The generated concept atlas now includes six reusable analysis bridge rows:
  `bridge_rational_interval_replay`, `bridge_sequence_tail_shadow`,
  `bridge_cauchy_tail_shadow`, `bridge_squeeze_shadow`,
  `bridge_derivative_identity_shadow`, and `bridge_integration_horizon`.
  These rows make rational intervals, finite tails, Cauchy-tail enumeration,
  squeeze-style side conditions, symbolic derivative samples, finite integrals,
  and theorem-horizon boundaries queryable across existing packs without
  creating new solver artifacts. For that increment, the public summary
  reported 117 concept rows: 23 curriculum nodes, 18 field rows, 71 bridge
  concepts, and 5 example-family rows; pack and check counts remained
  108 packs, 632 expected checks, 309 checked rows, 252 replay-only rows, and
  71 Lean-horizon rows.

- **Sequence-limit bad reciprocal-tail QF_LRA row landed.**
  `sequence-limit-shadow-v0` now includes a checked rejection for a malformed
  reciprocal-tail bound: exact replay reuses the reciprocal sequence witness,
  computes `a_2 = 1/3`, and rejects the strict claim that this distance from
  `0` is below `1/4`. The validator pins the source witness, claimed tail
  start, witness index, limit, epsilon, witness value, tail distance, positive
  excess, source SMT-LIB artifact, and route regression. The shared
  `math_resource_lra_routes` regression parses the new QF_LRA artifact and
  checks the `UnsatFarkas` evidence. For that increment, generated dashboards
  and the public query summary reported 117 concept rows, 108 non-template
  packs, 632 expected checks, 309 checked rows, 252 replay-only rows, and
  71 Lean-horizon rows.

- **Metric-continuity bad open-ball-preimage QF_LRA row landed.**
  `metric-continuity-v0` now includes a checked rejection for a malformed
  open-ball preimage row: exact finite metric replay computes the preimage of
  `|y - 0| < 1` as `{p0, p1}`, while the bad row claims `p2` is included even
  though `|f(p2) - 0| = 1`. The validator pins the finite points, function
  values, target value, epsilon, actual preimage, claimed point, source SMT-LIB
  artifact, and route regression. The shared `math_resource_lra_routes`
  regression parses the source QF_LRA artifact and checks the `UnsatFarkas`
  evidence. Generated dashboards and the public query summary now report 111
  concept rows, 108 non-template packs, 632 expected checks, 309 checked rows,
  252 replay-only rows, and 71 Lean-horizon rows.

- **Linear algebra bad nullspace-component QF_LRA row landed.**
  `linear-algebra-rational-v0` now includes a checked rejection for a
  malformed nullspace row: exact replay checks `A*v = [0, 0]` for
  `A = [[1, 2], [2, 4]]` and `v = [2, -1]`, while the bad row claims the first
  component is `1` instead of `2`. The validator pins the matrix, null vector,
  zero vector, component index, actual component, claimed component, source
  SMT-LIB artifact, and route regression. The shared
  `math_resource_lra_routes` regression parses the source QF_LRA artifact and
  checks the `UnsatFarkas` evidence. Generated dashboards and the public query
  summary were refreshed for that increment.

- **Numerical-linear-algebra bad solution-box QF_LRA row landed.**
  `numerical-linear-algebra-v0` now includes a checked rejection for a
  malformed solution-box row: exact replay solves the fixed `2x2` system as
  `x = [6/5, 6/5]`, while the bad row claims the first component satisfies
  `x0 <= 1`. The validator pins the source witness, matrix, right-hand side,
  exact solution, component index, actual component, claimed bound, source
  SMT-LIB artifact, and route regression. The shared
  `math_resource_lra_routes` regression parses the source QF_LRA artifact and
  checks the `UnsatFarkas` evidence. Generated dashboards and the public query
  summary were refreshed for that increment.

- **Complex-plane bad conjugation-product imaginary QF_LRA row landed.**
  `complex-plane-transforms-v0` now includes a checked rejection for a
  malformed conjugation-product row: exact real-pair replay computes both
  `conjugate(z*w)` and `conjugate(z)*conjugate(w)` as `5 - 5i` for
  `z = 1 + 2i` and `w = 3 - i`, while the bad row claims imaginary part `5`.
  The validator pins the source witness, replayed conjugate products,
  computed imaginary part, claimed imaginary part, gap, source SMT-LIB
  artifact, regression, and independently checked `UnsatFarkas` certificate.
  The shared `math_resource_lra_routes` regression parses the shifted
  QF_LRA artifact and checks the Farkas evidence. Generated dashboards and the
  public query summary were refreshed for that increment.

- **Bounded-dynamics bad threshold-step QF_LRA row landed.**
  `bounded-dynamics-v0` now includes a checked rejection for a malformed early
  threshold-reachability row: exact replay of the plus-three trace computes
  state `6` at step `2`, below threshold `7` by shortfall `1`, while the bad
  row claims the threshold is already reached. The validator pins the source
  witness, claimed step, replayed state, threshold, shortfall, source SMT-LIB
  artifact, regression, and independently checked `UnsatFarkas` certificate.
  The shared `math_resource_lra_routes` regression parses the artifact and
  checks the Farkas evidence. Generated dashboards and the public query summary
  now report 111 concept rows, 108 non-template packs, 627 expected checks, 304
  checked rows, 252 replay-only rows, and 71 Lean-horizon rows.

- **Finite-proximal-gradient bad composite-decrease QF_LRA row landed.**
  `finite-proximal-gradient-v0` now includes a checked rejection for a
  malformed composite-decrease row: exact replay computes composite values
  `F(0)=9/2`, `F(1)=3`, and decrease `3/2`, while the bad row claims decrease
  `2`. The validator pins the source witness, replayed start/prox values,
  computed decrease, claimed decrease, source SMT-LIB artifact, regression, and
  independently checked `UnsatFarkas` certificate. The shared
  `math_resource_lra_routes` regression parses the artifact and checks the
  Farkas evidence. Generated dashboards and the public query summary now
  report 111 concept rows, 108 non-template packs, 626 expected checks, 303
  checked rows, 252 replay-only rows, and 71 Lean-horizon rows.

- **Finite-line-search bad descent-direction QF_LRA row landed.**
  `finite-line-search-v0` now includes a checked rejection for a malformed
  descent-direction row: exact replay computes directional derivative
  `2 * (-2) = -4`, while the bad row claims the same derivative is
  nonnegative. The validator pins the source witness, gradient, direction,
  computed derivative, source SMT-LIB artifact, regression, and independently
  checked `UnsatFarkas` certificate. The shared `math_resource_lra_routes`
  regression parses the artifact and checks the Farkas evidence. Generated
  dashboards and the public query summary now report 111 concept rows, 108
  non-template packs, 625 expected checks, 302 checked rows, 252 replay-only
  rows, and 71 Lean-horizon rows.

- **Finite-gradient-descent bad descent-bound QF_LRA row landed.**
  `finite-gradient-descent-v0` now includes a checked rejection for a malformed
  finite descent-bound row: exact replay computes decrease `11/4`, descent
  bound `5/2`, and descent slack `1/4`, while the bad row claims the same slack
  is nonpositive. The validator pins the source witness, replayed decrease,
  bound, slack, source SMT-LIB artifact, regression, and independently checked
  `UnsatFarkas` certificate. The shared `math_resource_lra_routes` regression
  parses the artifact and checks the Farkas evidence. Generated dashboards and
  the public query summary now report 111 concept rows, 108 non-template packs,
  624 expected checks, 301 checked rows, 252 replay-only rows, and 71
  Lean-horizon rows.

- **Finite-active-set inactive-slack QF_LRA row landed.**
  `finite-active-set-qp-v0` now includes a checked rejection for a malformed
  inactive-constraint row: exact active-face replay computes
  `inactive slack = 0 - (-1) = 1` for the lower-bound constraint `y >= 0` at
  `(1,1)`, while the bad row claims the same slack is nonpositive. The
  validator pins the source witness, inactive constraint value, bound,
  computed slack, SMT-LIB artifact, regression, and independently checked
  `UnsatFarkas` certificate. The shared `math_resource_lra_routes` regression
  parses the artifact and checks the Farkas evidence. Generated dashboards and
  the public query summary now report 111 concept rows, 108 non-template
  packs, 624 expected checks, 301 checked rows, 252 replay-only rows, and 71
  Lean-horizon rows.

- **Finite-Wolfe-line-search bad sufficient-decrease QF_LRA row landed.**
  `finite-wolfe-line-search-v0` now includes a checked rejection for a
  malformed Wolfe sufficient-decrease row: exact replay computes Armijo RHS
  `1/2`, accepted value `0`, and sufficient-decrease slack `1/2`, while the bad
  row claims that the same slack is nonpositive. The validator pins the source
  witness, replayed RHS/value/slack, SMT-LIB artifact, regression, and
  independently checked `UnsatFarkas` certificate. The shared
  `math_resource_lra_routes` regression parses the artifact and checks the
  Farkas evidence. Generated dashboards and the public query summary now report
  111 concept rows, 108 non-template packs, 624 expected checks, 301 checked
  rows, 252 replay-only rows, and 71 Lean-horizon rows.

- **Finite-SDP bad slack-entry QF_LRA row landed.**
  `finite-sdp-v0` now includes a checked rejection for a malformed dual
  slack-entry row: exact primal/dual replay computes
  `S = C - yI = [[0,0],[0,1]]`, while the bad row claims the bottom-right
  slack entry is `1/2`, leaving gap `1/2`. The validator pins the SDP source
  witness, slack-entry index, computed entry, claimed entry, gap, SMT-LIB
  artifact, regression, and independently checked `UnsatFarkas` certificate.
  The shared `math_resource_lra_routes` regression parses the artifact and
  checks the Farkas evidence. Generated dashboards and the public query summary
  now report 111 concept rows, 108 non-template packs, 621 expected checks, 298
  checked rows, 252 replay-only rows, and 71 Lean-horizon rows.

- **Finite-Euler bad terminal-error QF_LRA row landed.**
  `finite-euler-method-v0` now includes a checked pointwise terminal-error
  refutation for the quadratic-forcing Euler trace: exact replay computes
  terminal state `3/2`, exact value `9/4`, and terminal error `3/4`, while the
  bad row claims terminal error `1/2`, leaving gap `1/4`. The validator pins
  the source witness, terminal time/state/exact value, computed error, claimed
  error, gap, SMT-LIB artifact, regression, and independently checked
  `UnsatFarkas` certificate. The shared `math_resource_lra_routes` regression
  parses the artifact and checks the Farkas evidence. Generated dashboards and
  the public query summary now report 111 concept rows, 108 non-template packs,
  620 expected checks, 297 checked rows, 252 replay-only rows, and 71
  Lean-horizon rows.

- **Finite-projected-gradient bad decrease QF_LRA row landed.**
  `finite-projected-gradient-v0` now includes a checked rejection for a
  malformed projected-decrease row: exact replay computes `f(0) = 4`,
  `f(1) = 1`, and projected decrease `3`, while the bad row claims decrease
  `4`, leaving positive error `1`. The validator pins the source witness,
  computed start value, computed projected value, computed decrease, claimed
  decrease, exact error, SMT-LIB artifact, regression, and independently
  checked `UnsatFarkas` certificate. The shared `math_resource_lra_routes`
  regression parses the artifact and checks the Farkas evidence. Generated
  dashboards and the public query summary now report 111 concept rows, 108
  non-template packs, 619 expected checks, 296 checked rows, 252 replay-only
  rows, and 71 Lean-horizon rows.

- **Finite-KKT bad complementarity QF_LRA row landed.**
  `finite-kkt-v0` now includes a checked rejection for a malformed
  complementary-slackness row: exact KKT replay computes
  `lambda * (x - bound) = 2 * 0 = 0` at the boundary quadratic witness, while
  the bad row claims complementarity product `1`, leaving positive error `1`.
  The validator pins the source witness, computed constraint value, multiplier,
  computed product, claimed product, exact error, SMT-LIB artifact, regression,
  and independently checked `UnsatFarkas` certificate. The shared
  `math_resource_lra_routes` regression parses the artifact and checks the
  Farkas evidence. Generated dashboards and the public query summary now report
  111 concept rows, 108 non-template packs, 618 expected checks, 295 checked
  rows, 252 replay-only rows, and 71 Lean-horizon rows.

- **Finite-SDP bad duality-gap QF_LRA row landed.**
  `finite-sdp-v0` now includes a checked rejection for a malformed duality-gap
  row: exact primal/dual replay computes objective `1`, dual objective `1`,
  and gap `0`, while the bad row claims gap `1/2`, leaving positive gap error
  `1/2`. The validator pins the SDP source witness, computed gap, claimed gap,
  exact error, SMT-LIB artifact, regression, and independently checked
  `UnsatFarkas` certificate. The shared `math_resource_lra_routes` regression
  parses the artifact and checks the Farkas evidence. Generated dashboards and
  the public query summary now report 111 concept rows, 108 non-template packs,
  618 expected checks, 295 checked rows, 252 replay-only rows, and 71
  Lean-horizon rows.

- **Finite-separation bad convex-combination QF_LRA row landed.**
  `finite-separation-v0` now includes a checked rejection for a malformed
  convex-combination point row: exact replay keeps weights `(1/3,1/3,1/3)` on
  triangle vertices `(0,0)`, `(1,0)`, `(0,1)` and computes point
  `(1/3,1/3)`, while the bad row claims x-coordinate `1/2`, leaving error
  `1/6`. The validator pins the convex-hull source witness, computed point,
  claimed point, exact coordinate error, SMT-LIB artifact, regression, and
  independently checked `UnsatFarkas` certificate. The shared
  `math_resource_lra_routes` regression parses the artifact and checks the
  Farkas evidence. Generated dashboards and the public query summary now
  report 111 concept rows, 108 non-template packs, 618 expected checks, 295
  checked rows, 252 replay-only rows, and 71 Lean-horizon rows.

- **Finite-root-finding bad bisection-width QF_LRA row landed.**
  `finite-root-finding-v0` now includes a checked rejection for a malformed
  bisection-width row: exact replay selects interval `[1, 3/2]`, computes
  width `1/2`, and rejects the claimed width `1/3` with positive excess `1/6`.
  The validator pins the source bisection witness, selected interval, exact
  width arithmetic, SMT-LIB artifact, regression, and independently checked
  `UnsatFarkas` certificate. The shared `math_resource_lra_routes` regression
  parses the artifact and checks the Farkas evidence. Generated dashboards and
  the public query summary now report 111 concept rows, 108 non-template packs,
  618 expected checks, 295 checked rows, 252 replay-only rows, and 71
  Lean-horizon rows.

- **Finite-recurrence affine-step QF_LRA row landed.**
  `finite-recurrence-prefix-v0` now includes a checked rejection for a
  malformed affine recurrence step: exact replay computes `x_4 = 2*7 + 1 =
  15`, while the bad row claims `x_4 = 14`, leaving positive transition
  residual `1`. The validator pins the affine source witness, step index,
  recurrence arithmetic, residual, SMT-LIB artifact, regression, and
  independently checked `UnsatFarkas` certificate. The shared
  `math_resource_lra_routes` regression parses the artifact and checks the
  Farkas evidence. Generated dashboards and the public query summary now
  report 111 concept rows, 108 non-template packs, 618 expected checks, 295
  checked rows, 252 replay-only rows, and 71 Lean-horizon rows.

- **Bounded-monotone bad tail-gap QF_LRA row landed.**
  `bounded-monotone-sequence-v0` now includes a checked rejection for a
  malformed finite epsilon-tail row: exact replay computes `a_2 = 2/3`, so the
  gap to limit `1` is `1/3` and exceeds `epsilon = 1/4` by `1/12`. The
  validator pins the source witness, exact gap arithmetic, SMT-LIB artifact,
  regression, and independently checked `UnsatFarkas` certificate. The shared
  `math_resource_lra_routes` regression parses the artifact and checks the
  Farkas evidence. Generated dashboards and the public query summary now report
  111 concept rows, 108 non-template packs, 618 expected checks, 295 checked
  rows, 252 replay-only rows, and 71 Lean-horizon rows.

- **Convexity rational bad affine-threshold QF_LRA row landed.**
  `convexity-rational-v0` now includes a checked rejection for a malformed
  affine-threshold sample: exact replay computes `g(1/2) = -1/2` for
  `g(x)=3x-2`, so the claimed threshold output `1` has shortfall `3/2`. The
  validator pins the source witness, exact shortfall arithmetic, SMT-LIB
  artifact, regression, and independently checked `UnsatFarkas` certificate.
  The shared `math_resource_lra_routes` regression parses the artifact and
  checks the Farkas evidence. Generated dashboards and the public query summary
  now report 111 concept rows, 108 non-template packs, 618 expected checks, 295
  checked rows, 252 replay-only rows, and 71 Lean-horizon rows.

- **Finite-proximal-gradient box-plus-L1 QF_LRA row landed.**
  `finite-proximal-gradient-v0` now includes a box-constrained L1 proximal
  replay row: exact replay computes the ordinary trial point `3/2`, the
  unconstrained soft-threshold point `1`, clips it to the upper bound `3/4`,
  and checks the active upper multiplier `1/2` by stationarity. A new checked
  Farkas row rejects the malformed unconstrained point as a feasible boxed
  proximal point because exact replay computes box violation `1/4`. The
  validator pins the boxed witness, violation arithmetic, source SMT-LIB
  artifact, and regression; the shared `math_resource_lra_routes` regression
  parses the artifact and checks `UnsatFarkas` evidence. Generated dashboards
  and the public query summary now report 111 concept rows, 108 non-template
  packs, 618 expected checks, 295 checked rows, 252 replay-only rows, and 71
  Lean-horizon rows.

- **Finite-active-set degenerate multiplier QF_LRA row landed.**
  `finite-active-set-qp-v0` now includes a degenerate active-bound replay row:
  exact quadratic replay computes a tight `x <= 1` active constraint at the
  unconstrained minimizer `(1,0)` with zero gradient and zero active multiplier.
  A new checked Farkas row rejects the malformed positive multiplier `lambda=1`
  because exact stationarity replay produces residual `(1,0)` and stationarity
  error `1`. The validator pins the degenerate witness, claimed multiplier,
  source SMT-LIB artifact, and regression; the shared `math_resource_lra_routes`
  regression parses the artifact and checks `UnsatFarkas` evidence. Generated
  dashboards and the public query summary now report 111 concept rows, 108
  non-template packs, 609 expected checks, 287 checked rows, 251 replay-only
  rows, and 71 Lean-horizon rows.

- **Finite-Wolfe-line-search bad minimizer QF_LRA row landed.**
  `finite-wolfe-line-search-v0` now includes a second checked Farkas row:
  exact line-minimizer replay computes `alpha = 1/2` and `x = 0`, while the
  malformed source SMT-LIB artifact claims `alpha = 1` and `x = -1`. The
  validator pins the source witness, computed and claimed minimizer steps,
  computed and claimed candidate points, minimizer condition, artifact path,
  and regression; the shared `math_resource_lra_routes` regression parses the
  artifact and checks `UnsatFarkas` evidence. Generated dashboards and the
  public query summary now report 111 concept rows, 108 non-template packs,
  607 expected checks, 286 checked rows, 250 replay-only rows, and 71
  Lean-horizon rows.

- **Finite-line-search bad accepted-candidate QF_LRA row landed.**
  `finite-line-search-v0` now includes a second checked Farkas row: exact
  Armijo backtracking replay computes `accepted_x = 1 + (1/2)*(-2) = 0`,
  while the malformed source SMT-LIB artifact claims `accepted_x = 1/4`.
  The validator pins the source witness, start point, accepted step, descent
  direction, computed and claimed accepted points, candidate equation, artifact
  path, and regression; the shared `math_resource_lra_routes` regression parses
  the artifact and checks `UnsatFarkas` evidence. At that point, generated
  dashboards and the public query summary reported 111 concept rows, 108
  non-template packs, 606 expected checks, 285 checked rows, 250 replay-only
  rows, and 71 Lean-horizon rows.

- **Finite-gradient-descent bad step-coordinate QF_LRA row landed.**
  `finite-gradient-descent-v0` now includes a second checked Farkas row:
  exact gradient-step replay computes `next_x = 1 - (1/4)*2 = 1/2`, while the
  malformed source SMT-LIB artifact claims `next_x = 3/4`. The validator pins
  the source witness, start point, step size, gradient, computed next point,
  coordinate equation, artifact path, and regression; the shared
  `math_resource_lra_routes` regression parses the artifact and checks
  `UnsatFarkas` evidence. At that point, generated dashboards and the public
  query summary reported 111 concept rows, 108 non-template packs, 605 expected
  checks, 284 checked rows, 250 replay-only rows, and 71 Lean-horizon rows.

- **Least-squares bad RSS-improvement QF_LRA row landed.**
  `least-squares-regression-v0` now includes a second checked Farkas row:
  exact mean-baseline replay computes baseline RSS `14/3`, model RSS `1/6`,
  and improvement `9/2`, while the malformed source SMT-LIB artifact claims
  improvement `4`. The validator pins the source witness, response, mean,
  replayed RSS values, computed and claimed improvements, artifact path, and
  regression; the shared `math_resource_lra_routes` regression parses the
  artifact and checks `UnsatFarkas` evidence. Generated dashboards and the
  public query summary now report 111 concept rows, 108 non-template packs,
  604 expected checks, 283 checked rows, 250 replay-only rows, and 71
  Lean-horizon rows.

- **Finite-operator bad Chebyshev-prefix QF_LRA row landed.**
  `finite-operator-v0` now includes a third checked Farkas row: exact
  Chebyshev recurrence replay at `x=1/2` computes `T3=-1`, while the
  malformed source SMT-LIB artifact claims the shifted value `T3+1=1/2`.
  The validator pins the source witness, finite prefix, target index, actual
  and claimed values, recurrence text, artifact path, and regression; the
  shared `math_resource_lra_routes` regression parses the artifact and checks
  `UnsatFarkas` evidence. Generated dashboards and the public query summary
  now report 111 concept rows, 108 non-template packs, 603 expected checks,
  282 checked rows, 250 replay-only rows, and 71 Lean-horizon rows.

- **Finite random-matrix bad expected-rank QF_LRA row landed.**
  `random-matrix-finite-v0` now includes a second checked Farkas row: exact
  rank replay computes ranks `0`, `1`, and `2` with probability `1/3` each,
  so `E[rank]=1`, while the malformed source SMT-LIB artifact claims
  `E[rank]=2`. The validator pins the rank-mixture source witness, atom
  matrices, rank-probability table, actual and claimed expected ranks,
  artifact path, and regression; the shared `math_resource_lra_routes`
  regression parses the artifact and checks `UnsatFarkas` evidence. Generated
  dashboards and the public query summary now report 111 concept rows, 108
  non-template packs, 602 expected checks, 281 checked rows, 250 replay-only
  rows, and 71 Lean-horizon rows. Validated with the full
  `math_resource_lra_routes` regression, foundational pack/concept/negative
  fixture/consumer checks, and link/diff hygiene.

- **Finite-conditional-expectation bad total-expectation QF_LRA row landed.**
  `finite-conditional-expectation-v0` now includes a third checked Farkas row:
  exact finite partition replay computes `E[X]=7/2` and
  `E[E[X|G]]=7/2`, while the malformed source SMT-LIB artifact claims
  `E[E[X|G]]=4` under the finite law-of-total-expectation equality. The
  validator pins the source witness, atom table, partition, conditional
  expectation table, replayed expectation values, claimed value, artifact path,
  and regression; the shared `math_resource_lra_routes` regression parses the
  artifact and checks `UnsatFarkas` evidence. Generated dashboards and the
  public query summary now report 111 concept rows, 108 non-template packs,
  601 expected checks, 280 checked rows, 250 replay-only rows, and 71
  Lean-horizon rows.

- **Finite-probability bad independence QF_LRA row landed.**
  `finite-probability-v0` now includes a replayed finite independence witness
  and a checked bad-independence row: exact atom-table replay computes
  `P(heads)=1/2`, `P(red)=1/2`, and `P(heads and red)=1/4`, then rejects the
  malformed claim `P(heads and red)=1/3` under the finite independence
  equation through a source SMT-LIB artifact on the shared QF_LRA/Farkas route.
  The validator pins the atom table, events, replayed marginals, actual/product
  joint masses, claimed joint mass, artifact path, and regression; the shared
  `math_resource_lra_routes` regression parses the artifact and checks
  `UnsatFarkas` evidence. Generated dashboards and the public query summary
  now report 111 concept rows, 108 non-template packs, 600 expected checks,
  279 checked rows, 250 replay-only rows, and 71 Lean-horizon rows.

- **Finite measure monotonicity bad union-subadditivity QF_LRA row landed.**
  `finite-measure-monotonicity-v0` now includes a checked bad
  union-subadditivity row: exact inclusion-exclusion replay computes
  `mu(A union B)=1` and `mu(A)+mu(B)=4/3` for `A={a,b}` and `B={b,c}`, then
  rejects the malformed claim `mu(A union B)=3/2` under the finite
  subadditivity obligation through a source SMT-LIB artifact on the shared
  QF_LRA/Farkas route. The validator pins the source witness, claimed and
  computed union/left/right/bound measures, artifact path, and regression; the
  shared `math_resource_lra_routes` regression parses the artifact and checks
  `UnsatFarkas` evidence. Generated dashboards and the public query summary
  now report 111 concept rows, 108 non-template packs, 598 expected checks,
  278 checked rows, 249 replay-only rows, and 71 Lean-horizon rows.

- **Finite martingales bad stopped-expectation QF_LRA row landed.**
  `finite-martingales-v0` now includes a checked bad stopped-expectation row:
  exact bounded stopping replay computes `E[M_tau] = 0` for stopped values
  `1, 1, 0, -2`, then rejects the malformed claim `E[M_tau] = 1/2` through a
  source SMT-LIB artifact on the shared QF_LRA/Farkas route. The validator
  pins the atom table, full filtration, process values, stopping time,
  stopped values, actual and claimed stopped expectation, artifact path, and
  regression; the shared `math_resource_lra_routes` regression parses the
  artifact and checks `UnsatFarkas` evidence. Generated dashboards and the
  public query summary now report 111 concept rows, 108 non-template packs,
  597 expected checks, 277 checked rows, 249 replay-only rows, and 71
  Lean-horizon rows.

- **Finite hitting-times bad survival-mass QF_LRA row landed.**
  `finite-hitting-times-v0` now includes a checked bad survival-mass row:
  exact first-hit replay through horizon 4 computes `P(T > 4) = 5/16`, then
  rejects the malformed claim `P(T > 4) = 1/4` through a source SMT-LIB
  artifact on the shared QF_LRA/Farkas route. The validator pins the
  transition matrix, target set, first-hit probabilities, horizon, actual and
  claimed survival mass, artifact path, and regression; the shared
  `math_resource_lra_routes` regression parses the artifact and checks
  `UnsatFarkas` evidence. Generated dashboards and the public query summary
  now report 111 concept rows, 108 non-template packs, 596 expected checks,
  276 checked rows, 249 replay-only rows, and 71 Lean-horizon rows.

- **Finite stochastic-kernel composition QF_LRA row landed.**
  `finite-stochastic-kernels-v0` now includes a checked
  `qf-lra-bad-kernel-composition` row: exact kernel-composition replay computes
  `(K;L)(rainy, early) = 22/75`, then the QF_LRA/Farkas artifact rejects the
  fixed malformed claim `(K;L)(rainy, early) = 1/3`. The validator pins both
  component kernels, the recomputed composed kernel, the bad source/target
  entry, artifact path, and regression; the shared `math_resource_lra_routes`
  regression parses the artifact and checks `UnsatFarkas` evidence. Generated
  dashboards and the public query summary now report 111 concept rows,
  108 non-template packs, 595 expected checks, 275 checked rows, 249
  replay-only rows, and 71 Lean-horizon rows.

- **Finite concentration bad union-bound QF_LRA row landed.**
  `finite-concentration-v0` now includes a checked bad union-bound row: exact
  atom-table replay computes `P(A union B) = 3/4` for events with
  `P(A)=P(B)=1/2`, then rejects the malformed claim `P(A union B) <= 1/2`
  through a source SMT-LIB artifact on the shared QF_LRA/Farkas route. The
  validator pins the atom table, event probabilities, actual union
  probability, valid union bound, artifact path, and regression; the shared
  `math_resource_lra_routes` regression parses the artifact and checks
  `UnsatFarkas` evidence. Generated dashboards and the public query summary
  now report 111 concept rows, 108 non-template packs, 594 expected checks,
  274 checked rows, 249 replay-only rows, and 71 Lean-horizon rows.

- **Finite Markov-chain stationary QF_LRA row landed.**
  `finite-markov-chain-v0` now includes a checked bad stationary-distribution
  row: exact replay computes `[1/2,1/2] * P = [3/8,5/8]` for the fixed
  two-state chain, then rejects the malformed stationary claim that the first
  next-coordinate is `1/2` through a source SMT-LIB artifact on the shared
  QF_LRA/Farkas route. The validator pins the transition matrix, claimed
  distribution, computed next distribution, mismatch coordinate, artifact
  path, and regression; the shared `math_resource_lra_routes` regression
  parses the artifact and checks `UnsatFarkas` evidence. Generated dashboards
  and the public query summary now report 111 concept rows, 108 non-template
  packs, 593 expected checks, 273 checked rows, 249 replay-only rows, and 71
  Lean-horizon rows.

- **Numerical-linear-algebra Jacobi QF_LRA row landed.**
  `numerical-linear-algebra-v0` now includes a checked bad Jacobi first-step
  error-bound row: exact replay recomputes the fixed Jacobi update
  `[1/4, 2/3]`, exact solution `[1/11, 7/11]`, and
  `||x1 - x*||_inf = 7/44`, then rejects the malformed claim
  `||x1 - x*||_inf <= 1/8` through a source SMT-LIB artifact on the shared
  QF_LRA/Farkas route. The validator pins the matrix, right-hand side,
  initial iterate, first step, exact solution, actual/claimed error bounds,
  artifact path, and regression; the shared `math_resource_lra_routes`
  regression parses the artifact and checks `UnsatFarkas` evidence. Generated
  dashboards and the public query summary now report 111 concept rows,
  108 non-template packs, 593 expected checks, 273 checked rows, 249
  replay-only rows, and 71 Lean-horizon rows.

- **Exact-statistical-tests multinomial QF_LRA row landed.**
  `exact-statistical-tests-v0` now includes a probability-ordered exact
  multinomial test for `n = 3`, uniform three-category probabilities, and
  observed counts `[3,0,0]`: finite enumeration includes exactly `[3,0,0]`,
  `[0,3,0]`, and `[0,0,3]`, giving `3 * (1/27) = 1/9`, then a source SMT-LIB
  artifact rejects the malformed claim `p = 1/6` through the final linear
  equation `9*p = 1`. The validator pins the category probabilities,
  observed counts, included count vectors, actual/claimed p-values, artifact
  path, and regression; the shared `math_resource_lra_routes` regression parses
  the artifact and checks `UnsatFarkas` evidence. Generated dashboards and the
  public query summary now report 111 concept rows, 108 non-template packs,
  591 expected checks, 271 checked rows, 249 replay-only rows, and 71
  Lean-horizon rows.

- **Exact-statistical-tests two-sided Fisher QF_LRA row landed.**
  `exact-statistical-tests-v0` now covers the probability-ordered two-sided
  Fisher convention for the fixed `2x2` table: finite replay includes top-left
  counts `0`, `1`, `3`, and `4`, giving `(1 + 16 + 16 + 1) / 70 = 17/35`,
  then a source SMT-LIB artifact rejects the malformed claim `p = 1/2` through
  the final linear equation `35*p = 17`. The validator pins the explicit
  two-sided convention, included top-left counts, actual/claimed p-values,
  artifact path, and regression; the shared `math_resource_lra_routes`
  regression parses the artifact and checks `UnsatFarkas` evidence. Generated
  dashboards and the public query summary now report 111 concept rows, 108
  non-template packs, 591 expected checks, 271 checked rows, 249 replay-only
  rows, and 71 Lean-horizon rows.

- **Exact-statistical-tests bad Fisher QF_LRA row landed.**
  `exact-statistical-tests-v0` now has a checked Farkas row for a malformed
  one-sided Fisher exact-test claim: finite fixed-margin replay computes the
  left tail as `(1 + 16) / 70 = 17/70`, then the source SMT-LIB artifact
  rejects the incompatible claim `p = 1/4` through the final linear equation
  `70*p = 17`. The shared `math_resource_lra_routes` regression parses the
  artifact and checks `UnsatFarkas` evidence, while the validator pins the
  `2x2` table, margins, observed top-left count, numerator/denominator,
  actual/claimed p-values, artifact path, and regression. Generated dashboards
  and the public query summary now report 111 concept rows, 108 non-template
  packs, 591 expected checks, 271 checked rows, 249 replay-only rows, and 71
  Lean-horizon rows.

- **Descriptive-statistics bad variance QF_LRA row landed.**
  `descriptive-statistics-v0` gained a checked Farkas row for exact finite
  statistics: replay computes the sample mean `5/2`, second moment `15/2`,
  `mean^2 = 25/4`, and population variance `5/4`, then rejects the malformed
  claim `Var(X) = 3/2`. The source SMT-LIB artifact keeps the nonlinear square
  out of the trusted solver step by checking only the final linear equation
  `population_variance + mean_square = second_moment`, the shared
  `math_resource_lra_routes` regression parses it and checks `UnsatFarkas`
  evidence, and the validator pins the sample, moments, actual/claimed
  variance, artifact path, and regression. A later split makes the proof row
  explicit as `qf-lra-bad-variance`. Generated dashboards and the public
  query summary now report 111 concept rows, 108 non-template packs, 591
  expected checks, 271 checked rows, 249 replay-only rows, and 71 Lean-horizon
  rows.

- **Finite-probability bad conditional-probability QF_LRA row landed.**
  `finite-probability-v0` now has a third checked Farkas row: exact atom-table
  replay computes `P(rain)=3/10`, `P(late and rain)=1/10`, and therefore
  `P(late | rain)=1/3`, then rejects the malformed claim `P(late | rain)=1/2`.
  The source SMT-LIB artifact uses the division-free linear equation
  `condition_probability * conditional_probability = joint_probability`, the
  shared `math_resource_lra_routes` regression parses it and checks
  `UnsatFarkas` evidence, and the validator pins the atom table, event,
  condition, joint mass, conditioning mass, actual/claimed conditional
  probabilities, artifact path, and regression. Generated dashboards and the
  public query summary now report 111 concept rows, 108 non-template packs, 591
  expected checks, 271 checked rows, 249 replay-only rows, and 71 Lean-horizon
  rows.

- **Modular-arithmetic nonunit inverse QF_BV/DRAT row landed.**
  `modular-arithmetic-v0` now has a checked fixed-width BV proof row for the
  composite nonunit inverse search: a 3-bit residue `b < 6` is zero-extended to
  6 bits, `(2*b) mod 6 = 1` is asserted, and the bit-blasted CNF refutation is
  rechecked with DRAT evidence. The row sits beside the existing finite replay
  and Diophantine gcd obstruction for `2 mod 6`, giving the same obstruction a
  width-explicit solver route. Generated dashboards and the public query
  summary now report 111 concept rows, 108 non-template packs, 591 expected
  checks, 271 checked rows, 249 replay-only rows, and 71 Lean-horizon rows.

- **Finite-conditional-expectation bad tower-property QF_LRA row landed.**
  `finite-conditional-expectation-v0` now has a second checked Farkas row:
  exact nested-partition replay computes `E[E[X|G]|H] = 7/2` on the coarse
  block, then rejects the malformed claim that the tower value is `4`. The new
  source SMT-LIB artifact isolates the final exact-linear scalar conflict, the
  shared `math_resource_lra_routes` regression parses it and checks
  `UnsatFarkas` evidence, and the validator pins the atom table, fine/coarse
  partitions, exact conditional-expectation tables, actual tower table, claimed
  tower table, artifact path, and regression. Generated dashboards and the
  public query summary now report 111 concept rows, 108 non-template packs, 591
  expected checks, 271 checked rows, 249 replay-only rows, and 71 Lean-horizon
  rows.

- **Finite-random-variable bad expectation-through-pushforward QF_LRA row landed.**
  `finite-random-variables-v0` now has a second checked Farkas row: exact
  finite random-variable replay computes `E[X] = 20` both from source atoms and
  from the pushforward distribution, then rejects the malformed claim
  `E[X] = 25`. The new source SMT-LIB artifact isolates the final exact-linear
  expectation conflict, the shared `math_resource_lra_routes` regression parses
  it and checks `UnsatFarkas` evidence, and the validator pins the atom table,
  total random-variable map, pushforward distribution, outcome values, source
  expectation, pushforward expectation, claimed expectation, artifact path,
  regression, and certificate note. Generated dashboards and the public query
  summary now report 111 concept rows, 108 non-template packs, 591 expected
  checks, 271 checked rows, 249 replay-only rows, and 71 Lean-horizon rows.

- **Comprehensive math-curriculum resource plan landed.**
  Added
  [`MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md)
  as the owner-facing plan for building all curriculum-based resource families:
  educational content, ontology/taxonomy rows, example packs, proof artifacts,
  solver feedback, rules/law transfer, consumer boundaries, and future library
  splits. The plan is grounded in the current 2026-07-01 resource baseline
  (111 concept rows, 108 non-template packs, 591 expected checks, 271 checked
  rows, 249 replay-only rows, 71 Lean-horizon rows, and 108 promoted
  solver-reuse packs) and is linked from the foundational-resource index,
  mdBook summary, buildout plan, master plan, build sequence, detailed build
  ledger, roadmap, and `PLAN.md`.

- **Finite-product-measure bad marginal QF_LRA row landed.**
  `finite-product-measure-v0` now has a second checked Farkas row: exact
  finite product-table replay sums the `heads` row as
  `1/6 + 1/6 + 1/6 = 1/2`, then rejects the malformed claim that the left
  marginal is `2/3`. The new source SMT-LIB artifact isolates the final
  exact-linear marginal conflict, the shared `math_resource_lra_routes`
  regression parses it and checks `UnsatFarkas` evidence, and the validator
  pins the factor tables, product table, target axis/atom, artifact path,
  regression, and certificate note. Generated dashboards and the public query
  summary now report 111 concept rows, 108 non-template packs, 591 expected
  checks, 271 checked rows, 249 replay-only rows, and 71 Lean-horizon rows.

- **Finite-inversion bad inverse-distance-product QF_LRA row landed.**
  `finite-inversion-geometry-v0` now has a second checked Farkas row: exact
  unit-circle inversion replay computes `|p|^2 = 5`, `|I(p)|^2 = 1/5`, and
  squared-radius product `1` for `p = (2,1)`, then rejects the malformed claim
  that the product is `2`. The new source SMT-LIB artifact isolates the final
  exact-linear scalar conflict, the shared `math_resource_lra_routes`
  regression parses it and checks `UnsatFarkas` evidence, and the validator
  pins the point, inverse point, radius squares, artifact path, regression, and
  certificate note. Generated dashboards and the public query summary now
  report 111 concept rows, 108 non-template packs, 580 expected checks, 262
  checked rows, 247 replay-only rows, and 71 Lean-horizon rows.

- **Coordinate-geometry bad midpoint-coordinate QF_LRA row landed.**
  `coordinate-geometry-v0` now has a second checked Farkas row: exact midpoint
  replay computes midpoint `(2,1)` for the segment `(0,0)` to `(4,2)`, then
  rejects the malformed claim that the midpoint x-coordinate is `3`. The new
  source SMT-LIB artifact isolates the final exact-linear coordinate conflict,
  the shared `math_resource_lra_routes` regression parses it and checks
  `UnsatFarkas` evidence, and the validator pins the segment endpoints,
  computed midpoint, claimed coordinate, artifact path, regression, and
  certificate note. Generated dashboards and the public query summary now
  report 111 concept rows, 108 non-template packs, 579 expected checks, 261
  checked rows, 247 replay-only rows, and 71 Lean-horizon rows.

- **Rigid-configuration bad translation-image QF_LRA row landed.**
  `rigid-configuration-geometry-v0` now has a second checked Farkas row: exact
  translation replay computes `(3,0) + (1,-2) = (4,-2)`, then rejects the
  malformed claim that the translated x-coordinate is `5`. The new source
  SMT-LIB artifact isolates the final exact-linear coordinate conflict, the
  shared `math_resource_lra_routes` regression parses it and checks
  `UnsatFarkas` evidence, and the validator pins the source point, translation
  vector, computed target, claimed coordinate, artifact path, regression, and
  certificate note. This advanced the generated dashboard and public
  query-summary counters by one checked row.

- **Incidence-geometry bad intersection-coordinate QF_LRA row landed.**
  `incidence-geometry-v0` now has a second checked Farkas row: exact
  line-intersection replay checks `(2,1)` for `x + y - 3 = 0` and
  `x - y - 1 = 0`, then rejects the malformed claim that the intersection
  x-coordinate is `3`. The new source SMT-LIB artifact isolates the final
  exact-linear coordinate conflict, the shared `math_resource_lra_routes`
  regression parses it and checks `UnsatFarkas` evidence, and the validator
  pins both lines, determinant, computed intersection, claimed coordinate,
  artifact path, regression, and certificate note. This advanced the generated
  dashboard and public query-summary counters by one checked row.

- **Affine-geometry bad midpoint-coordinate QF_LRA row landed.**
  `affine-geometry-v0` now has a second checked Farkas row: exact affine replay
  computes midpoint `M = (2,1)` for the segment `(0,0)` to `(4,2)` and
  `T(M) = (6,4)`, then rejects the malformed claim that the image
  y-coordinate is `5`. The new source SMT-LIB artifact isolates the final
  exact-linear coordinate conflict, the shared `math_resource_lra_routes`
  regression parses it and checks `UnsatFarkas` evidence, and the validator
  pins the map, segment, midpoint, replayed image, claimed coordinate,
  artifact path, regression, and certificate note. This advanced the generated
  dashboard and public query-summary counters by one checked row.

- **Affine-geometry bad collinearity-determinant QF_LRA row landed.**
  `affine-geometry-v0` now has a third checked Farkas row: exact affine replay
  sends the collinear triple `(0,0)`, `(1,1)`, `(3,3)` to
  `(1,-1)`, `(4,3)`, `(10,11)` and computes transformed collinearity
  determinant `0`, then rejects the malformed claim that the determinant is
  `1`. The source SMT-LIB artifact isolates that final exact-linear conflict,
  the shared `math_resource_lra_routes` regression checks `UnsatFarkas`
  evidence, and the validator pins the map, determinant, source/image triples,
  artifact path, regression, and certificate note.

- **Finite quotient-topology representative QF_UF/Alethe row landed.**
  `finite-quotient-topology-v0` now has a second checked Alethe row: exact
  quotient-map replay computes `q(a)=q(b)=p` for representatives `a` and `b`
  in the same fiber, then rejects the malformed claim that their quotient
  images are distinct. The source SMT-LIB artifact isolates that equality
  conflict, the shared `math_resource_uf_routes` regression checks
  `UnsatAletheProof` evidence through `Evidence::check`, and the validator
  pins the source topology, quotient map, common fiber, artifact path,
  regression, and certificate note.

- **Complex-algebraic bad product-coordinate QF_LRA row landed.**
  `complex-algebraic-v0` now has a second checked Farkas row: exact real-pair
  replay computes `(1 + 2i) * (3 - i) = 5 + 5i`, then rejects the malformed
  claim that the product real part is `4`. The new source SMT-LIB artifact
  isolates the final exact-linear real-part conflict, the shared
  `math_resource_lra_routes` regression parses it and checks `UnsatFarkas`
  evidence, and the validator pins the source operands, computed product,
  claimed real part, artifact path, regression, and certificate note. This
  advanced the generated dashboard and public query-summary counters by one
  checked row.

- **Orientation/area bad affine-area-scaling QF_LRA row landed.**
  `orientation-area-geometry-v0` now has a second checked Farkas row: exact
  affine replay computes source signed double area `12`, determinant `5`, and
  image signed double area `60`, then rejects the malformed claim that the
  image signed double area is still `12`. The new source SMT-LIB artifact
  isolates the final exact-linear area-preservation conflict, the shared
  `math_resource_lra_routes` regression parses it and checks `UnsatFarkas`
  evidence, and the validator pins the matrix, translation, source/image
  points, determinant, signed-area values, claimed image area, artifact path,
  regression, and certificate note. This advanced the generated dashboard and
  public query-summary counters by one checked row.

- **Finite-Euler bad max-error QF_LRA row landed.**
  `finite-euler-method-v0` now has a second checked Farkas row: exact finite
  error-table replay computes maximum error `3/4` for the quadratic-forcing
  Euler trace, then rejects the malformed claim `max_error <= 1/2`. The new
  source SMT-LIB artifact isolates the final exact-linear error-bound
  contradiction, the shared `math_resource_lra_routes` regression parses it and
  checks `UnsatFarkas` evidence, and the validator pins the Euler table,
  exact-solution values, absolute errors, computed max error, claimed bound,
  artifact path, regression, and certificate note. This advanced the generated
  dashboard and public query-summary counters by one checked row.

- **Bounded-dynamics bad transition-step QF_LRA row landed.**
  `bounded-dynamics-v0` now has a second checked Farkas row: exact recurrence
  replay computes the plus-two transition after state `2` as `4`, then rejects
  the malformed claim that the same next state is `5`. The new source SMT-LIB
  artifact isolates the local transition equality conflict, the shared
  `math_resource_lra_routes` regression parses it and checks `UnsatFarkas`
  evidence, and the validator pins the trace, step index, previous state,
  computed next state, claimed next state, artifact path, regression, and
  certificate note. This advanced the generated dashboard and public
  query-summary counters by one checked row.

- **Matrix-invariants bad trace QF_LRA row landed.**
  `matrix-invariants-v0` now has a second checked Farkas row: exact replay
  computes `trace([[2,1],[1,2]]) = 4`, then rejects the malformed claim that
  the same trace is `5`. The new source SMT-LIB artifact isolates the final
  equality conflict, the shared `math_resource_lra_routes` regression parses it
  and checks `UnsatFarkas` evidence, and the validator pins the matrix, computed
  trace, claimed trace, artifact path, regression, and certificate note. This
  advanced the generated dashboard and public query-summary counters by one
  checked row.

- **Linear algebra bad LU product-entry QF_LRA row landed.**
  `linear-algebra-rational-v0` now has a second checked Farkas row: exact
  replay multiplies `L=[[1,0],[2,1]]` and `U=[[2,1],[0,1]]`, computes
  `(L*U)[1,1] = 3`, and rejects the malformed claim that the same product
  entry is `4`. The new source SMT-LIB artifact isolates the final equality
  conflict, the shared `math_resource_lra_routes` regression parses it and
  checks `UnsatFarkas` evidence, and the validator pins the matrices, selected
  entry, computed/claimed values, artifact path, regression, and certificate
  note. This advanced the generated dashboard and public query-summary counters
  by one checked row.

- **Spectral bad Rayleigh-quotient QF_LRA row landed.**
  `spectral-linear-algebra-v0` now has a second checked Farkas row: exact
  replay computes `v^T*A*v = 6`, `v^T*v = 2`, and Rayleigh quotient `3` for
  `[1,1]` under `[[2,1],[1,2]]`, then rejects the malformed claim that the
  quotient is `4`. The new source SMT-LIB artifact isolates the final equality
  conflict, the shared `math_resource_lra_routes` regression parses it and
  checks `UnsatFarkas` evidence, and the validator pins the matrix, vector,
  numerator, denominator, computed quotient, artifact path, regression, and
  certificate note. Generated dashboards and the public query summary now
  report 111 concept rows, 108 non-template packs, 569 expected checks, 251
  checked rows, 247 replay-only rows, and 71 Lean-horizon rows.

- **Inner-product bad projection-orthogonality QF_LRA row landed.**
  `inner-product-spaces-rational-v0` now has a second checked Farkas row:
  finite replay reuses the projection of `[2,3]` onto `span([1,1])`,
  computes residual `[-1/2,1/2]` and `<residual,[1,1]> = 0`, then rejects
  the malformed claim that the same inner product is `1`. The new source
  SMT-LIB artifact isolates the final equality conflict, the shared
  `math_resource_lra_routes` regression parses it and checks `UnsatFarkas`
  evidence, and the validator pins the projection witness, residual inner
  product, artifact path, regression, and certificate note. Generated
  dashboards and the public query summary now report 111 concept rows, 108
  non-template packs, 568 expected checks, 250 checked rows, 247 replay-only
  rows, and 71 Lean-horizon rows.

- **Finite-operator bad `l1` norm QF_LRA row landed.**
  `finite-operator-v0` now has a second checked Farkas row: finite replay
  reuses the `l1` triangle witness with `u=(1,2)`, `v=(3,-1)`, and
  `u+v=(4,1)`, computes `||u+v||_1 = 5`, and rejects the malformed claim
  `||u+v||_1 <= 4`. The new source SMT-LIB artifact isolates the final exact
  inequality conflict, the shared `math_resource_lra_routes` regression parses
  it and checks `UnsatFarkas` evidence, and the validator pins the vectors,
  replayed norms, true triangle bound, artifact path, regression, and
  certificate note. The operator pack docs, learner pages, proof frontier,
  field matrix, and buildout ledgers now reference both checked finite-operator
  rows. Generated dashboards and the public query summary now report 111
  concept rows, 108 non-template packs, 567 expected checks, 249 checked rows,
  247 replay-only rows, and 71 Lean-horizon rows.

- **Finite cyclic-geometry bad Ptolemy QF_LRA row landed.**
  `finite-cyclic-geometry-v0` now has a rational Ptolemy replay witness and a
  third checked Farkas row: finite replay checks the origin-centered `4 x 3`
  rectangle, side lengths `4,3,4,3`, diagonal lengths `5,5`, and Ptolemy
  equality `5*5 = 4*4 + 3*3 = 25`, while the malformed row claims the replayed
  right-hand side is `24`. The new source SMT-LIB artifact isolates the final
  exact equality conflict, the shared `math_resource_lra_routes` regression
  parses it and checks `UnsatFarkas` evidence, and the validator pins the
  cyclic rectangle, side/diagonal lengths, product terms, artifact path,
  regression, and certificate note. The cyclic pack docs, learner pages, proof
  frontier, field matrix, and buildout ledgers now reference all three checked
  cyclic-geometry rows. Generated dashboards and the public query summary now
  report 111 concept rows, 108 non-template packs, 566 expected checks, 248
  checked rows, 247 replay-only rows, and 71 Lean-horizon rows.

- **Finite circle-geometry bad line-intersection QF_LRA row landed.**
  `finite-circle-geometry-v0` now has a second checked Farkas row plus a new
  replay witness: finite circle-line replay checks the horizontal diameter
  `y=0`, endpoints `(-1,0)` and `(1,0)`, midpoint `(0,0)`, and the right
  intersection `(1,0)`, while the malformed row claims right-intersection
  x-coordinate `2`. The new source SMT-LIB artifact isolates the final exact
  equality conflict, the shared `math_resource_lra_routes` regression parses it
  and checks `UnsatFarkas` evidence, and the validator pins the line equation,
  endpoint radii, line values, midpoint, chord direction, computed/claimed
  intersection coordinates, artifact path, regression, and certificate note.
  The circle pack docs, learner pages, proof frontier, field matrix, and
  buildout ledgers now reference both checked circle-geometry rows. Generated
  dashboards and the public query summary now report 111 concept rows, 108
  non-template packs, 564 expected checks, 247 checked rows, 246 replay-only
  rows, and 71 Lean-horizon rows.

- **Finite cyclic-geometry bad opposite-angle QF_LRA row landed.**
  `finite-cyclic-geometry-v0` now has a second checked Farkas row in addition
  to the bad diagonal-intersection conflict: finite cyclic replay computes the
  angle dot product at `B` in the square as `0`, while the malformed row claims
  `1`. The new source SMT-LIB artifact isolates the exact equality conflict,
  the shared `math_resource_lra_routes` regression parses it and checks
  `UnsatFarkas` evidence, and the validator pins the replayed angle vectors,
  computed/claimed dot products, artifact path, regression, and certificate
  note. The cyclic pack docs, learner pages, proof frontier, field matrix, and
  buildout ledgers now reference both checked cyclic-geometry rows. Generated
  dashboards and the public query summary now report 111 concept rows, 108
  non-template packs, 562 expected checks, 246 checked rows, 245 replay-only
  rows, and 71 Lean-horizon rows.

- **Finite-Chebyshev alternation QF_LRA row landed.**
  `finite-chebyshev-systems-v0` now has a third checked Farkas row:
  finite replay recomputes the alternating residual table
  `1/2, -1/2, 1/2` for `r(x)=x^2-1/2`, while the malformed row claims common
  uniform error `2/3`. The new SMT-LIB artifact isolates the final exact
  conflict `uniform_error = 1/2` and `uniform_error = 2/3`; the shared
  `math_resource_lra_routes` regression parses it and checks `UnsatFarkas`
  evidence; and the validator pins the residual polynomial, values, signs,
  actual/claimed uniform errors, artifact path, regression, and certificate
  note. The Chebyshev pack docs, learner pages, operator index, proof frontier,
  field matrix, and buildout ledgers now reference the row. Generated
  dashboards and the public query summary now report 111 concept rows, 108
  non-template packs, 561 expected checks, 245 checked rows, 245 replay-only
  rows, and 71 Lean-horizon rows.

- **Modular Fermat-unit QF_BV/DRAT row landed.**
  `modular-arithmetic-v0` now has a checked fixed-width residue proof route
  for the Fermat-style modulo-5 search. The finite replay row still enumerates
  units directly; the new solver-facing row encodes a 3-bit residue
  `0 < a < 5`, computes `a^4` at 9-bit width so `4^4 = 256` is exact, asserts
  `a^4 mod 5 != 1`, and checks the resulting QF_BV contradiction through
  DIMACS/DRAT evidence. The pack validator pins the modulus, exponent, unit
  residues, bit widths, SMT-LIB artifact, regression, and certificate note.
  Modular arithmetic, number-systems, proof-frontier, field matrix, and
  buildout ledgers now reference the row. Generated dashboards and the public
  query summary now report 111 concept rows, 108 non-template packs, 560
  expected checks, 244 checked rows, 245 replay-only rows, and 71 Lean-horizon
  rows.

- **Finite-Chebyshev bad interpolation-sample QF_LRA row landed.**
  `finite-chebyshev-systems-v0` now has a second checked Farkas row:
  finite replay recomputes `p(1)=4` for `p(x)=2 - x + 3*x^2`, while the
  malformed row claims `p(1)=5`. The new SMT-LIB artifact isolates the final
  exact sample-value conflict, the shared `math_resource_lra_routes`
  regression parses it and checks `UnsatFarkas` evidence, and the validator
  pins the coefficients, evaluation row, actual/claimed values, artifact path,
  regression, and certificate note. The Chebyshev learner pages, operator
  index, proof frontier, field matrix, and buildout ledgers now reference the
  row. Generated dashboards and the public query summary now report 111
  concept rows, 108 non-template packs, 559 expected checks, 243 checked rows,
  245 replay-only rows, and 71 Lean-horizon rows.

- **Modular incompatible-CRT Diophantine QF_LIA row landed.**
  `modular-arithmetic-v0` now has a second checked solver-form arithmetic
  obstruction: the false CRT pair `x == 1 mod 4` and `x == 2 mod 6` reduces to
  `4*a - 6*b = 1`, but `gcd(4,6)=2` does not divide `1`. The new SMT-LIB
  artifact is checked by `math_resource_lia_routes` through
  `UnsatDiophantine` evidence, the validator pins the congruences, gcd,
  artifact path, regression, and certificate note, and the modular arithmetic,
  Diophantine anatomy, algebra/number-theory, number-systems, proof-frontier,
  and curriculum buildout docs now reference the row. Generated dashboards and
  the public query summary now report 111 concept rows, 108 non-template packs,
  558 expected checks, 242 checked rows, 245 replay-only rows, and 71
  Lean-horizon rows.

- **Bounded number-theory Diophantine QF_LIA row landed.**
  `number-theory-v0` now has a checked unsat counterpart to the existing
  `14*x + 21*y = 7` witness: the new row encodes `14*x + 21*y = 5`, records
  `gcd(14,21)=7`, and rejects the claim because `7` does not divide `5`.
  The new SMT-LIB artifact is checked by `math_resource_lia_routes` through
  `UnsatDiophantine` evidence, the validator pins the coefficients, gcd,
  artifact path, regression, and certificate note, generated dashboards now
  show `number-theory-v0` at 10 checked rows, and the public query summary is
  111 concept rows, 108 non-template packs, 557 expected checks, 241 checked
  rows, 245 replay-only rows, and 71 Lean-horizon rows.

- **Bounded number-theory bad square-witness QF_BV row landed.**
  `number-theory-v0` now has a second fixed-width residue contradiction:
  exact replay computes `2^2 mod 7 = 4` while the malformed square-root claim
  requires `2`. The new SMT-LIB artifact is checked by
  `math_resource_bv_routes` through DIMACS/DRAT evidence, the pack validator
  enforces both the replay row and proof-route row, generated dashboards now
  show `number-theory-v0` at 9 checked rows, and the public query summary is
  111 concept rows, 108 non-template packs, 556 expected checks, 240 checked
  rows, 245 replay-only rows, and 71 Lean-horizon rows.

- **Finite-rings bad multiplicative-identity QF_BV row landed.**
  `finite-rings-v0` now has a second fixed-width ring-table contradiction:
  XOR addition, zero multiplication, and a claimed identity `1`. Finite replay
  isolates `1*1=0` while the identity law requires `1`; the new SMT-LIB
  artifact is checked by `math_resource_bv_routes` through DIMACS/DRAT
  evidence, and the pack validator, learner page, generated dashboards,
  buildout ledgers, `PLAN.md`, and public query counts advanced to
  552 expected checks and 236 checked rows.

- **Finite-fields bad inverse-candidate QF_BV row landed.**
  `finite-fields-v0` now has a second fixed-width finite-field contradiction:
  exact replay computes `3*4 mod 7 = 5` while the false inverse claim requires
  `1`. The new SMT-LIB artifact is checked by `math_resource_bv_routes`
  through DIMACS/DRAT evidence, and the pack validator, learner pages,
  generated dashboards, buildout ledgers, `PLAN.md`, and public query counts
  now reflect 554 expected checks and 238 checked rows.

- **Bad finite group-homomorphism Alethe row landed.**
  `finite-algebra-homomorphisms-v0` now has a second source-linked
  QF_UF/Alethe row: after finite table replay finds the malformed map's
  failing pair `1+1`, the new SMT-LIB artifact checks the isolated conflict
  `phi(1+1)=1` versus `phi(1)+phi(1)=0` with
  `prove_qf_uf_unsat_alethe` and `Evidence::check`. The learner page,
  consumer guide, field-readiness matrix, concept generator, and resource
  smoke now expose the row through `bridge_homomorphism_preservation`, while
  general isomorphism, quotient, categorical, and infinite-algebra theorems
  remain Lean-horizon.

- **Random-matrix moment learner index landed.**
  `random-matrix-moment-index.md` now ties finite matrix-valued atom tables,
  exact trace/determinant moments, expected Gram matrices, rank-mixture
  probabilities, checked QF_LRA/Farkas bad trace-square refutation, and
  adjacent finite probability/statistics table patterns into one learner
  path. The consumer guide, field-readiness matrix, atlas source refs, matrix
  query guide, probability/statistics pages, and resource smoke now expose
  `bridge_random_matrix_finite_moment` through concept-scoped Farkas route
  queries. The boundary stays finite: exact rational atom-table, matrix,
  expectation, Gram, and rank replay are current evidence; asymptotic spectral
  laws, universality, concentration theorems, simulation quality, and
  high-dimensional random-matrix claims remain theorem/numerical-honesty
  horizons.

- **Optimization/convexity query guide landed.**
  `OPTIMIZATION-CONVEXITY-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route and pack-specific Farkas queries for LP objectives,
  convexity shadows, projection/residual rows, exact-vs-floating boundaries,
  KKT stationarity, active-set QP, SDP, gradient-descent, Armijo/Wolfe
  line-search, projected-gradient, and proximal-gradient finite rows. The
  foundational-resource smoke check now runs those focused drills, while
  duality, KKT sufficiency, SDP strong duality, convergence, stability, and
  benchmark claims remain horizon work.

- **Functional/operator query guide landed.**
  `FUNCTIONAL-OPERATOR-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route and pack-specific queries for finite operator/Chebyshev
  rows, eigenpair/Rayleigh rows, inner-product/projection rows, and finite
  dual/tensor equality rows. The foundational-resource smoke check now runs
  those Farkas and Alethe drills, while Banach/Hilbert-space,
  compact-operator, minimax, Haar-space, alternation-theorem, stability, and
  infinite-dimensional approximation claims remain horizon work.

- **Analysis/numerical query guide landed.**
  `ANALYSIS-NUMERICAL-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route and pack-specific Farkas queries for bounded
  epsilon-delta rows, metric balls, algebraic derivative/integral rows,
  Newton/root-finding rows, finite dynamics/Euler rows,
  residual/solution-box/Jacobi rows, exact-vs-floating boundaries, and complex
  real-pair rows. The
  foundational-resource smoke check now runs those drills, while completeness,
  IVT/MVT/FTC, convergence, numerical stability, floating-point error,
  holomorphicity, contour integration, analytic continuation, and algebraic
  closure remain horizon work.

- **Foundations/discrete query guide landed.**
  `FOUNDATIONS-DISCRETE-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route and pack-specific queries for Boolean proof/CNF rows,
  refutation-as-query rows, finite proof patterns, bounded induction, finite
  quantifier expansion, finite cardinality/bijection, finite Boolean algebra,
  counting, partition/equivalence, and finite relation/function/image/preimage
  rows. The foundational-resource smoke check now runs those Boolean, Alethe,
  Diophantine, and LIA drills, while proof automation, ZFC, infinite
  sets/cardinality, unbounded induction, asymptotic enumeration, and broad
  combinatorial theorem families remain horizon work.

- **Measure-theory query guide landed.**
  `MEASURE-THEORY-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route and pack-specific Farkas queries for finite measure
  additivity, complement, monotonicity, subadditivity, product measures,
  marginals, integration, pushforwards, conditional expectation, martingales,
  stopped expectation, stochastic kernels, hitting times, and concentration
  rows. The foundational-resource smoke check now runs the focused pack drills,
  while countable additivity, Lebesgue construction, convergence theorems,
  almost-everywhere reasoning, stochastic-process limits, simulation quality,
  and floating-point claims remain horizon work.

- **Dynamics query guide landed.**
  `DYNAMICS-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route and pack-specific Farkas queries for finite recurrences,
  transition steps, invariant rows, explicit Euler rows, stochastic kernels,
  finite Markov chains, hitting-time equations, and calculus shadow
  prerequisites. The foundational-resource smoke check now runs those focused
  dynamics drills, while continuous ODE/PDE theory, flow/stability/bifurcation
  theorems, chaos/ergodic theory, Euler convergence, stochastic-process limits,
  continuous-time Markov processes, numerical stability, and floating-point
  claims remain horizon work.

- **Chebyshev/operator learner index landed.**
  `chebyshev-operator-index.md` now ties finite-dimensional operator bounds,
  Chebyshev recurrence values, Vandermonde interpolation matrices,
  alternating residuals, checked QF_LRA/Farkas bad-grid and bad-bound
  refutations, spectral rows, and characteristic-polynomial arithmetic into
  one functional-analysis/operator learner path. The consumer guide,
  field-readiness matrix, atlas source refs, matrix query guide, and resource
  smoke now expose `bridge_finite_operator_chebyshev` through concept-scoped
  Farkas route queries. The boundary stays finite: exact rational matrix,
  polynomial, norm, determinant, residual, eigenpair, and characteristic
  polynomial replay are current evidence; Banach/Hilbert-space,
  compact-operator, Haar-space, minimax, alternation-theorem, and
  infinite-dimensional approximation claims remain Lean-horizon.

- **Probability/statistics query guide landed.**
  `PROBABILITY-STATISTICS-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route queries for exact finite probability/statistics resources.
  It groups finite probability tables, measure additivity, product/integration,
  pushforwards, conditional expectation, stochastic kernels, tail counts,
  exact tests, and random-matrix moments through Farkas route checks, and
  `check-foundational-resources.sh` now smoke-checks representative
  concept-scoped probability/statistics queries. This is count-neutral and
  keeps continuous probability, asymptotic statistics, stochastic-process
  limits, simulation quality, random-matrix limit laws, and floating-point
  inference guarantees in the proof-horizon or numerical-honesty lanes.

- **Topology/homology query guide landed.**
  `TOPOLOGY-HOMOLOGY-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route queries for finite topology and finite
  homology/cohomology resources. It groups metric balls, bounded epsilon-delta
  shadows, compactness, connectedness, continuity, quotient topology,
  specialization order, boundary/homology, torsion, cohomology, UCT shadows,
  and cup products across Boolean, Farkas, Alethe, Diophantine, and QF_BV
  routes, and `check-foundational-resources.sh` now smoke-checks the compactness
  and connectedness bridge drilldowns. This is count-neutral and keeps general
  topology, invariance, exact-sequence, UCT naturality, and cohomology-ring
  theorem claims in the proof-horizon lane.

- **Algebra structure query guide landed.**
  `ALGEBRA-STRUCTURE-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route queries for finite algebra resources. It groups
  homomorphism, group-action, module-action, ideal/quotient, tensor, modular
  residue, and gcd/divisibility bridge rows across Alethe, QF_BV, and
  Diophantine routes, and `check-foundational-resources.sh` now smoke-checks
  the representative concept-scoped algebra queries. This is count-neutral and
  keeps arbitrary group/ring/module/category, classification, isomorphism, and
  infinite-algebra claims in the proof-horizon lane.

- **Number/arithmetic query guide landed.**
  `NUMBER-ARITHMETIC-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route queries for finite arithmetic resources. It groups
  gcd/divisibility, CRT, nonunit inverse, fixed-width residue, totality,
  quotient/ideal, and exact-vs-floating rows across Diophantine, QF_BV,
  Alethe, and Farkas routes, and `check-foundational-resources.sh` now
  smoke-checks representative concept-scoped arithmetic queries. This is
  count-neutral and keeps analytic number theory, algebraic number theory,
  unbounded induction, prime-distribution claims, arbitrary structure
  theorems, and floating-point guarantees in the proof-horizon or
  numerical-honesty lanes.

- **Geometry resource query guide landed.**
  `GEOMETRY-RESOURCE-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route queries for finite geometry resources. It separates
  `bridge_coordinate_orientation_geometry` (coordinate, incidence, rigid,
  affine, and orientation rows) from
  `bridge_finite_circle_inversion_cyclic_replay` (circle, inversion, and
  cyclic rows), and `check-foundational-resources.sh` now smoke-checks both
  concept-scoped Farkas pack/check paths. This is count-neutral and keeps
  synthetic, projective, differential, global, higher-degree, and numerical
  robustness geometry claims in the proof-horizon lane.

- **Graph/discrete query guide landed.**
  `GRAPH-DISCRETE-QUERIES.md` now gives downstream consumers copyable
  concept-plus-route queries for finite graph and discrete resources. It groups
  coloring, reachability, matching, cut, d-separation, fixed-width
  graph-coloring, and BFS/DFS runtime rows through
  `bridge_finite_graph_replay_obstruction`, and
  `check-foundational-resources.sh` now smoke-checks Boolean, QF_BV, and LIA
  concept-scoped graph pack/check paths. This is count-neutral and keeps
  general graph theorems, extremal/minor theory, asymptotic algorithms,
  graph-family lower bounds, and average-case traversal claims in the
  proof-horizon lane.

- **Graph traversal runtime learner index landed.**
  `graph-traversal-runtime-index.md` now ties finite reachability,
  deterministic BFS/DFS traces, shortcut-tail visited-node counters, checked
  QF_LIA bad-bound refutations, and asymptotic runtime horizons into one
  graph learner path. The graph consumer guide, field-readiness matrix, atlas
  source refs, and resource smoke now expose
  `bridge_finite_graph_replay_obstruction` through LIA route queries alongside
  the existing Boolean graph rows. The boundary stays finite: queue/stack
  replay and checked QF_LIA arithmetic evidence are current evidence; asymptotic
  BFS/DFS complexity, graph-family lower bounds, average-case traversal, and
  heuristic/parallel search guarantees remain Lean-horizon.

- **Metric-ball / epsilon-delta learner index landed.**
  `metric-ball-epsilon-delta-index.md` now ties bounded rational balls,
  finite metric continuity, sequence-tail shadows, finite compactness, finite
  connectedness, and finite continuity/open-preimage replay into one learner
  path. The generated bridge source refs and consumer smoke now make
  `bridge_metric_ball` and `bridge_bounded_epsilon_delta_shadow` discoverable
  through topology and real-analysis queries without changing the 108-pack /
  65-bridge baseline. The boundary is explicit: exact finite or bounded replay
  and checked Farkas/Boolean certificates are current evidence; quantified
  continuity, compactness, connectedness, convergence, and arbitrary-space
  theorem claims remain Lean-horizon.

- **Finite quotient-topology resource and bridge landed.**
  `finite-quotient-topology-v0` and
  `bridge_finite_quotient_topology_replay` now make quotient-map fibers,
  same-fiber equivalence pairs, quotient topology by preimage-open
  enumeration, saturated-open image replay, and checked bad representative/open
  QF_UF/Alethe evidence queryable through the public JSON boundary. The bridge
  keeps quotient topology universal properties, quotient-map theorem schemas,
  preservation/invariance theorems, and arbitrary quotient-space reasoning in
  the Lean-horizon lane. `PLAN.md`, the foundational-resource plans, learner
  pages, `CONSUMER-QUERIES.md`, `FIELD-READINESS-QUERY-MATRIX.md`,
  `PROOF-ROUTE-QUERY-MATRIX.md`, `PROOF-UPGRADE-FRONTIER.md`, and
  `check-foundational-resources.sh` now reflect the 108-pack / 65-bridge
  baseline and exercise topology quotient lookup plus concept-scoped Alethe
  route queries. Focused validation passed for the pack validator and the
  `finite_quotient_topology_bad_open_emits_checked_alethe` regression; full
  foundational-resource smoke also passes after regenerating dashboards.

- **Curriculum resource build sequence landed.** Added
  `docs/foundational-resources/MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md` as
  the practical plan for turning the math curriculum into educational content,
  ontology/bridge rows, example packs, proof artifacts, solver-feedback rows,
  rules/law transfer examples, and eventual library boundaries. The document
  records the current 111-concept / 108-pack / 554-check / 108-promoted-pack
  baseline, R0-R6 gates, staged learner/proof/solver work, field-specific next
  work for delta-epsilon balls, graph runtime pathologies, random matrices,
  LU/matrix computation, topology quotients, Chebyshev/operator rows, and
  rules/law transfer, plus a commit-sized execution queue. `PLAN.md` and the
  foundational-resource index, master plan, execution plan, detailed build
  plan, operating roadmap, and library-boundary decision now link the sequence
  and carry refreshed public-query counts where they had drifted.

- **Finite universal-coefficient shadow resource and bridge landed.**
  `finite-universal-coefficient-shadow-v0` and
  `bridge_finite_universal_coefficient_shadow` now make one dual integer
  cochain complex, `H^1 = Z/2`, degree-one Hom/Ext bookkeeping, checked bad
  `H^1 = 0` rejection, and source-linked QF_UF/Alethe evidence queryable
  through the public JSON boundary. The bridge keeps the universal coefficient
  theorem, naturality, splitting choices, Ext/Tor laws, exact sequences, and
  invariance in the Lean-horizon lane. `PLAN.md`, the foundational-resource
  plans, learner pages, `CONSUMER-QUERIES.md`,
  `FIELD-READINESS-QUERY-MATRIX.md`, `PROOF-ROUTE-QUERY-MATRIX.md`,
  `PROOF-UPGRADE-FRONTIER.md`, `MATRIX-COMPUTATION-QUERIES.md`, and
  `check-foundational-resources.sh` now reflect the 107-pack / 64-bridge
  baseline and exercise topology universal lookup plus concept-scoped Alethe
  route queries. Focused validation passed for the pack validator, concept
  validator, query helper, rustfmt, and the
  `finite_universal_coefficient_bad_h1_zero_emits_checked_alethe` regression;
  full foundational-resource smoke also passes after staging generated outputs.

- **Finite chain-complex torsion resource and bridge landed.**
  `finite-chain-complex-torsion-v0` and
  `bridge_finite_torsion_homology_replay` now make a two-term integer chain
  complex, one-entry Smith diagonal replay, `H0 = Z/2`, torsion-generator
  replay, checked bad-generator rejection, and source-linked
  QF_LIA/Diophantine evidence for `2*k = 1` queryable through the public JSON
  boundary. The bridge keeps general Smith normal form, universal coefficient
  theorems, Ext/Tor functor laws, exact sequences, and homology invariance in
  the Lean-horizon lane. `PLAN.md`, the foundational-resource plans, learner
  pages, `CONSUMER-QUERIES.md`, `FIELD-READINESS-QUERY-MATRIX.md`,
  `PROOF-ROUTE-QUERY-MATRIX.md`, `MATRIX-COMPUTATION-QUERIES.md`, and
  `check-foundational-resources.sh` reflected that increment's 106-pack / 63-bridge
  baseline and exercise topology torsion lookup plus concept-scoped
  Diophantine route queries.

- **Finite cup-product resource and bridge landed.**
  `finite-simplicial-cup-products-v0` and
  `bridge_finite_cup_product_replay` now make ordered F2 cup-product replay,
  one finite coboundary-Leibniz row, finite bad-cup-product replay, and checked
  bad cup-product QF_BV/DRAT evidence queryable through the public JSON
  boundary. The bridge keeps associativity, graded commutativity, naturality,
  cohomology-ring quotienting, universal coefficients, and invariance theorems
  in the Lean-horizon lane. `PLAN.md`, the foundational-resource plans,
  learner pages, `CONSUMER-QUERIES.md`, `FIELD-READINESS-QUERY-MATRIX.md`,
  `PROOF-ROUTE-QUERY-MATRIX.md`, and `check-foundational-resources.sh` now
  reflected the then-current 105-pack / 62-bridge baseline and exercised
  topology cup lookup plus concept-scoped QF_BV route queries.

- **Finite cohomology resource and bridge landed.**
  `finite-simplicial-cohomology-v0` and
  `bridge_finite_cohomology_replay` now make finite F2 cochain coboundary
  replay, `delta^2 = 0`, F2 cohomology-rank replay, non-coboundary cocycle
  checking, and checked bad coboundary-value QF_UF/Alethe evidence queryable
  through the public JSON boundary. The bridge keeps cohomology functoriality,
  cohomology-operation laws, universal coefficients, de Rham comparison, sheaf
  cohomology, duality, and invariance theorems in the Lean-horizon lane.
  `PLAN.md`, the
  foundational-resource plans, learner pages, `CONSUMER-QUERIES.md`,
  `FIELD-READINESS-QUERY-MATRIX.md`, `PROOF-ROUTE-QUERY-MATRIX.md`, and
  `check-foundational-resources.sh` reflected that increment's 104-pack /
  61-bridge baseline and exercised topology cohomology lookup plus
  concept-scoped Alethe route queries.

- **Finite specialization-order resource and bridge landed.**
  `finite-specialization-order-v0` and
  `bridge_finite_specialization_order_replay` now make finite topology to
  preorder replay, singleton-closure characterization, finite `T0`
  antisymmetry replay, and checked bad `T0` QF_UF/Alethe evidence queryable
  through the public JSON boundary. The bridge keeps T0 quotients, sobriety,
  Alexandroff-space/domain-theory results, and arbitrary-space
  specialization-order theorems in the Lean-horizon lane. `PLAN.md`, the
  foundational-resource plans, learner pages, `CONSUMER-QUERIES.md`,
  `FIELD-READINESS-QUERY-MATRIX.md`, `PROOF-ROUTE-QUERY-MATRIX.md`, and
  `check-foundational-resources.sh` reflected the 103-pack / 60-bridge
  baseline and exercise topology specialization lookup plus concept-scoped
  Alethe route queries.

- **Finite boundary-operator bridge concept landed.**
  `bridge_finite_boundary_operator_replay` now makes oriented boundary
  coefficients, boundary-of-boundary cancellation, boundary-matrix shape, and
  the checked QF_LIA/Diophantine bad boundary coefficient row queryable from
  one shared atlas concept. The bridge keeps functoriality, exactness,
  homology invariance, cohomology-operation laws, and general algebraic-topology
  theorem claims in the Lean-horizon lane. `CONSUMER-QUERIES.md`,
  `FIELD-READINESS-QUERY-MATRIX.md`, and `check-foundational-resources.sh`
  now exercise boundary lookup plus concept-scoped Diophantine route queries
  through the public JSON/query boundary.

- **Finite topology-operator/homeomorphism bridge concept landed.**
  `bridge_finite_topology_operator_homeomorphism` now makes finite
  topology-axiom replay, closure/interior replay, finite continuity by
  preimage, finite homeomorphism replay, checked Bool/CNF malformed-topology
  rows, and checked QF_UF/Alethe malformed-preimage rows queryable from one
  shared atlas concept. The bridge keeps Kuratowski closure axioms,
  arbitrary-space homeomorphism invariance, compactness/connectedness
  preservation, homology invariance, and general topology theorems in the
  Lean-horizon lane. `CONSUMER-QUERIES.md`,
  `FIELD-READINESS-QUERY-MATRIX.md`, and `check-foundational-resources.sh`
  now exercise closure/homeomorphism lookup plus concept-scoped Alethe route
  queries through the public JSON/query boundary.

- **Finite chain-complex/homology bridge concept landed.**
  `bridge_finite_chain_homology_replay` now makes finite
  simplicial-complex closure, oriented-boundary replay, `boundary^2 = 0`,
  Betti-rank replay, and the checked QF_LIA/Diophantine bad boundary
  coefficient row queryable from one shared atlas concept. The bridge keeps
  homology invariance, exact sequences, homotopy equivalence, cohomology
  operations, and general algebraic-topology theorem claims in the
  Lean-horizon lane.
  `CONSUMER-QUERIES.md`, `FIELD-READINESS-QUERY-MATRIX.md`, and
  `check-foundational-resources.sh` now exercise homology lookup plus
  concept-scoped Diophantine route queries through the public JSON/query
  boundary.

- **Finite circle/inversion/cyclic geometry bridge concept landed.**
  `bridge_finite_circle_inversion_cyclic_replay` now makes finite
  circle-geometry, inversion-geometry, and cyclic-geometry rows queryable from
  one shared atlas concept, with exact coordinate replay and checked
  QF_LRA/Farkas bad-radius, bad-line-intersection, bad-inverse-coordinate, and
  bad-diagonal-intersection and bad-opposite-angle rows kept separate from
  general circle, inversion, cyclic-quadrilateral, Ptolemy, and synthetic
  geometry theorems. `CONSUMER-QUERIES.md`, `FIELD-READINESS-QUERY-MATRIX.md`,
  and `check-foundational-resources.sh` now exercise circle lookup plus
  concept-scoped Farkas route queries through the public JSON/query boundary.
  Focused concept queries, pack validation, the three geometry Farkas
  regressions, link checks, and the resource consumer smoke all pass for the
  new bridge.

- **Finite dynamics/Euler bridge concept landed.**
  `bridge_finite_dynamics_euler_replay` now makes finite recurrence-prefix,
  bounded-dynamics, and explicit-Euler rows queryable from one shared atlas
  concept, with exact finite replay and checked QF_LRA/Farkas bad-value,
  bad-invariant, and bad-step rows kept separate from ODE, stability,
  convergence-rate, stiffness, chaos, and PDE claims. `CONSUMER-QUERIES.md`,
  `FIELD-READINESS-QUERY-MATRIX.md`, and
  `check-foundational-resources.sh` now exercise Euler lookup plus
  concept-scoped Farkas route queries through the public JSON/query boundary.

- **Finite graph replay bridge concept landed.**
  `bridge_finite_graph_replay_obstruction` now makes finite coloring,
  reachability/traversal, matching, cut, and d-separation rows queryable from
  one shared atlas concept, with checked Bool/CNF, QF_BV, and QF_LIA routes
  kept distinct from graph-theorem, causal, and asymptotic-runtime claims.
  `CONSUMER-QUERIES.md`, `FIELD-READINESS-QUERY-MATRIX.md`, and
  `check-foundational-resources.sh` now exercise graph reachability lookup
  plus concept-scoped Boolean route queries through the public JSON/query
  boundary.

- **Finite counting replay bridge concept landed.**
  `bridge_finite_counting_replay` now makes permutation/Pascal rows,
  pigeonhole proof routes, double-counting tables, coefficient extraction,
  finite orbit counts, and exact finite tail-count contradictions queryable
  from the foundational concept atlas. `CONSUMER-QUERIES.md`,
  `FIELD-READINESS-QUERY-MATRIX.md`, and
  `check-foundational-resources.sh` now exercise discrete-math counting lookup
  plus concept-scoped Boolean and Diophantine route queries through the public
  JSON/query boundary.

- **Modular CRT/inverse bridge concept landed.**
  `bridge_modular_crt_inverse_witness` now makes concrete CRT congruence
  witnesses, modular inverse witnesses, fixed residue searches, finite-field
  unit/nonunit contrasts, quotient-ring-adjacent vocabulary, and the checked
  nonunit Diophantine certificate queryable from the foundational concept
  atlas. `CONSUMER-QUERIES.md`,
  `FIELD-READINESS-QUERY-MATRIX.md`, and
  `check-foundational-resources.sh` now exercise number-theory CRT concept
  lookup through the public JSON/query boundary.

- **GCD/divisibility bridge concept landed.**
  `bridge_gcd_divisibility_witness` now makes gcd/common-divisor replay,
  Bezout coefficient replay, quotient witnesses, modular nonunit obstructions,
  and checked gcd non-divisibility certificates queryable from the foundational
  concept atlas. `CONSUMER-QUERIES.md` and
  `check-foundational-resources.sh` now exercise number-theory gcd concept
  lookup through the public JSON/query boundary.

- **Proof-route query matrix landed.**
  [PROOF-ROUTE-QUERY-MATRIX.md](docs/foundational-resources/PROOF-ROUTE-QUERY-MATRIX.md)
  now gives downstream consumers route-level discovery for finite replay,
  Boolean CNF/LRAT, QF_BV, QF_LIA/Diophantine, QF_LRA/Farkas,
  QF_UF/Alethe, and Lean-horizon resources. `scripts/query-foundational-resources.py`
  now has a `routes` summary command with normalized aliases and optional field
  scoping, and the foundational smoke check exercises representative route
  summaries.

- **Matrix computation concept queries landed.**
  [MATRIX-COMPUTATION-QUERIES.md](docs/foundational-resources/MATRIX-COMPUTATION-QUERIES.md)
  now gives downstream consumers copyable concept-plus-route queries for LU,
  residual bounds, rank/nullity, eigenpairs, random-matrix moments,
  tensor/module rows, finite operators, and Chebyshev systems.
  `scripts/query-foundational-resources.py` supports exact `--concept` filters
  for `packs` and `checks`, and the foundational-resource smoke check exercises
  representative matrix concept queries without adding a crate, typed API, or
  separate repo.

- **All-field readiness query matrix landed.**
  [FIELD-READINESS-QUERY-MATRIX.md](docs/foundational-resources/FIELD-READINESS-QUERY-MATRIX.md)
  now gives downstream consumers a compact 18-field map: pack/check counts,
  the smoke-checked primary route, bridge lookup terms, checked-row drilldown,
  and theorem-horizon boundary for each math field. It links from
  [CONSUMER-QUERIES.md](docs/foundational-resources/CONSUMER-QUERIES.md) and
  keeps the boundary JSON-first without introducing a crate, typed API, or
  separate repo.

- **Foundations/discrete/probability consumer queries landed.**
  [CONSUMER-QUERIES.md](docs/foundational-resources/CONSUMER-QUERIES.md)
  now shows public JSON queries for logic/proof Boolean readiness,
  proof-vocabulary lookups, checked proof-pattern/CNF rows, set-theory and
  foundations Alethe readiness, partition lookups, checked finite
  relation/function/quotient rows, discrete-math Diophantine readiness,
  finite-family lookups, checked counting/coefficient/tail-count rows,
  probability-theory Farkas readiness, probability-table lookups, and checked
  finite probability/process rows. The smoke check exercises those queries
  without promoting proof automation, ZFC/infinite set theory, asymptotic
  combinatorics, continuous probability, stochastic-process limits, or
  theorem-level probability claims.

- **Analysis/numerical/complex consumer queries landed.**
  [CONSUMER-QUERIES.md](docs/foundational-resources/CONSUMER-QUERIES.md)
  now shows public JSON queries for real-analysis Farkas readiness,
  epsilon/gradient bridge lookups, checked bounded-analysis rows,
  numerical-analysis Farkas readiness, residual/operator bridge lookups,
  checked exact numerical rows, complex-analysis Farkas readiness, real-pair
  bridge lookup, and checked algebraic complex rows. The smoke check exercises
  those queries without promoting completeness, convergence, floating-point
  stability, holomorphic, analytic-continuation, or theorem-level calculus
  claims.

- **Core algebra/number/graph consumer queries landed.**
  [CONSUMER-QUERIES.md](docs/foundational-resources/CONSUMER-QUERIES.md)
  now shows public JSON queries for abstract-algebra Alethe readiness,
  homomorphism/ideal bridge lookups, checked Alethe and fixed-width QF_BV
  finite-algebra rows, number-theory Diophantine readiness, checked
  integer-arithmetic rows, and graph-theory Boolean/CNF readiness with checked
  finite coloring, reachability, matching, cut, and d-separation rows.
  `check-foundational-resources.sh` smoke-checks those queries without
  promoting arbitrary algebraic-structure theorems, unbounded number-theory
  claims, asymptotic graph algorithms, or general graph theorems.

- **Linear-algebra consumer queries landed.**
  [CONSUMER-QUERIES.md](docs/foundational-resources/CONSUMER-QUERIES.md)
  now shows public JSON queries for linear-algebra Farkas/Alethe field
  readiness, rank/projection bridge lookups, checked exact-rational matrix
  rows, and checked equality-heavy finite vector-space, dual-space, module,
  and tensor rows. `check-foundational-resources.sh` now smoke-checks those
  queries without promoting spectral-theorem, conditioning/stability, or
  general vector-space theorem claims.

- **Statistics consumer queries landed.**
  [CONSUMER-QUERIES.md](docs/foundational-resources/CONSUMER-QUERIES.md)
  now shows public JSON queries for statistics Farkas field readiness,
  finite-table/tail-count bridge lookups, checked exact-rational statistics
  rows, and checked Diophantine count rows across exact finite tests,
  contingency tables, regression, random matrices, finite probability/process
  tables, concentration, and stochastic-kernel resources.
  `check-foundational-resources.sh` now smoke-checks those queries without
  promoting floating-point inference or asymptotic sampling claims.

- **Topology consumer queries landed.**
  [CONSUMER-QUERIES.md](docs/foundational-resources/CONSUMER-QUERIES.md)
  now shows public JSON queries for topology Boolean/Alethe/Diophantine/QF_BV field
  readiness, compactness/preimage/closure/homeomorphism/specialization/boundary/
  homology/cohomology/cup bridge lookups, concept-scoped finite
  topology-operator/homeomorphism, finite specialization-order, finite
  boundary-operator, chain-complex/homology, finite cohomology, and finite
  cup-product queries, and checked Boolean/Alethe/Diophantine/QF_BV topology rows across finite topology, compactness,
  connectedness, continuous maps, homeomorphism replay, boundary replay,
  homology, cohomology, finite cup products, metric balls, and bounded
  epsilon-delta resources.
  `check-foundational-resources.sh` now smoke-checks those queries without
  promoting arbitrary compactness, connectedness, homeomorphism,
  homology/cohomology invariance, exact sequence, cohomology-operation laws, or
  general algebraic-topology claims.

- **Functional-analysis/operator consumer queries landed.**
  [CONSUMER-QUERIES.md](docs/foundational-resources/CONSUMER-QUERIES.md)
  now shows public JSON queries for the
  `functional_analysis_and_operator_theory` Farkas field summary, the shared
  operator bridge lookup, split finite-operator replay plus checked `qf-lra-*`
  norm/bound/Chebyshev rows, and checked inner-product, Chebyshev, and spectral
  Farkas rows.
  `check-foundational-resources.sh` now
  smoke-checks those queries so this field stays visible without promoting
  Banach/Hilbert or infinite-dimensional theorem claims.

- **Rules/law generated-query dashboard landed.**
  [`rules-query-dashboard.md`](docs/rules-as-code/generated/rules-query-dashboard.md)
  was first generated from the three initial rules-as-code packs and reports 738
  bounded sample rows, 12 checked rows, 5 replayed rows, and per-pack query
  families for coverage, equivalence, threshold, cap, version-delta, and
  monotonicity checks. The generator now also writes deterministic query-row
  JSON under [`docs/rules-as-code/generated/queries/`](docs/rules-as-code/generated/queries/),
  materializing 1,374 replayed rows from those initial packs. `just rules-as-code`
  now regenerates the dashboard and query artifacts, validates them, and fails
  on generated drift.

- **Tax/benefit arithmetic rules/law pack landed.**
  [`tax-benefit-arithmetic-v0`](docs/rules-as-code/examples/tax-benefit-arithmetic-v0/README.md)
  is the third rules-as-code pack and reuses integer thresholds, household-size
  adjustments, caps, active phase-out monotonicity, effective-date witnesses,
  and bounded implementation-equivalence checks. The pack has checked
  Bool/QF_LIA fixtures for non-negative benefit, cap, active phase-out
  monotonicity, and bounded implementation equivalence; the validator replays
  the full piecewise finite sample. The focused
  `rules_as_code_examples` regression now checks the first 12 obligations with
  certified evidence across those three initial rule packs.

- **Matrix corpus/benchmark boundary note landed.**
  [`matrix-corpus-benchmark-boundary.md`](docs/learn/math/matrix-corpus-benchmark-boundary.md)
  now separates educational matrix examples, solver regressions,
  benchmark-corpus rows, and theorem-horizon claims. The atlas generator cites
  it from the matrix-adjacent bridge rows, and the learner path links it from
  the top-level math page, the matrix-computation index, and the linear algebra
  cluster. The resource baseline remains unchanged because no new pack or
  concept row was added.

- **Analysis/calculus theorem-horizon map landed.**
  [`analysis-calculus-theorem-horizon-map.md`](docs/learn/math/analysis-calculus-theorem-horizon-map.md)
  now maps real completeness, IVT/MVT/FTC, compactness/connectedness, sequence
  and recurrence convergence, root-finding convergence, optimization
  convergence/duality, measure/probability convergence,
  functional-analysis/operator theory, and dynamics from finite shadows to
  missing Lean/theorem reconstruction routes. The atlas generator now cites
  this page from analysis, topology, optimization, measure/probability,
  stochastic/dynamics, operator, and generic Lean-horizon bridge rows; the
  resource baseline remains unchanged because no new pack or concept row was
  added.

- **Matrix-computation learner index landed.**
  [`matrix-computation-index.md`](docs/learn/math/matrix-computation-index.md)
  now groups LU, rank/nullity, residual, projection, eigenpair,
  characteristic-polynomial, finite random-matrix, chain-complex, operator,
  module, and tensor rows by proof route. The atlas generator now cites this
  page from the relevant matrix bridge rows, and generated learner dashboards
  will show it as a focused matrix-resource entry without changing the 102-pack
  resource baseline.

- **Finite cyclic-geometry resource landed.**
  [`finite-cyclic-geometry-v0`](artifacts/examples/math/finite-cyclic-geometry-v0/README.md)
  and
  [`finite-cyclic-geometry-end-to-end.md`](docs/learn/math/finite-cyclic-geometry-end-to-end.md)
  now add exact cyclic quadrilateral replay to the geometry, real-analysis,
  linear-algebra, and polynomial resource paths. The pack validates cyclic
  quadrilateral replay, diagonal-intersection and diagonal-perpendicularity
  replay, opposite-angle dot-product replay, a source-linked checked
  QF_LRA/Farkas rejection for false diagonal-intersection and opposite-angle
  claims, and a cyclic-geometry Lean-horizon row. The generated resource
  summary is now 102
  promoted non-template packs, 516 checks, 222 checked rows, 229 replay-only
  rows, and 65 Lean-horizon rows.

- **Math curriculum resource master plan landed.**
  [`MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md)
  now gives the top-down build plan for expanding the 23-node curriculum and
  18-field taxonomy into resource waves, acceptance gates, field-by-field
  build priorities, proof routes, solver reuse, consumer boundaries, and the
  next commit-sized queue. At landing, this was a plan-only increment and
  preserved the then-current 101 promoted non-template math packs, 511 expected
  checks, 221 checked rows, 226 replay-only rows, and 64 Lean-horizon rows.

- **Proof-upgrade frontier planned.** The learner path sweep is mechanically
  complete for the current queue (102 focused math packs, 0 path-only links).
  The next resource layer is
  [`PROOF-UPGRADE-FRONTIER.md`](docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md):
  classify the two `needs-proof-route` packs, then upgrade CNF/LRAT,
  QF_LRA/Farkas, QF_UF/Alethe, QF_LIA/Diophantine, QF_BV bit-blast, and Lean
  horizons with explicit trust boundaries and route-specific checks.

- **Route-specific tamper/rejection tests landed.** The five active resource
  proof-certificate routes now each have a focused negative regression:
  `math_resource_boolean_routes` truncates DRAT and clears LRAT hints,
  `math_resource_bv_routes` truncates a QF_BV DRAT certificate,
  `math_resource_lra_routes` tampers a Farkas multiplier,
  `math_resource_lia_routes` tampers a Diophantine contradiction row, and
  `math_resource_uf_routes` drops the closing Alethe command. Each test requires
  the independent checker to reject the doctored certificate.

- **Optimization/convexity consumer-query coverage landed.**
  [`CONSUMER-QUERIES.md`](docs/foundational-resources/CONSUMER-QUERIES.md) now
  shows optimization/Farkas field readiness, LP-objective and convexity bridge
  lookups, and checked optimization/convexity Farkas row drill-downs. The
  foundational-resource smoke check runs the same commands so exact LP,
  convexity, finite active-set QP replay, finite SDP objective/slack, finite
  gradient-descent replay, finite line-search replay, finite Wolfe line-search
  replay, finite projected-gradient interval/decrease replay,
  finite proximal-gradient replay,
  least-squares, gradient/Hessian, residual, eigenpair, and related matrix
  examples remain visible through the public JSON boundary.

- **Finite inversion-geometry resource landed.**
  [`finite-inversion-geometry-v0`](artifacts/examples/math/finite-inversion-geometry-v0/README.md)
  and
  [`finite-inversion-geometry-end-to-end.md`](docs/learn/math/finite-inversion-geometry-end-to-end.md)
  now add exact unit-circle inversion replay to the geometry, real-analysis,
  linear-algebra, and polynomial resource paths. The pack validates inversion
  image replay, inverse-distance product replay, collinearity replay, a
  source-linked checked QF_LRA/Farkas rejection for a false inverse-coordinate
  claim, and an inversion-geometry Lean-horizon row. The generated resource
  summary at landing was 101 promoted non-template packs, 511 checks, 221 checked rows,
  226 replay-only rows, and 64 Lean-horizon rows.

- **Finite circle-geometry resource landed.**
  [`finite-circle-geometry-v0`](artifacts/examples/math/finite-circle-geometry-v0/README.md)
  and
  [`finite-circle-geometry-end-to-end.md`](docs/learn/math/finite-circle-geometry-end-to-end.md)
  now add exact circle point, tangent-line, and chord-midpoint replay to the
  geometry, real-analysis, linear-algebra, and polynomial resource paths. The
  pack validates point-on-circle replay, tangent-line/radius perpendicularity,
  chord-midpoint perpendicularity, circle-line intersection replay,
  source-linked checked QF_LRA/Farkas rejections for false radius and
  line-intersection claims, and a circle-geometry Lean-horizon row.
  The generated resource summary at landing was 100 promoted non-template packs,
  506 checks, 220 checked rows, 223 replay-only rows, and 63 Lean-horizon rows.

- **Finite active-set QP resource landed.**
  [`finite-active-set-qp-v0`](artifacts/examples/math/finite-active-set-qp-v0/README.md)
  and
  [`finite-active-set-qp-end-to-end.md`](docs/learn/math/finite-active-set-qp-end-to-end.md)
  now add exact active-face QP replay to the optimization/convexity,
  numerical-analysis, real-analysis, calculus, and linear-algebra resource
  paths. The pack validates unconstrained-minimizer replay, active-face
  candidate replay, active-set KKT replay, inactive-constraint slack replay, a
  source-linked checked QF_LRA/Farkas rejection for a false free-gradient claim,
  and an active-set-method Lean-horizon row. The generated resource summary at
  landing was 99 promoted non-template packs, 501 checks, 219 checked rows,
  220 replay-only rows, and 62 Lean-horizon rows.

- **Finite Wolfe line-search resource landed.**
  [`finite-wolfe-line-search-v0`](artifacts/examples/math/finite-wolfe-line-search-v0/README.md)
  and
  [`finite-wolfe-line-search-end-to-end.md`](docs/learn/math/finite-wolfe-line-search-end-to-end.md)
  now add exact Wolfe sufficient-decrease and curvature replay to the
  optimization/convexity, numerical-analysis, real-analysis, calculus, and
  linear-algebra resource paths. The pack validates descent-direction replay,
  exact line-minimizer replay, Wolfe sufficient-decrease replay, Wolfe
  curvature replay, a source-linked checked QF_LRA/Farkas rejection for a false
  curvature claim, and a Wolfe line-search convergence Lean-horizon row. The
  generated resource summary at landing was 98 promoted non-template packs,
  495 checks, 218 checked rows, 216 replay-only rows, and 61 Lean-horizon rows.

- **Finite proximal-gradient resource landed.**
  [`finite-proximal-gradient-v0`](artifacts/examples/math/finite-proximal-gradient-v0/README.md)
  and
  [`finite-proximal-gradient-end-to-end.md`](docs/learn/math/finite-proximal-gradient-end-to-end.md)
  now add exact L1 proximal-gradient soft-threshold replay to the
  optimization/convexity, numerical-analysis, real-analysis, calculus, and
  linear-algebra resource paths. The pack validates smooth-gradient replay,
  ordinary trial-step replay, soft-threshold proximal replay, composite
  objective-decrease replay, a source-linked checked QF_LRA/Farkas rejection
  for a false proximal point, and a proximal-gradient convergence
  Lean-horizon row.

- **Finite projected-gradient resource landed.**
  [`finite-projected-gradient-v0`](artifacts/examples/math/finite-projected-gradient-v0/README.md)
  and
  [`finite-projected-gradient-end-to-end.md`](docs/learn/math/finite-projected-gradient-end-to-end.md)
  now add exact interval projected-gradient replay to the
  optimization/convexity, numerical-analysis, real-analysis, calculus, and
  linear-algebra resource paths. The pack validates gradient replay,
  unconstrained-step replay, interval projection, projected objective-decrease
  replay, a source-linked checked QF_LRA/Farkas rejection for a false projected
  point, and a projected-gradient convergence Lean-horizon row.

- **Finite line-search resource landed.**
  [`finite-line-search-v0`](artifacts/examples/math/finite-line-search-v0/README.md)
  and
  [`finite-line-search-end-to-end.md`](docs/learn/math/finite-line-search-end-to-end.md)
  now add exact Armijo backtracking replay to the optimization/convexity,
  numerical-analysis, real-analysis, calculus, and linear-algebra resource
  paths. The pack validates descent-direction replay, rejected-trial Armijo
  replay, accepted backtracked-step replay, a source-linked checked
  QF_LRA/Farkas rejection for a false Armijo acceptance claim, and a
  line-search convergence Lean-horizon row. At that point, the generated
  resource summary was 95 promoted non-template packs, 477 checks, 215 checked rows, 204
  replay-only rows, and 58 Lean-horizon rows.

- **Finite gradient-descent resource landed.**
  [`finite-gradient-descent-v0`](artifacts/examples/math/finite-gradient-descent-v0/README.md)
  and
  [`finite-gradient-descent-end-to-end.md`](docs/learn/math/finite-gradient-descent-end-to-end.md)
  now add exact quadratic gradient-step replay to the optimization/convexity,
  numerical-analysis, real-analysis, calculus, and linear-algebra resource
  paths. The pack validates gradient/Hessian replay, one exact
  gradient-descent step, objective-decrease and descent-bound replay, a
  source-linked checked QF_LRA/Farkas rejection for a false decrease claim, and
  a convergence Lean-horizon row; later rows also reject false step-coordinate
  and false descent-bound claims through checked QF_LRA/Farkas evidence. At
  that point, the generated resource summary was 94
  promoted non-template packs, 472 checks, 214 checked rows, 201 replay-only
  rows, and 57 Lean-horizon rows.

- **Finite SDP resource landed.**
  [`finite-sdp-v0`](artifacts/examples/math/finite-sdp-v0/README.md) and
  [`finite-sdp-end-to-end.md`](docs/learn/math/finite-sdp-end-to-end.md) now
  add exact two-by-two SDP replay to the optimization/convexity, real-analysis,
  and linear-algebra resource paths. The pack validates primal PSD replay,
  trace/objective replay, dual-slack PSD replay, zero duality-gap checking, a
  source-linked checked QF_LRA/Farkas rejection for a false objective claim,
  and an SDP-duality Lean-horizon row. At that point, the generated resource summary was
  93 promoted non-template packs, 467 checks, 213 checked rows, 198 replay-only
  rows, and 56 Lean-horizon rows.

- **Finite KKT resource landed.**
  [`finite-kkt-v0`](artifacts/examples/math/finite-kkt-v0/README.md) and
  [`finite-kkt-end-to-end.md`](docs/learn/math/finite-kkt-end-to-end.md) now
  add exact constrained-quadratic KKT replay to the optimization/convexity,
  real-analysis, calculus, and linear-algebra resource paths. The pack
  validates one finite feasible-grid replay, one stationarity replay, one
  complementary-slackness replay, a source-linked checked QF_LRA/Farkas
  rejection for a false stationarity multiplier, and a KKT-sufficiency
  Lean-horizon row. At that point, the generated resource summary was 92 promoted
  non-template packs, 462 checks, 212 checked rows, 195 replay-only rows, and
  55 Lean-horizon rows.

- **Finite hyperplane-separation resource landed.**
  [`finite-separation-v0`](artifacts/examples/math/finite-separation-v0/README.md)
  and
  [`finite-separation-end-to-end.md`](docs/learn/math/finite-separation-end-to-end.md)
  now add exact convex-hull/separating-hyperplane replay to the
  optimization/convexity, real-analysis, and linear-algebra resource paths. The
  pack validates one convex-combination witness, one separator score table, one
  supporting-face replay, a source-linked checked QF_LRA/Farkas rejection for a
  false separator, and a separation/duality Lean-horizon row. At that point,
  the generated resource summary was 91 promoted non-template packs, 457
  checks, 211 checked rows, 192 replay-only rows, and 54 Lean-horizon rows.

- **Finite root-finding resource landed.**
  [`finite-root-finding-v0`](artifacts/examples/math/finite-root-finding-v0/README.md)
  and
  [`finite-root-finding-end-to-end.md`](docs/learn/math/finite-root-finding-end-to-end.md)
  now add exact bisection/Newton replay to the numerical-analysis,
  real-analysis, optimization, polynomial, and calculus resource paths. The
  pack validates one bisection bracket update, one Newton step, one residual
  decrease witness, a source-linked checked QF_LRA/Farkas rejection for a false
  Newton iterate, and a root-finding convergence/stability Lean-horizon row.
  At that point, the generated resource summary was 90 promoted non-template
  packs, 452 checks, 210 checked rows, 189 replay-only rows, and 53
  Lean-horizon rows.

- **Finite group-action QF_UF promotion landed.**
  [`finite-group-actions-v0`](artifacts/examples/math/finite-group-actions-v0/)
  now links `bad-action-rejected` and `bad-compatibility-rejected` to
  source-level QF_UF artifacts for malformed identity-action and
  action-compatibility rows. The shared `math_resource_uf_routes` regressions
  emit and check Alethe certificates for those rows, and the generated
  dashboards track the promoted solver-reuse pack.

- **Finite continuous-map QF_UF promotion landed.**
  [`finite-continuous-maps-v0`](artifacts/examples/math/finite-continuous-maps-v0/)
  now links `bad-continuous-map-rejected` to a source-level QF_UF artifact for
  the malformed preimage-membership row. The shared `math_resource_uf_routes`
  regression emits and checks an Alethe certificate for that row, while the
  finite-topology openness failure stays in replay; generated dashboards move
  promoted solver-reuse packs to 18.

- **Finite product-measure QF_LRA promotion landed.**
  [`finite-product-measure-v0`](artifacts/examples/math/finite-product-measure-v0/)
  now links `bad-product-measure-rejected` to a source-level QF_LRA artifact for
  the malformed product-probability row. The shared `math_resource_lra_routes`
  regression emits and independently rechecks Farkas evidence for
  `product_probability = 1/6` versus `product_probability = 1/5`; generated
  dashboards move promoted solver-reuse packs to 19.

- **Finite random-variable QF_LRA promotion landed.**
  [`finite-random-variables-v0`](artifacts/examples/math/finite-random-variables-v0/)
  now links the malformed pushforward-distribution row to a source-level
  QF_LRA artifact. The shared
  `math_resource_lra_routes` regression emits and independently rechecks
  Farkas evidence for `long_probability = 1/4` versus
  `long_probability = 1/2`; generated dashboards move promoted solver-reuse
  packs to 20.

- **Finite integration QF_LRA promotion landed.**
  [`finite-integration-v0`](artifacts/examples/math/finite-integration-v0/)
  now links `bad-expectation-rejected` to a source-level QF_LRA artifact for
  the malformed finite expectation row. The shared `math_resource_lra_routes`
  regression emits and independently rechecks Farkas evidence for
  `integral_value = 5/2` versus `integral_value = 3`; generated dashboards move
  promoted solver-reuse packs to 21.

- **Finite martingales QF_LRA promotion landed.**
  [`finite-martingales-v0`](artifacts/examples/math/finite-martingales-v0/)
  now links `bad-martingale-rejected` to a source-level QF_LRA artifact for the
  malformed terminal table. The shared `math_resource_lra_routes` regression
  emits and independently rechecks Farkas evidence for
  `up_block_conditional_expectation = 3/2` versus
  `up_block_conditional_expectation = 1`; generated dashboards move promoted
  solver-reuse packs to 22.

- **Finite Markov-chain solver-reuse promotion landed.**
  [`finite-markov-chain-v0`](artifacts/examples/math/finite-markov-chain-v0/)
  now carries explicit promoted `solver_reuse` metadata for the existing
  `bad-stochastic-row-rejected` QF_LRA/Farkas artifact. The shared
  `math_resource_lra_routes` regression continues to recheck
  `row_sum = p10 + p11`, `p10 = 1/3`, `p11 = 1/3`, and `row_sum = 1`;
  generated dashboards move promoted solver-reuse packs to 23.

- **Finite concentration QF_LRA promotion landed.**
  [`finite-concentration-v0`](artifacts/examples/math/finite-concentration-v0/)
  now links `bad-concentration-bound-rejected` to a source-level QF_LRA artifact
  for the malformed finite tail-bound row. The shared
  `math_resource_lra_routes` regression emits and independently rechecks
  Farkas evidence for `tail_probability = 1/4` and
  `tail_probability <= 1/8`; generated dashboards move promoted solver-reuse
  packs to 24.

- **Finite conditional-expectation QF_LRA promotion landed.**
  [`finite-conditional-expectation-v0`](artifacts/examples/math/finite-conditional-expectation-v0/)
  now carries promoted `solver_reuse` metadata for its existing source-level
  QF_LRA artifact. The shared `math_resource_lra_routes` regression emits and
  independently rechecks Farkas evidence for
  `(1/2) * high_block_expectation = 3` and
  `high_block_expectation = 5`; generated dashboards move promoted
  solver-reuse packs to 25.

- **Finite hitting-time QF_LRA promotion landed.**
  [`finite-hitting-times-v0`](artifacts/examples/math/finite-hitting-times-v0/)
  now carries promoted `solver_reuse` metadata for its existing source-level
  QF_LRA artifact. The shared `math_resource_lra_routes` regression emits and
  independently rechecks Farkas evidence for `h_start = 3`, `h_middle = 2`,
  and `2*h_start = 2 + h_start + h_middle`; generated dashboards move promoted
  solver-reuse packs to 26.

- **Finite Euler-method QF_LRA promotion landed.**
  [`finite-euler-method-v0`](artifacts/examples/math/finite-euler-method-v0/)
  now carries promoted `solver_reuse` metadata for its existing source-level
  QF_LRA artifact. The shared `math_resource_lra_routes` regression emits and
  independently rechecks Farkas evidence for `state = 1`, `derivative = -1`,
  `next_state = state + (1/2)*derivative`, and `next_state = 3/4`;
  generated dashboards move promoted solver-reuse packs to 27.

- **Linear, geometry, statistics, and numerical QF_LRA promotion batch landed.**
  `least-squares-regression-v0`, `real-analysis-rational-v0`,
  `orientation-area-geometry-v0`, `numerical-linear-algebra-v0`,
  `random-matrix-finite-v0`, `affine-geometry-v0`,
  `inner-product-spaces-rational-v0`, `spectral-linear-algebra-v0`, and
  `matrix-invariants-v0` now carry promoted `solver_reuse` metadata pointing at
  their checked Farkas rows and source-level SMT-LIB artifacts. The shared
  `math_resource_lra_routes` regression checks all nine rows as part of the
  29-test QF_LRA resource route suite; generated dashboards move promoted
  solver-reuse packs to 36 and leave 48 unclassified packs.

- **Equality-heavy QF_UF/Alethe promotion batch landed.**
  `equivalence-classes-v0`, `relations-functions-v0`, `finite-groups-v0`,
  `function-composition-v0`, `finite-algebra-homomorphisms-v0`,
  `finite-monoids-v0`, `finite-order-lattices-v0`,
  `finite-permutation-groups-v0`, `finite-vector-spaces-v0`,
  `finite-dual-spaces-v0`, `finite-modules-v0`, and
  `finite-tensor-products-v0` now carry promoted `solver_reuse` metadata tied
  to source-level QF_UF artifacts. The shared `math_resource_uf_routes`
  regression checks all twelve rows through the zero-trust Alethe route;
  generated dashboards move promoted solver-reuse packs to 48 and leave
  36 unclassified packs.

- **Integer-count QF_LIA/Diophantine promotion batch landed.**
  `modular-arithmetic-v0`, `exact-statistical-tests-v0`,
  `finite-simplicial-homology-v0`, `induction-patterns-v0`, and
  `descriptive-statistics-v0` now carry promoted `solver_reuse` metadata tied
  to source-level QF_LIA artifacts. The shared `math_resource_lia_routes`
  regression checks all five rows with independently rechecked Diophantine
  evidence; generated dashboards move promoted solver-reuse packs to 53 and
  leave 31 unclassified packs.

- **Finite algebra and graph QF_BV/DRAT promotion batch landed.**
  `finite-rings-v0`, `finite-fields-v0`, and `graph-coloring-v0` now carry
  promoted `solver_reuse` metadata tied to source-level QF_BV artifacts. The
  shared `math_resource_bv_routes` regression checks all three rows with
  independently rechecked DIMACS/DRAT evidence; generated dashboards move
  promoted solver-reuse packs to 56 and leave 28 unclassified packs.

- **Exact finite probability QF_LRA/Farkas promotion landed.**
  `finite-probability-v0` now carries promoted `solver_reuse` metadata tied to
  the checked bad-normalization, bad-conditional-probability, and bad-Bayes
  posterior source SMT-LIB rows.
  The focused `math_resource_lra_routes finite_probability` regression checks
  both rows with independently rechecked Farkas evidence; generated dashboards
  move promoted solver-reuse packs to 57 and leave 27 unclassified packs.

- **Linear algebra/optimization QF_LRA/Farkas source promotion landed.**
  `linear-algebra-rational-v0`, `linear-optimization-v0`, and
  `convexity-rational-v0` now carry source-level SMT-LIB artifacts and promoted
  `solver_reuse` metadata for their singular-system, objective-threshold, and
  bad-midpoint rows. The `math_resource_lra_routes` regression now parses those
  artifacts before checking independent Farkas evidence; generated dashboards
  move promoted solver-reuse packs to 60 and leave 24 unclassified packs.

- **Finite set/proof-method Bool/CNF promotion landed.**
  `finite-sets-v0` and `proof-methods-patterns-v0` now carry promoted
  `solver_reuse` metadata for their existing DIMACS-backed distributive-law and
  contradiction rows. The `math_resource_boolean_routes` regression already
  parses both CNF artifacts and checks generated DRAT plus elaborated LRAT
  evidence; generated dashboards move promoted solver-reuse packs to 62 and
  leave 22 unclassified packs.

- **Rational-order and gcd/Bezout arithmetic source promotion landed.**
  `rationals-lra-v0` now carries source-level SMT-LIB artifacts and promoted
  `solver_reuse` metadata for its fixed trichotomy and order-transitivity
  conflicts. `gcd-bezout-v0` now carries the same source-linked promotion for
  its fixed Diophantine gcd obstruction. The focused LRA and LIA route
  regressions parse those artifacts before checking independent Farkas or
  Diophantine evidence; generated dashboards move promoted solver-reuse packs
  to 64 and leave 20 unclassified packs.

- **PHP Bool/CNF resource promotion landed.**
  `proof-methods-refutation-v0` and `counting-v0` now carry source-level
  DIMACS artifacts and promoted `solver_reuse` metadata for their fixed
  `PHP(3,2)` rows. The `math_resource_boolean_routes` regression parses both
  CNF artifacts, emits DRAT, elaborates LRAT, and independently checks both
  proof objects; that promotion moved promoted solver-reuse packs to 66 before
  the later replay-only classification batch split out non-benchmark rows.

- **Replay-only solver-reuse classification batch landed.**
  `bounded-dynamics-v0`, `complex-algebraic-v0`,
  `coordinate-geometry-v0`, `finite-measure-v0`, `finite-operator-v0`, and
  `finite-topology-v0` initially received explicit `non-benchmark-horizon`
  `solver_reuse` metadata. These packs were kept as educational finite-replay
  resources until they gained negative, certificate-bearing rows; later
  finite-measure and finite-topology promotions moved those two packs out of
  the non-benchmark bucket.

- **Generating-functions QF_LIA/Diophantine promotion landed.**
  `generating-functions-v0` now carries promoted `solver_reuse` metadata for
  its bad finite Cauchy-product coefficient row. The new source-level artifact
  `bad-cauchy-product-diophantine-conflict.smt2` isolates the contradiction
  `coeff_2 = 5 + 8` and `coeff_2 = 12`, and
  `math_resource_lia_routes::generating_functions_bad_cauchy_product_emits_checked_diophantine_evidence`
  checks the emitted `UnsatDiophantine` certificate. Generated dashboards now
  report 67 promoted, 6 non-benchmark-horizon, and 11 unclassified
  solver-reuse packs.

- **Polynomial-identities QF_LIA/Diophantine promotion landed.**
  `polynomial-identities-v0` now carries promoted `solver_reuse` metadata for
  its false rational-root row. The new source-level artifact
  `false-rational-root-diophantine-conflict.smt2` isolates the contradiction
  `p(1)=2` and `p(1)=0` for `p(x)=x^2+1`, and
  `math_resource_lia_routes::polynomial_identities_false_rational_root_emits_checked_diophantine_evidence`
  checks the emitted `UnsatDiophantine` certificate. Generated dashboards now
  report 68 promoted, 6 non-benchmark-horizon, and 10 unclassified
  solver-reuse packs.

- **Finite-predicate Bool/CNF promotion landed.**
  `finite-predicate-v0` now carries promoted `solver_reuse` metadata for its
  finite `forall x. P(x) -> exists x. P(x)` no-counterexample row. The new
  source-level artifact `forall-implies-exists.cnf` isolates the fixed
  two-element quantifier expansion `P(a)`, `P(b)`, `not P(a)`, and `not P(b)`,
  and
  `math_resource_boolean_routes::finite_predicate_forall_implies_exists_emits_checked_drat_and_lrat`
  checks emitted DRAT plus elaborated LRAT evidence. Generated dashboards now
  report 69 promoted, 6 non-benchmark-horizon, and 9 unclassified solver-reuse
  packs.

- **Calculus Riemann-sum QF_LRA/Farkas promotion landed.**
  `calculus-riemann-sum-v0` now carries promoted `solver_reuse` metadata for
  its false exact-integral row. The new source-level artifact
  `false-integral-farkas-conflict.smt2` isolates the contradiction
  `integral_value = 1/2` and `integral_value = 3/4`, and
  `math_resource_lra_routes::calculus_riemann_sum_false_integral_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards now report
  70 promoted, 6 non-benchmark-horizon, and 8 unclassified solver-reuse packs.

- **Sequence-limit QF_LRA/Farkas promotion landed.**
  `sequence-limit-shadow-v0` now carries promoted `solver_reuse` metadata for
  its bounded Cauchy-tail no-counterexample row. The new source-level artifact
  `bounded-cauchy-tail-farkas-conflict.smt2` isolates replay's maximum pair
  distance `4/21` against the malformed threshold `>= 1/2`, and
  `math_resource_lra_routes::sequence_limit_bounded_cauchy_tail_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards now report
  71 promoted, 6 non-benchmark-horizon, and 7 unclassified solver-reuse packs.

- **Multivariable-calculus QF_LRA/Farkas promotion landed.**
  `multivariable-calculus-rational-v0` now carries promoted `solver_reuse`
  metadata for its bad-gradient row. The new source-level artifact
  `bad-gradient-farkas-conflict.smt2` isolates replay's computed
  `gradient_y = 14` against the malformed claim `gradient_y = 13`, and
  `math_resource_lra_routes::multivariable_calculus_bad_gradient_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards now report
  72 promoted, 6 non-benchmark-horizon, and 6 unclassified solver-reuse packs.

- **Calculus-algebraic QF_LRA/Farkas promotion landed.**
  `calculus-algebraic-shadow-v0` now carries promoted `solver_reuse` metadata
  for its false derivative-value row. The new source-level artifact
  `false-derivative-farkas-conflict.smt2` isolates replay's computed
  `derivative_value = 6` against the malformed claim `derivative_value = 5`,
  and
  `math_resource_lra_routes::calculus_algebraic_false_derivative_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards now report
  73 promoted, 6 non-benchmark-horizon, and 5 unclassified solver-reuse packs.

- **Complex-plane QF_LRA/Farkas promotion landed.**
  `complex-plane-transforms-v0` now carries promoted `solver_reuse` metadata
  for its bad unit-square real-part row. The new source-level artifact
  `bad-unit-square-real-part-farkas-conflict.smt2` isolates the equivalent
  contradiction `negated_real_part = 1` and `negated_real_part < 0`, and
  `math_resource_lra_routes::complex_plane_bad_unit_square_real_part_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards now report
  74 promoted, 6 non-benchmark-horizon, and 4 unclassified solver-reuse packs.

- **Induction-obligations QF_LIA arithmetic-evidence promotion landed.**
  `induction-obligations-v0` now carries promoted `solver_reuse` metadata for
  its bounded step no-counterexample row. The new source-level artifact
  `bounded-step-counterexample-count-lia-conflict.smt2` isolates finite
  replay's computed `bad_step_count = 0` against the malformed claim
  `bad_step_count >= 1`, and
  `math_resource_lia_routes::induction_obligations_bounded_step_count_emits_checked_lia_evidence`
  checks emitted QF_LIA arithmetic evidence. Generated dashboards now
  report 75 promoted, 6 non-benchmark-horizon, and 3 unclassified
  solver-reuse packs.

- **Cardinality-principles QF_LIA/Diophantine promotion landed.**
  `cardinality-principles-v0` now carries promoted `solver_reuse` metadata for
  its overlapping-set false additivity row. The new source-level artifact
  `overlap-additivity-diophantine-conflict.smt2` isolates finite replay's
  computed `union_count = 4` against the malformed disjoint-additivity claim
  `claimed_disjoint_sum = 6` and the asserted equality between them, and
  `math_resource_lia_routes::cardinality_principles_overlap_additivity_emits_checked_diophantine_evidence`
  checks the emitted `UnsatDiophantine` certificate. Generated dashboards now
  report 76 promoted, 6 non-benchmark-horizon, and 2 unclassified
  solver-reuse packs.

- **Polynomial-factorization QF_LRA/Farkas promotion landed.**
  `polynomial-factorization-rational-v0` now carries promoted `solver_reuse`
  metadata for its fixed irreducible-quadratic discriminant row. The new
  source-level artifact
  `irreducible-quadratic-discriminant-farkas-conflict.smt2` isolates exact
  replay's computed `discriminant = -4` as `discriminant + 4 = 0` against the
  nonnegative-discriminant requirement for rational linear factors, and
  `math_resource_lra_routes::polynomial_factorization_irreducible_quadratic_discriminant_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards now report
  77 promoted, 6 non-benchmark-horizon, and 1 unclassified solver-reuse pack.

- **Real-algebra RCF-shadow QF_LRA/Farkas promotion landed.**
  `reals-rcf-shadow-v0` now carries promoted `solver_reuse` metadata for its
  fixed negative-discriminant no-real-root row. The new source-level artifact
  `negative-discriminant-farkas-conflict.smt2` isolates exact replay's
  computed `discriminant = -4` as `discriminant + 4 = 0` against the
  nonnegative-discriminant requirement for a real quadratic root, and
  `math_resource_lra_routes::reals_rcf_shadow_negative_discriminant_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards now report
  78 promoted, 6 non-benchmark-horizon, and 0 unclassified solver-reuse packs.

- **Finite-measure QF_LRA/Farkas promotion landed.**
  `finite-measure-v0` now carries promoted `solver_reuse` metadata for its bad
  complement-measure row. The new source-level artifact
  `bad-complement-measure-farkas-conflict.smt2` isolates replay's computed
  `mu(A) = 1/3` and `mu(U) = 1` against the malformed complement claim
  `mu(A^c) = 1/2` while preserving complement additivity, and
  `math_resource_lra_routes::finite_measure_bad_complement_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards then reported
  79 promoted, 5 non-benchmark-horizon, and 0 unclassified solver-reuse packs.

- **Finite-topology Bool/CNF promotion landed.**
  `finite-topology-v0` now carries promoted `solver_reuse` metadata for its
  bad empty-open row. The new source-level artifact
  `bad-empty-open-rejected.cnf` isolates the malformed open-set table that
  omits the empty set against the topology axiom requiring it, and
  `math_resource_boolean_routes::finite_topology_bad_empty_open_emits_checked_drat_and_lrat`
  checks emitted DRAT plus elaborated LRAT evidence. Generated dashboards then
  reported 80 promoted, 4 non-benchmark-horizon, and 0 unclassified
  solver-reuse packs.

- **Coordinate-geometry QF_LRA/Farkas promotion landed.**
  `coordinate-geometry-v0` now carries promoted `solver_reuse` metadata for
  its bad squared-distance row. The new source-level artifact
  `bad-distance-squared-farkas-conflict.smt2` isolates exact replay's computed
  squared distance `25` against the malformed claim `26`, and
  `math_resource_lra_routes::coordinate_geometry_bad_distance_squared_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards then reported
  81 promoted, 2 non-benchmark-horizon, and 0 unclassified solver-reuse packs.

- **Finite-operator QF_LRA/Farkas promotion landed.**
  `finite-operator-v0` now carries promoted `solver_reuse` metadata for its
  bad operator-bound row. The new source-level artifact
  `bad-operator-bound-farkas-conflict.smt2` isolates exact replay's computed
  image norm `3` against the malformed upper-bound claim `2`, and
  `math_resource_lra_routes::finite_operator_bad_operator_bound_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards then reported
  82 promoted, 2 non-benchmark-horizon, and 0 unclassified solver-reuse packs.

- **Complex-algebraic QF_LRA/Farkas promotion landed.**
  `complex-algebraic-v0` now carries promoted `solver_reuse` metadata for its
  bad norm-squared row. The new source-level artifact
  `bad-norm-squared-farkas-conflict.smt2` isolates exact real-pair replay's
  computed norm squared `25` against the malformed claim `26`, and
  `math_resource_lra_routes::complex_algebraic_bad_norm_squared_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards now report
  83 promoted, 1 non-benchmark-horizon, and 0 unclassified solver-reuse packs.

- **Bounded-dynamics QF_LRA/Farkas promotion landed.**
  `bounded-dynamics-v0` now carries promoted `solver_reuse` metadata for its
  bad invariant-bound row. The new source-level artifact
  `bad-invariant-bound-farkas-conflict.smt2` isolates exact recurrence replay's
  terminal/max state `8` against the malformed upper-bound claim `6`, and
  `math_resource_lra_routes::bounded_dynamics_bad_invariant_bound_artifact_emits_checked_farkas`
  checks the emitted `UnsatFarkas` certificate. Generated dashboards now report
  84 promoted, 0 non-benchmark-horizon, and 0 unclassified solver-reuse packs.

- **Proof-object anatomy learner page landed.**
  [`proof-object-anatomy-end-to-end.md`](docs/learn/math/proof-object-anatomy-end-to-end.md)
  now follows `proof-methods-refutation-v0` from the PHP(3,2) source claim
  through committed CNF, emitted DRAT/LRAT proof objects, and same-artifact
  corrupted-proof rejection. The Boolean route regression now includes
  `proof_methods_refutation_php_3_2_rejects_tampered_drat_and_lrat`, which
  checks the good proof first, removes the final DRAT empty-clause step, clears
  LRAT hints, and requires both corrupted certificates to reject.

- **Farkas certificate anatomy learner page landed.**
  [`farkas-certificate-anatomy-end-to-end.md`](docs/learn/math/farkas-certificate-anatomy-end-to-end.md)
  now follows `linear-optimization-v0` from the exact LP threshold conflict
  through source SMT-LIB, emitted `UnsatFarkas` evidence, and same-artifact
  multiplier tamper rejection. The LRA route regression now includes
  `linear_optimization_objective_threshold_rejects_tampered_farkas_certificate`,
  which checks the genuine certificate first, zeroes a Farkas multiplier, and
  requires the corrupted certificate to reject.

- **Alethe certificate anatomy learner page landed.**
  [`alethe-certificate-anatomy-end-to-end.md`](docs/learn/math/alethe-certificate-anatomy-end-to-end.md)
  now follows `equivalence-classes-v0` from a quotient-map congruence conflict
  through source SMT-LIB, emitted zero-trust `UnsatAletheProof` evidence, and
  same-artifact truncated-proof rejection. The UF route regression already
  includes `qf_uf_resource_route_rejects_tampered_alethe_certificate`, which
  checks the genuine proof first, removes the closing Alethe command, and
  requires the corrupted certificate to reject.

- **Diophantine certificate anatomy learner page landed.**
  [`diophantine-certificate-anatomy-end-to-end.md`](docs/learn/math/diophantine-certificate-anatomy-end-to-end.md)
  now follows `modular-arithmetic-v0` from the nonunit inverse equation
  `2*b - 6*k = 1` through source SMT-LIB, emitted `UnsatDiophantine` evidence,
  and same-artifact contradiction-row tamper rejection, with the sibling
  incompatible CRT equation `4*a - 6*b = 1` listed as the same checked pattern.
  The LIA route regression already includes
  `qf_lia_resource_route_rejects_tampered_diophantine_certificate`, which
  checks the genuine certificate first, changes the recorded constant, and
  requires the corrupted certificate to reject.

- **QF_BV bit-blast certificate anatomy learner page landed.**
  [`qf-bv-bitblast-certificate-anatomy-end-to-end.md`](docs/learn/math/qf-bv-bitblast-certificate-anatomy-end-to-end.md)
  now follows `finite-fields-v0` from fixed-width finite-field BV rows through
  source SMT-LIB, generated DIMACS/DRAT evidence, and same-artifact
  truncated-DRAT rejection. The BV route regression already
  includes `qf_bv_resource_route_rejects_tampered_drat_certificate`, which
  checks the genuine proof first, removes the final DRAT step, and requires the
  corrupted certificate to reject.

- **Foundational resource boundary review refreshed.**
  [`LIBRARY-BOUNDARY-DECISION.md`](docs/foundational-resources/LIBRARY-BOUNDARY-DECISION.md)
  now records the refreshed 102-promoted, 0 non-benchmark-horizon, and
  0-unclassified solver-reuse counts. The decision remains in-repo and
  JSON-first: the query consumer reads promoted solver-reuse rows, but there is
  still no external consumer, repeated typed API demand, or reusable encoder
  boundary that warrants a new crate or separate repository.

- **Curriculum pressure by fragment landed.** The generated
  [`curriculum-pressure-by-fragment.md`](docs/foundational-resources/generated/curriculum-pressure-by-fragment.md)
  dashboard groups the 102 non-template math packs into overlapping Bool/CNF,
  QF_BV, QF_LIA, QF_LRA, QF_UF, NRA/RCF, finite-replay, and Lean-horizon
  buckets. It is now part of `check-foundational-resources`, so stale fragment
  planning output fails the same gate as coverage and proof-gap dashboards.

- **Solver-reuse disposition audit landed.** The generated
  [`solver-reuse-disposition-audit.md`](docs/foundational-resources/generated/solver-reuse-disposition-audit.md)
  dashboard audits every non-template math pack's `solver_reuse` disposition,
  reporting 102 promoted, 0 non-benchmark-horizon, and 0 unclassified packs.
  It is now part of `check-foundational-resources`, so any newly added
  unclassified pack appears in a freshness-checked queue.

- **Probability/statistics bridge concepts landed.**
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) now
  generates five bridge rows for finite probability mass tables, pushforward
  distributions, stochastic kernels, conditional expectation, and tail/count
  obstructions. Those rows remain part of the current bridge atlas and reuse
  existing finite probability, measure, kernel, martingale, hitting-time,
  concentration, and exact-test packs.

- **Measure-theory bridge concepts landed.**
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) now
  generates `bridge_finite_measure_additivity` and
  `bridge_finite_product_integration`, making finite event-algebra/additivity,
  complement, product-table, marginal, finite Fubini-style sum, and
  simple-function integral replay queryable without overstating Lebesgue,
  convergence-theorem, or almost-everywhere coverage.

- **Optimization/convexity bridge concepts landed.**
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) now
  generates `bridge_lp_objective_farkas` and
  `bridge_rational_convexity_shadow`, making exact LP feasibility,
  objective-threshold Farkas replay, finite midpoint/Jensen shadows, affine
  monotonicity, gradient replay, Hessian-minor witnesses, and least-squares
  normal-equation replay queryable. The finite KKT pack contributes
  stationarity/complementarity replay, the finite SDP pack contributes
  two-by-two PSD/objective/slack replay, the finite-gradient-descent pack
  contributes exact descent-step replay, and the finite-line-search pack
  contributes Armijo rejection/acceptance replay. The finite-wolfe-line-search
  pack contributes Wolfe sufficient-decrease/curvature replay. The
  finite-projected-gradient pack contributes interval-projection replay, and
  the finite-proximal-gradient pack contributes L1 soft-threshold replay, while
  KKT sufficiency, duality, SDP strong duality, Wolfe/projected-gradient
  convergence, proximal-gradient convergence, and algorithm-convergence theorem
  coverage remain horizons.

- **Measure-theory field-readiness consumer query landed.**
  [`CONSUMER-QUERIES.md`](docs/foundational-resources/CONSUMER-QUERIES.md)
  now shows measure/Farkas field readiness, measure bridge concept lookup, and
  checked measure-theory Farkas row drill-downs.
  [`check-foundational-resources.sh`](scripts/check-foundational-resources.sh)
  runs those same queries so finite measure, product-measure, integration,
  random-variable, conditional-expectation, martingale, kernel, hitting-time,
  and concentration resources stay visible through the committed JSON contract.

- **Proof/logic bridge concepts landed.**
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) now
  generates four bridge rows for refutation-as-query, finite proof-pattern
  replay, finite quantifier expansion, and bounded induction obligations. The
  rows remain part of the current bridge atlas and tie proof-method,
  finite-predicate, induction, natural-arithmetic, and Boolean/CNF packs to
  shared finite-proof vocabulary.

- **Proof-object anatomy bridge concepts landed.**
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) now
  generates four bridge rows for Boolean CNF DRAT/LRAT anatomy, QF_LRA Farkas
  certificate anatomy, QF_UF Alethe certificate anatomy, and QF_BV bit-blast
  certificate anatomy. Those rows remain part of the current bridge atlas and
  make the active proof-object routes queryable through shared R1 vocabulary.

- **Set/foundations bridge concepts landed.**
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) now
  generates five bridge rows for finite Boolean algebra, finite
  partition/relation roundtrips, finite image/preimage/inverse tables, finite
  bijection/cardinality checks, and cardinality theorem horizons. That
  increment remains part of the current bridge atlas.

- **Standalone finite topology and finite measure lessons landed.**
  [`finite-topology-end-to-end.md`](docs/learn/math/finite-topology-end-to-end.md)
  now follows `finite-topology-v0` through topology axiom replay,
  closure/interior replay, exact metric-ball replay, and checked Bool/CNF
  bad-empty-open rejection.
  [`finite-measure-end-to-end.md`](docs/learn/math/finite-measure-end-to-end.md)
  now follows `finite-measure-v0` through finite sigma-algebra replay, exact
  finite additivity, event complements, and checked QF_LRA/Farkas
  bad-complement rejection. The combined topology/measure page remains as the
  cross-field bridge.

- **Standalone linear optimization lesson landed.**
  [`linear-optimization-end-to-end.md`](docs/learn/math/linear-optimization-end-to-end.md)
  now follows `linear-optimization-v0` through exact LP feasible-point replay,
  objective-threshold replay, checked QF_LRA/Farkas infeasible-threshold
  evidence, and tampered-certificate rejection. The combined linear-system/LP
  page remains as the matrix-to-optimization bridge.

- **Standalone finite probability mass-table lesson landed.**
  [`finite-probability-mass-tables-end-to-end.md`](docs/learn/math/finite-probability-mass-tables-end-to-end.md)
  now follows `finite-probability-v0` through exact PMF normalization,
  conditional probability replay, Bayes posterior replay, checked QF_LRA/Farkas
  bad-normalization rejection, checked bad-conditional-probability rejection,
  and checked bad-posterior rejection. The broader
  finite-probability page remains as the stochastic-process bridge.

- **Curriculum status audit landed.** The generated
  [`curriculum-status-audit.md`](docs/foundational-resources/generated/curriculum-status-audit.md)
  dashboard separates source `curriculum_status` from generated
  `resource_status`: non-horizon curriculum rows with validated packs now
  generate `validated` resource maturity, while source `planned` rows remain
  visible as explicit `covered` versus `lean-horizon` review items. The
  dashboard is now freshness-checked by `check-foundational-resources`.

- **`needs-proof-route` cleanup landed.** Classified
  [`descriptive-statistics-v0`](artifacts/examples/math/descriptive-statistics-v0/)
  as finite replay for current SAT witness rows plus QF_LRA/Farkas for future
  impossible exact-rational statistic constraints; its first inconsistent
  integer margin/count row now has a checked QF_LIA/Diophantine regression for
  the bad contingency total. Classified
  [`finite-probability-v0`](artifacts/examples/math/finite-probability-v0/) as
  finite replay for current SAT witness rows plus QF_LRA/Farkas for impossible
  probability-table constraints; its first bad normalization row now has a
  checked QF_LRA/Farkas regression. After dashboard regeneration, the generated
  proof-upgrade queue has no `needs-proof-route` rows; `finite-probability-v0`
  is now `checked-evidence` with one checked row and three replay rows.

- **First Boolean CNF/LRAT resource proof regression landed.**
  [`graph-coloring-v0`](artifacts/examples/math/graph-coloring-v0/) now has a
  deterministic DIMACS artifact for triangle non-2-colorability. The focused
  `axeyum-cnf` regression parses that artifact, emits DRAT from the
  proof-producing SAT core, elaborates to LRAT, and checks both proof objects,
  making the first CNF/LRAT proof-upgrade lane concrete without trusting search.

- **Proof-methods CNF/LRAT regression landed.**
  [`proof-methods-patterns-v0`](artifacts/examples/math/proof-methods-patterns-v0/)
  now has a deterministic DIMACS artifact for the contradiction row `p`,
  `p -> q`, `not q`. The same resource-backed `axeyum-cnf` regression emits
  DRAT, elaborates LRAT, and checks both proof objects, leaving only
  `finite-sets-v0` as the remaining first-wave Boolean CNF/LRAT target.

- **Finite-sets CNF/LRAT regression landed.**
  [`finite-sets-v0`](artifacts/examples/math/finite-sets-v0/) now has a
  deterministic DIMACS artifact for the malformed distributive-law
  counterexample at element `c`. The shared `axeyum-cnf` resource regression
  emits DRAT, elaborates LRAT, and checks both proof objects; the first-wave
  Boolean CNF/LRAT target set is now covered by concrete resource artifacts.

- **Finite-order-lattices bad top-element CNF/LRAT regression landed.**
  [`finite-order-lattices-v0`](artifacts/examples/math/finite-order-lattices-v0/)
  now promotes the false Boolean-lattice top-element claim to checked evidence:
  exact relation replay identifies `B !<= A`, the bad claim that `A` is top
  requires `B <= A`, and the one-variable CNF contradiction is emitted through
  DRAT, elaborated to LRAT, and checked by the shared Boolean resource
  regression.

- **Rationals QF_LRA/Farkas regression landed.**
  [`rationals-lra-v0`](artifacts/examples/math/rationals-lra-v0/) now promotes
  its fixed trichotomy and order-transitivity `unsat` rows to checked evidence.
  The new `axeyum-solver` resource regression builds the exact rational
  branches, requires `UnsatFarkas` evidence, rechecks the evidence
  independently, and records the certified Farkas trust step.

- **Linear-algebra QF_LRA/Farkas regression landed.**
  [`linear-algebra-rational-v0`](artifacts/examples/math/linear-algebra-rational-v0/)
  now promotes its singular inconsistent-system row to checked evidence. The
  shared LRA resource regression builds `x + y = 1` and `2x + 2y = 3`, requires
  `UnsatFarkas` evidence, and rechecks the certificate independently.

- **Linear-optimization QF_LRA/Farkas regression landed.**
  [`linear-optimization-v0`](artifacts/examples/math/linear-optimization-v0/)
  now binds its already-checked objective-threshold row to Axeyum's evidence
  path. The shared LRA resource regression builds `x + y <= 4` and
  `x + y >= 5`, requires `UnsatFarkas` evidence, and rechecks the certificate
  independently.

- **Convexity QF_LRA/Farkas regression landed.**
  [`convexity-rational-v0`](artifacts/examples/math/convexity-rational-v0/)
  now binds its bad midpoint-convexity and bad affine-threshold rows to
  Axeyum's evidence path. The shared LRA resource regression builds the
  division-free inequality `2*f(midpoint) <= f(left)+f(right)` over the fixed
  values and parses the threshold-shortfall SMT-LIB artifact, requires
  `UnsatFarkas` evidence, and rechecks the certificate independently.

- **Finite-concentration QF_LRA/Farkas regression landed.**
  [`finite-concentration-v0`](artifacts/examples/math/finite-concentration-v0/)
  now binds its bad finite tail-bound row to Axeyum's evidence path. The
  shared LRA resource regression builds `tail_probability = 1/4` and
  `tail_probability <= 1/8`, requires `UnsatFarkas` evidence, and rechecks the
  certificate independently.

- **Equivalence-classes QF_UF/Alethe regression landed.**
  [`equivalence-classes-v0`](artifacts/examples/math/equivalence-classes-v0/)
  now upgrades its quotient-map congruence row from proof-gap to checked. The
  new SMT-LIB artifact asserts `a = c` and `q(a) != q(c)` over declared carrier
  sorts; the resource regression requires `prove_qf_uf_unsat_alethe` to emit a
  pure EUF `Evidence::UnsatAletheProof` and rechecks it independently.

- **Relations/functions QF_UF/Alethe regression landed.**
  [`relations-functions-v0`](artifacts/examples/math/relations-functions-v0/)
  now has a checked proof-object row for function single-valuedness. The new
  SMT-LIB artifact asserts `f(x0) = y0`, `f(x0) = y1`, and `y0 != y1`; the
  shared UF resource regression requires a pure EUF `Evidence::UnsatAletheProof`
  and rechecks it independently.

- **Finite-groups QF_UF/Alethe regression landed.**
  [`finite-groups-v0`](artifacts/examples/math/finite-groups-v0/) now has a
  checked proof-object row for binary-operation congruence. The new SMT-LIB
  artifact asserts `a = b`, `c = d`, and `mul(a,c) != mul(b,d)`; the shared UF
  resource regression requires a pure EUF `Evidence::UnsatAletheProof` and
  rechecks it independently.

- **Function-composition QF_UF/Alethe regression landed.**
  [`function-composition-v0`](artifacts/examples/math/function-composition-v0/)
  now has a checked proof-object row for composition application consistency.
  The new SMT-LIB artifact asserts `comp(a) = g(f(a))`, `f(a) = b`,
  `g(b) = c`, and `comp(a) != c`; the shared UF resource regression requires a
  pure EUF `Evidence::UnsatAletheProof` and rechecks it independently.

- **Finite-algebra-homomorphisms QF_UF/Alethe regression landed.**
  [`finite-algebra-homomorphisms-v0`](artifacts/examples/math/finite-algebra-homomorphisms-v0/)
  now has a checked proof-object row for homomorphism-preservation congruence.
  The new SMT-LIB artifact asserts source congruence plus a preservation
  equality and refutes the induced preservation equality for the congruent
  source pair; the shared UF resource regression requires a pure EUF
  `Evidence::UnsatAletheProof` and rechecks it independently.

- **Finite-monoids QF_UF/Alethe regression landed.**
  [`finite-monoids-v0`](artifacts/examples/math/finite-monoids-v0/) now has a
  checked proof-object row for the bad associativity conflict. The new
  SMT-LIB artifact asserts the failing table equations, the associativity
  claim `(b*b)*b = b*(b*b)`, and `a != b`; the shared UF resource regression
  requires a pure EUF `Evidence::UnsatAletheProof` and rechecks it
  independently.

- **Finite-order-lattices QF_UF/Alethe regression landed.**
  [`finite-order-lattices-v0`](artifacts/examples/math/finite-order-lattices-v0/)
  now has a checked proof-object row for the bad antisymmetry conflict. The
  new SMT-LIB artifact records the failing relation facts, the antisymmetry
  equality claim `x = y`, and `x != y`; the shared UF resource regression
  requires a pure EUF `Evidence::UnsatAletheProof` and rechecks it
  independently.

- **Finite-permutation-groups QF_UF/Alethe regression landed.**
  [`finite-permutation-groups-v0`](artifacts/examples/math/finite-permutation-groups-v0/)
  now has a checked proof-object row for the bad nonbijection conflict. The
  new SMT-LIB artifact records the duplicate-image table equations and refutes
  the fixed distinct-image claim `bad(1) != bad(2)`; the shared UF resource
  regression requires a pure EUF `Evidence::UnsatAletheProof` and rechecks it
  independently.

- **Finite-vector-spaces QF_UF/Alethe regression landed.**
  [`finite-vector-spaces-v0`](artifacts/examples/math/finite-vector-spaces-v0/)
  now has a checked proof-object row for the bad subspace-closure conflict.
  The new SMT-LIB artifact records `10 + 01 = 11`, subset membership for
  `10` and `01`, absence of `11`, and the fixed closure membership claim; the
  shared UF resource regression requires a pure EUF
  `Evidence::UnsatAletheProof` and rechecks it independently.

- **Finite-dual-spaces QF_UF/Alethe regression landed.**
  [`finite-dual-spaces-v0`](artifacts/examples/math/finite-dual-spaces-v0/)
  now has a checked proof-object row for the bad covector-additivity conflict.
  The new SMT-LIB artifact records `10 + 01 = 11`, the malformed evaluation
  table, `1 + 1 = 0`, and the fixed additivity equality; the shared UF
  resource regression requires a pure EUF `Evidence::UnsatAletheProof` and
  rechecks it independently.

- **Finite-modules QF_UF/Alethe regression landed.**
  [`finite-modules-v0`](artifacts/examples/math/finite-modules-v0/) now has a
  checked proof-object row for the bad submodule scalar-closure conflict. The
  new SMT-LIB artifact records `1` present in the claimed subset, `2` absent,
  `2 * 1 = 2`, and the fixed scalar-closure membership claim; the shared UF
  resource regression requires a pure EUF `Evidence::UnsatAletheProof` and
  rechecks it independently.

- **Finite-ideals QF_UF/Alethe regressions landed.**
  [`finite-ideals-v0`](artifacts/examples/math/finite-ideals-v0/) now has a
  checked proof-object row for the bad ideal additive-closure conflict and a
  second checked proof-object row for quotient-ring representative congruence.
  The first SMT-LIB artifact records `2` present in the claimed subset, `4`
  absent, `2 + 2 = 4`, and the fixed additive-closure membership claim. The
  second records equal even-coset representatives, equal odd-coset
  representatives, and rejects unequal quotient addition results for those
  congruent representative choices. The shared UF resource regression requires
  pure EUF `Evidence::UnsatAletheProof` evidence and rechecks it independently.

- **Finite-tensor-products QF_UF/Alethe regression landed.**
  [`finite-tensor-products-v0`](artifacts/examples/math/finite-tensor-products-v0/)
  now has a checked proof-object row for the bad bilinear-map left-additivity
  conflict. The new SMT-LIB artifact records `10 + 01 = 11`,
  `beta(11,1) = 00`, `beta(10,1) = 10`, `beta(01,1) = 01`, and the fixed
  left-additivity equality; the shared UF resource regression requires a pure
  EUF `Evidence::UnsatAletheProof` and rechecks it independently.

- **Modular-arithmetic QF_LIA/Diophantine regression landed.**
  [`modular-arithmetic-v0`](artifacts/examples/math/modular-arithmetic-v0/)
  now has a checked proof-object row for the composite nonunit inverse
  obstruction. The new SMT-LIB artifact encodes `2*b == 1 mod 6` as
  `2*b - 6*k = 1`; the shared LIA resource regression requires
  `Evidence::UnsatDiophantine` and rechecks the gcd certificate independently.

- **Exact-statistical-tests QF_LIA/Diophantine regression landed.**
  [`exact-statistical-tests-v0`](artifacts/examples/math/exact-statistical-tests-v0/)
  now has a checked proof-object row for the bad binomial tail-count
  contradiction. The new SMT-LIB artifact encodes `C(4,3) = 4`, `C(4,4) = 1`,
  `tail_count = 4 + 1`, and `tail_count = 4`; the shared LIA resource
  regression requires `Evidence::UnsatDiophantine` and rechecks the integer
  certificate independently.

- **Finite-simplicial-homology QF_LIA/Diophantine regression landed.**
  [`finite-simplicial-homology-v0`](artifacts/examples/math/finite-simplicial-homology-v0/)
  now has a checked proof-object row for the bad boundary coefficient
  contradiction. The new SMT-LIB artifact encodes the `[a,c]` boundary
  coefficient as both `-1` and `1`; the shared LIA resource regression requires
  `Evidence::UnsatDiophantine` and rechecks the integer certificate
  independently.

- **Induction-patterns QF_LIA/Diophantine regression landed.**
  [`induction-patterns-v0`](artifacts/examples/math/induction-patterns-v0/)
  now has a checked proof-object row for the finite even-product parity
  obstruction. The new SMT-LIB artifact encodes the evaluated bad witness
  `6 * 7 = 42` and `2 * 20 + 1 = 41` as `product = 42` and `product = 41`;
  the shared LIA resource regression requires `Evidence::UnsatDiophantine`
  and rechecks the integer certificate independently.

- **Descriptive-statistics QF_LIA/Diophantine regression landed.**
  [`descriptive-statistics-v0`](artifacts/examples/math/descriptive-statistics-v0/)
  now has a checked proof-object row for the bad contingency total. The new
  SMT-LIB artifact encodes row sums `10` and `10`, `total = 10 + 10`, and the
  false claim `total = 19`; the shared LIA resource regression requires
  `Evidence::UnsatDiophantine` and rechecks the integer certificate
  independently.

- **Finite-probability QF_LRA/Farkas regression landed.**
  [`finite-probability-v0`](artifacts/examples/math/finite-probability-v0/)
  now has a checked proof-object row for bad normalization. The new SMT-LIB
  artifact encodes `heads = 1/2`, `tails = 1/2`, `total = heads + tails`, and
  the false claim `total = 3/2`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Finite-Markov-chain QF_LRA/Farkas regression landed.**
  [`finite-markov-chain-v0`](artifacts/examples/math/finite-markov-chain-v0/)
  now binds its bad stochastic-row rejection to Axeyum's evidence path. The new
  SMT-LIB artifact encodes `p10 = 1/3`, `p11 = 1/3`,
  `row_sum = p10 + p11`, and the false claim `row_sum = 1`; the shared LRA
  resource regression requires `Evidence::UnsatFarkas` and rechecks the
  rational certificate independently.

- **Finite-hitting-times QF_LRA/Farkas regression landed.**
  [`finite-hitting-times-v0`](artifacts/examples/math/finite-hitting-times-v0/)
  now binds its bad expected-time table to Axeyum's evidence path. The new
  SMT-LIB artifact encodes `h_start = 3`, `h_middle = 2`, and the
  denominator-cleared equation `2*h_start = 2 + h_start + h_middle`; the shared
  LRA resource regression requires `Evidence::UnsatFarkas` and rechecks the
  rational certificate independently.

- **Least-squares-regression QF_LRA/Farkas regression landed.**
  [`least-squares-regression-v0`](artifacts/examples/math/least-squares-regression-v0/)
  now binds its bad coefficient row to Axeyum's evidence path. The new SMT-LIB
  artifact encodes `beta0 = 1`, `beta1 = 1`, and the first failed normal
  equation `3*beta0 + 3*beta1 = 7`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Real-analysis-rational QF_LRA/Farkas regression landed.**
  [`real-analysis-rational-v0`](artifacts/examples/math/real-analysis-rational-v0/)
  now binds its bad linear-delta counterexample to Axeyum's evidence path. The
  new SMT-LIB artifact encodes `output_distance = 4/3` and the false claim
  `output_distance < 1`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Finite-conditional-expectation QF_LRA/Farkas regression landed.**
  [`finite-conditional-expectation-v0`](artifacts/examples/math/finite-conditional-expectation-v0/)
  now binds its bad high-block and tower-property tables to Axeyum's evidence
  path. The SMT-LIB artifacts encode `(1/2)*high_block_expectation = 3` with
  the false claim `high_block_expectation = 5`, and `tower_value = 7/2` with
  the false claim `tower_value = 4`; the shared LRA resource regressions
  require `Evidence::UnsatFarkas` and recheck the rational certificates
  independently.

- **Finite-Euler-method QF_LRA/Farkas regression landed.**
  [`finite-euler-method-v0`](artifacts/examples/math/finite-euler-method-v0/)
  now binds its bad fixed-step update to Axeyum's evidence path. The new
  SMT-LIB artifact encodes `state = 1`, `derivative = -1`,
  `next_state = state + (1/2)*derivative`, and the false claim
  `next_state = 3/4`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Finite-probability Bayes QF_LRA/Farkas regression landed.**
  [`finite-probability-v0`](artifacts/examples/math/finite-probability-v0/)
  now binds a bad diagnostic-test posterior to Axeyum's evidence path. The new
  SMT-LIB artifact encodes `(117/2000)*posterior = 9/1000` and the false claim
  `posterior = 1/5`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Orientation/area geometry QF_LRA/Farkas regression landed.**
  [`orientation-area-geometry-v0`](artifacts/examples/math/orientation-area-geometry-v0/)
  now binds its bad fixed-orientation row to Axeyum's evidence path. The new
  SMT-LIB artifact encodes `signed_double_area = -1` and the false claim
  `signed_double_area > 0`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Numerical-linear-algebra QF_LRA/Farkas regression landed.**
  [`numerical-linear-algebra-v0`](artifacts/examples/math/numerical-linear-algebra-v0/)
  now binds its bad residual-bound row to Axeyum's evidence path. The new
  SMT-LIB artifact encodes `residual_inf_norm = 1` and the false claim
  `residual_inf_norm <= 1/2`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Random-matrix-finite QF_LRA/Farkas regression landed.**
  [`random-matrix-finite-v0`](artifacts/examples/math/random-matrix-finite-v0/)
  now binds its bad trace-square moment row to Axeyum's evidence path. The new
  SMT-LIB artifact encodes `expected_trace_square = 2` and the false claim
  `expected_trace_square = 1`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Affine-geometry QF_LRA/Farkas regression landed.**
  [`affine-geometry-v0`](artifacts/examples/math/affine-geometry-v0/)
  now binds its bad midpoint-coordinate, collinearity-determinant, and
  distance-preservation rows to Axeyum's evidence path. The source SMT-LIB
  artifacts encode `image_midpoint_y = 4` versus `5`,
  `image_collinearity_determinant = 0` versus `1`, and
  `original_distance_squared = 1` versus `transformed_distance_squared = 5`
  with a false equality between them; the shared LRA resource regressions
  require `Evidence::UnsatFarkas` and recheck the rational certificates
  independently.

- **Inner-product-spaces QF_LRA/Farkas regression landed.**
  [`inner-product-spaces-rational-v0`](artifacts/examples/math/inner-product-spaces-rational-v0/)
  now binds its bad negative-norm row to Axeyum's evidence path. The new
  SMT-LIB artifact encodes `norm_square = -1` and the impossible positivity
  claim `norm_square > 0`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Spectral-linear-algebra QF_LRA/Farkas regression landed.**
  [`spectral-linear-algebra-v0`](artifacts/examples/math/spectral-linear-algebra-v0/)
  now binds its bad eigenpair row to Axeyum's evidence path. The new SMT-LIB
  artifact encodes the first component as `eigen_image_0 = 3` and the false
  claimed scaled component `eigen_image_0 = 2`; the shared LRA resource
  regression requires `Evidence::UnsatFarkas` and rechecks the rational
  certificate independently.

- **Matrix-invariants QF_LRA/Farkas regression landed.**
  [`matrix-invariants-v0`](artifacts/examples/math/matrix-invariants-v0/)
  now binds its bad characteristic-polynomial row to Axeyum's evidence path.
  The new SMT-LIB artifact encodes `characteristic_value_at_witness = 0` and
  the false value `characteristic_value_at_witness = 2`; the shared LRA
  resource regression requires `Evidence::UnsatFarkas` and rechecks the
  rational certificate independently.

- **Finite-stochastic-kernels QF_LRA/Farkas regression landed.**
  [`finite-stochastic-kernels-v0`](artifacts/examples/math/finite-stochastic-kernels-v0/)
  now binds its bad kernel-row normalization row to Axeyum's evidence path.
  The new SMT-LIB artifact encodes `rainy_walk = 3/5`, `rainy_bus = 3/5`,
  `rainy_row_sum = rainy_walk + rainy_bus`, and the false stochastic-kernel
  row claim `rainy_row_sum = 1`; the shared LRA resource regression requires
  `Evidence::UnsatFarkas` and rechecks the rational certificate independently.

- **Finite-calculus-shadows end-to-end lesson landed.** Added
  [`calculus-shadows-end-to-end.md`](docs/learn/math/calculus-shadows-end-to-end.md)
  as the combined learner-facing trace for the calculus-algebraic-shadow and
  calculus-Riemann-sum packs: polynomial derivative replay, product-rule and
  tangent checks, finite Riemann sums, antiderivative endpoint replay, checked
  false derivative/integral rejection, and the differentiability,
  integrability, and fundamental-theorem Lean horizons. The lesson is linked
  from the math learning index plus the analysis/topology path.

- **Sequence-limit-shadow end-to-end lesson landed.** Added
  [`sequence-limit-shadow-end-to-end.md`](docs/learn/math/sequence-limit-shadow-end-to-end.md)
  as the learner-facing trace for the sequence-limit-shadow pack: finite
  epsilon-tail replay, proposed-limit counterexample replay, monotone bounded
  prefix checks, geometric partial sums, finite Cauchy-tail enumeration, and
  the general limit Lean horizon. The lesson is linked from the math learning
  index plus the analysis/topology path.

- **Counting and pigeonhole end-to-end lesson landed.** Added
  [`counting-pigeonhole-end-to-end.md`](docs/learn/math/counting-pigeonhole-end-to-end.md)
  as the learner-facing trace for the counting pack: fixed permutation count,
  one Pascal-identity instance, finite pigeonhole enumeration, and the Boolean
  CNF/LRAT proof-upgrade route. The lesson is linked from the math learning
  index plus the graph/discrete and probability/statistics paths.

- **Graph d-separation end-to-end lesson landed.** Added
  [`graph-d-separation-end-to-end.md`](docs/learn/math/graph-d-separation-end-to-end.md)
  as the learner-facing trace for the graph-d-separation pack: finite
  active-chain replay, conditioned chain/fork blocking, unconditioned-collider
  blocking, descendant-opened collider replay, and the causal-identification
  proof horizon. The lesson is linked from the math learning index plus the
  graph/discrete and probability/statistics paths.

- **Graph-cut end-to-end lesson landed.** Added
  [`graph-cut-end-to-end.md`](docs/learn/math/graph-cut-end-to-end.md)
  as the learner-facing trace for the graph-cut pack: finite minimum-edge-cut
  and minimum-vertex-cut certificates, rejected one-cut claims, checked
  smaller-cut enumeration, and the general max-flow/min-cut theorem horizon.
  The lesson is linked from the math learning index plus the graph/discrete
  path.

- **Graph-matching end-to-end lesson landed.** Added
  [`graph-matching-end-to-end.md`](docs/learn/math/graph-matching-end-to-end.md)
  as the learner-facing trace for the graph-matching pack: finite matching
  witness replay, overlapping-edge rejection, augmenting-path flip replay,
  checked `K3` perfect-matching refutation, and the general matching-theory
  horizon. The lesson is linked from the math learning index plus the
  graph/discrete path.

- **Graph-search-runtime end-to-end lesson landed.** Added
  [`graph-search-runtime-end-to-end.md`](docs/learn/math/graph-search-runtime-end-to-end.md)
  as the learner-facing trace for the graph-search-runtime pack: finite BFS
  and DFS visited-node counter replay, shortcut-tail family checks, checked
  bad DFS-bound rejection, and the asymptotic graph-search runtime Lean
  horizon. The lesson is linked from the math learning index plus the
  graph/discrete path.

- **Graph-reachability end-to-end lesson landed.** Added
  [`graph-reachability-end-to-end.md`](docs/learn/math/graph-reachability-end-to-end.md)
  as the learner-facing trace for the graph-reachability pack: finite BFS
  shortest-distance replay, deterministic DFS traversal replay, checked
  disconnected no-path refutation, and edge-cut separation. The lesson is
  linked from the math learning index plus the graph/discrete path.

- **Generating-functions end-to-end lesson landed.** Added
  [`generating-functions-end-to-end.md`](docs/learn/math/generating-functions-end-to-end.md)
  as the learner-facing trace for the generating-functions pack: finite
  coefficient extraction, Cauchy product convolution, bounded Fibonacci
  generating-function prefix replay, checked bad Cauchy-product rejection, and
  the general generating-functions Lean horizon. The lesson is linked from the
  math learning index plus the algebra/number-theory, graph/discrete,
  rational/real algebra, and analysis/topology paths.

- **Learner/proof-upgrade dashboard landed.** Extended
  [`gen-foundational-dashboards.py`](scripts/gen-foundational-dashboards.py) to
  generate
  [`learner-proof-upgrade-dashboard.md`](docs/foundational-resources/generated/learner-proof-upgrade-dashboard.md)
  from math pack metadata, `expected.json` proof statuses, cookbook recipe
  links, and explicit `docs/learn/math` pack references. The normal
  foundational-resource gate now fails if this dashboard is stale. Current
  generated queue: 102 non-template packs, 102 focused learner links, 0 path-only
  links, 0 missing learner links, and 91 packs with non-checked proof rows.

- **Curriculum resource execution plan landed.** Added
  [`CURRICULUM-RESOURCE-EXECUTION-PLAN.md`](docs/foundational-resources/CURRICULUM-RESOURCE-EXECUTION-PLAN.md)
  as the forward plan for building the math-curriculum resources past broad
  validated packs: canonical status and coverage, learner-path completion,
  proof/certificate upgrades, concept granularity, solver feedback reuse, and
  eventual consumer/library boundaries. Linked it from the top-level plan,
  foundational-resources index, roadmap, and math buildout phase contract.

- **Math curriculum implementation matrix landed.** Added
  [`MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md`](docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md)
  as the detailed, commit-sized resource plan: R0-R6 acceptance gates,
  per-curriculum-node next work, per-field extension work, route-specific build
  sequences, and the next execution queue. Linked it from `PLAN.md`, the
  foundational-resources index, mdBook summary, roadmap, buildout plan, and
  execution plan. Next resource work should pick one row from that matrix and
  carry it through validation, status update, commit, and push.

- **Math curriculum detailed build ledger landed.** Added
  [`MATH-CURRICULUM-DETAILED-BUILD-PLAN.md`](docs/foundational-resources/MATH-CURRICULUM-DETAILED-BUILD-PLAN.md)
  as the execution ledger for the current 102-pack math resource surface. It
  records the baseline counts, the R0-R6 gate contract, build waves, the empty
  unclassified solver-reuse queue, field-by-field next steps, curriculum-node
  next steps, and a commit-sized queue. Next resource work should continue
  proof-route promotions, learner-page splits, or consumer-query examples from
  the ledger.

- **Math curriculum resource buildout roadmap landed.** Added
  [`RESOURCE-BUILDOUT-ROADMAP.md`](docs/foundational-resources/RESOURCE-BUILDOUT-ROADMAP.md)
  as the detailed operating plan for turning the curriculum and 18-field math
  taxonomy into ontology rows, example packs, learner pages, proof routes,
  solver-reuse artifacts, consumer boundaries, rules/law transfer, and future
  library splits. It now records the current committed baseline of 105 concept
  rows, 102 non-template packs, 516 expected checks, 222 checked rows, 229
  replay-only rows, 65 Lean-horizon rows, and 102 promoted solver-reuse packs,
  then lays out field-by-field build plans plus a prioritized execution queue.
  Linked it from
  `PLAN.md`, the foundational-resources index, mdBook summary, sibling-project
  notes, roadmap, buildout plan, implementation matrix, and execution plan.

- **Rules/law crosswalk landed.** Added
  [`RULES-LAW-CROSSWALK.md`](docs/foundational-resources/RULES-LAW-CROSSWALK.md)
  as the concrete transfer map from math resources into rule and policy
  checks. It maps finite predicates, sets/relations, integer thresholds,
  threshold cliffs, graph reachability, precedence/lattices, temporal versions,
  implementation equivalence, and proof routes to current packs and expected
  rule-check shapes. `benefit-eligibility-v0` is now explicitly tied to
  finite-sample replay plus checked Bool/QF_LIA proof-harness rows. The
  crosswalk is linked from the foundational-resource index, mdBook summary,
  rules-as-code README/roadmap, buildout roadmap, execution plan, and
  implementation matrix.

- **Benefit-eligibility Bool/QF_LIA fixtures landed.**
  [`benefit-eligibility-v0`](docs/rules-as-code/examples/benefit-eligibility-v0/README.md)
  now has source-linked SMT-LIB fixtures for consistency, coverage, fixed
  no-exception monotonicity, and active-threshold implementation equivalence:
  [`consistency-bool-qf-lia-conflict.smt2`](docs/rules-as-code/examples/benefit-eligibility-v0/smt2/consistency-bool-qf-lia-conflict.smt2),
  [`coverage-bool-qf-lia-conflict.smt2`](docs/rules-as-code/examples/benefit-eligibility-v0/smt2/coverage-bool-qf-lia-conflict.smt2),
  [`implementation-equivalence-bool-qf-lia-conflict.smt2`](docs/rules-as-code/examples/benefit-eligibility-v0/smt2/implementation-equivalence-bool-qf-lia-conflict.smt2),
  and
  [`monotonicity-bool-qf-lia-conflict.smt2`](docs/rules-as-code/examples/benefit-eligibility-v0/smt2/monotonicity-bool-qf-lia-conflict.smt2).
  The new
  [`rules_as_code_examples`](crates/axeyum-solver/tests/rules_as_code_examples.rs)
  regression parses all four obligations, requires `Unsat`, and accepts only
  certified evidence that independently rechecks with `Evidence::check`. The
  rules validator now enforces the artifact paths, citation labels, regression
  names, checked-evidence contract, and generated multi-row query replay.
  Next work is another rule-pack family or promoting selected generated query
  rows into executable fixture corpora when a downstream consumer needs them.

- **Authorization-policy rules/law pack landed.**
  [`authorization-policy-v0`](docs/rules-as-code/examples/authorization-policy-v0/README.md)
  is the second rules-as-code pack and reuses finite predicates,
  tenant/resource relations, precedence, bounded version deltas, and
  implementation-equivalence checks. The pack has source-linked Bool/QF_LIA
  fixtures for
  [`tenant-isolation-bool-qf-lia-conflict.smt2`](docs/rules-as-code/examples/authorization-policy-v0/smt2/tenant-isolation-bool-qf-lia-conflict.smt2),
  [`explicit-deny-precedence-bool-qf-lia-conflict.smt2`](docs/rules-as-code/examples/authorization-policy-v0/smt2/explicit-deny-precedence-bool-qf-lia-conflict.smt2),
  [`admin-tenant-guard-bool-qf-lia-conflict.smt2`](docs/rules-as-code/examples/authorization-policy-v0/smt2/admin-tenant-guard-bool-qf-lia-conflict.smt2),
  and
  [`implementation-equivalence-bool-qf-lia-conflict.smt2`](docs/rules-as-code/examples/authorization-policy-v0/smt2/implementation-equivalence-bool-qf-lia-conflict.smt2).
  The `rules_as_code_examples` regression now checks all four authorization
  obligations with certified evidence, and
  [`validate-rules-as-code.py`](scripts/validate-rules-as-code.py) now discovers
  and validates multiple rules-as-code packs with pack-specific finite replay.

- **R1 bridge-concept atlas rows expanded.**
  [`foundational-concepts.json`](artifacts/ontology/foundational-concepts.json)
  is now generated with 59 bridge rows. The proof-methodology rows are
  `bridge_finite_model_replay`, `bridge_counterexample_proof`,
  `bridge_refutation_query`, `bridge_finite_proof_pattern`,
  `bridge_finite_quantifier_expansion`,
  `bridge_bounded_induction_obligation`, `bridge_bounded_theorem_shadow`, and
  `bridge_lean_horizon`; the proof-object anatomy rows are
  `bridge_boolean_cnf_lrat_anatomy`, `bridge_qf_lra_farkas_anatomy`,
  `bridge_qf_uf_alethe_anatomy`, and `bridge_qf_bv_bitblast_anatomy`; the
  number-system semantic-boundary rows are
  `bridge_exact_vs_floating_arithmetic` and
  `bridge_totality_conventions`, which make exact rational replay,
  floating-point/numerical-honesty boundaries, SMT totality, explicit side
  conditions, and frontend trapping/UB boundaries queryable; the
  gcd/divisibility row is `bridge_gcd_divisibility_witness`, making
  gcd/common-divisor replay, Bezout replay, quotient witnesses, modular
  nonunit obstructions, and checked gcd non-divisibility certificates
  queryable; the modular row is `bridge_modular_crt_inverse_witness`, making
  concrete CRT congruence witnesses, modular inverse witnesses, fixed residue
  searches, finite-field unit/nonunit contrasts, and checked nonunit
  Diophantine evidence queryable; the finite-counting row is
  `bridge_finite_counting_replay`, making permutation/Pascal rows, pigeonhole
  proof routes, double-counting tables, coefficient extraction, finite orbit
  counts, and exact finite tail-count contradictions queryable; the finite
  graph row is `bridge_finite_graph_replay_obstruction`, making coloring,
  reachability/traversal, matching, cut, and d-separation resources queryable
  across finite replay, Bool/CNF, QF_BV, and QF_LIA routes; the finite
  dynamics row is `bridge_finite_dynamics_euler_replay`, making finite
  recurrence-prefix, bounded-dynamics, explicit-Euler, invariant, threshold,
  and finite-error rows queryable across finite replay and QF_LRA/Farkas
  routes; the
  optimization/convexity rows are `bridge_lp_objective_farkas` and
  `bridge_rational_convexity_shadow`; the
  set/foundations rows are `bridge_finite_boolean_algebra`,
  `bridge_partition_relation_roundtrip`,
  `bridge_finite_image_preimage_inverse`,
  `bridge_finite_bijection_cardinality`, and
  `bridge_cardinality_theorem_horizon`; the analysis and topology boundary
  rows are `bridge_metric_ball`,
  `bridge_bounded_epsilon_delta_shadow`, `bridge_compactness_shadow`,
  `bridge_connectedness_shadow`, `bridge_continuity_preimage`, and
  `bridge_finite_topology_operator_homeomorphism`,
  `bridge_finite_boundary_operator_replay`, and
  `bridge_finite_chain_homology_replay`; the
  linear-algebra computation rows are `bridge_lu_replay`,
  `bridge_rank_nullity`, `bridge_residual_bound`, `bridge_eigenpair`,
  `bridge_characteristic_polynomial`, and
  `bridge_random_matrix_finite_moment`; the probability/statistics table rows
  are `bridge_finite_measure_additivity`,
  `bridge_probability_mass_table`, `bridge_pushforward_distribution`,
  `bridge_stochastic_kernel`, `bridge_conditional_expectation`,
  `bridge_finite_product_integration`, and
  `bridge_tail_count_obstruction`; the algebra-map rows are
  `bridge_homomorphism_preservation`, `bridge_kernel_image`,
  `bridge_quotient_map`, `bridge_ideal_closure`, `bridge_module_action`,
  `bridge_tensor_bilinearity`, and `bridge_group_action`. The rows are
  generated from
  [`gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py) and
  point at existing validated packs plus proof-cookbook recipes. The
  geometry/complex bridge rows now add
  `bridge_coordinate_orientation_geometry`,
  `bridge_finite_circle_inversion_cyclic_replay`, and
  `bridge_complex_real_pair_transform`, grouping finite coordinate, affine,
  oriented-area, circle, inversion, cyclic-configuration, and complex real-pair
  transform replay without overclaiming synthetic, differential, global, or
  analytic theorem coverage.
  The functional-analysis bridge rows now add
  `bridge_inner_product_projection` and
  `bridge_finite_operator_chebyshev`, grouping finite Gram/projection,
  operator-bound, interpolation, and Chebyshev-grid replay without
  overclaiming Banach, Hilbert, compact-operator, minimax, or
  infinite-dimensional approximation theorems. The measure-theory bridge rows
  now add finite event-algebra, additivity, complement, product-table,
  marginal, finite Fubini-style sum, and simple-function integral replay while
  keeping Lebesgue, convergence, and almost-everywhere theorems as Lean
  horizons. The optimization/convexity bridge rows now add LP feasibility,
  objective-threshold Farkas replay, finite midpoint/Jensen shadows, affine
  monotonicity, gradient replay, Hessian-minor witnesses, least-squares
  normal-equation replay, finite root-finding, and finite hyperplane
  separation, plus finite KKT stationarity/complementarity replay, finite SDP
  objective/slack replay, finite gradient-descent replay, finite line-search
  replay, finite projected-gradient interval/decrease replay, and
  finite proximal-gradient replay
  while keeping duality, KKT sufficiency, SDP strong duality, general
  separation, projected-gradient convergence, proximal-gradient convergence,
  and convergence theorems as Lean horizons. The
  foundational resource consumer now reports 105 concept rows while
  preserving 23 curriculum rows and 18 field rows. Next resource work should
  add the next proof-frontier promotion or boundary evidence from a real
  repeated consumer, depending on which roadmap lane is being advanced.

- **Proof-cookbook math examples landed.** The six active route recipes now
  include `Math Examples Using This Route` sections that point to concrete
  resource packs: Boolean CNF/LRAT, QF_BV bit-blast, QF_LIA/Diophantine,
  QF_LRA/Farkas, QF_UF/Alethe, and Lean horizons. The examples name the exact
  finite-math rows each route should carry and keep bounded replay, certificate
  evidence, and Lean-horizon claims separate.

- **High-use learner proof-route notes landed.** Added concise
  `Proof Upgrade Notes` sections to
  [`logic-and-proof.md`](docs/learn/math/logic-and-proof.md),
  [`graph-and-discrete-reasoning.md`](docs/learn/math/graph-and-discrete-reasoning.md),
  [`linear-algebra-and-optimization.md`](docs/learn/math/linear-algebra-and-optimization.md),
  [`probability-and-statistics.md`](docs/learn/math/probability-and-statistics.md),
  and [`algebra-and-number-theory.md`](docs/learn/math/algebra-and-number-theory.md).
  The notes map finite replay, CNF/LRAT, QF_BV/DRAT, QF_LIA/Diophantine,
  QF_LRA/Farkas, QF_UF/Alethe, and Lean-horizon routes to the pack families
  actually shown on each page. Next resource work can turn recurring Farkas or
  Alethe patterns into reusable example families, or promote selected
  resource-backed rows into solver regression corpora.

- **Finite-algebra Alethe example-family row landed.**
  [`foundational-concepts.json`](artifacts/ontology/foundational-concepts.json)
  now includes `family_finite_algebra_alethe`, the first generated
  `example-family` row. It groups the recurring finite algebra/function-table
  QF_UF conflicts across equivalence classes, relations/functions, finite
  groups, function composition, homomorphisms, monoids, order lattices,
  permutation groups, vector/dual/module/ideal/tensor packs, and ties the
  family to the checked
  [`math_resource_uf_routes`](crates/axeyum-solver/tests/math_resource_uf_routes.rs)
  regression. The row is scoped to `abstract_algebra` to avoid broad
  cross-field dashboard pollution; field dashboards now show the family as a
  validated decidable algebra row.

- **Exact-rational Farkas example-family row landed.**
  [`foundational-concepts.json`](artifacts/ontology/foundational-concepts.json)
  now includes `family_exact_rational_farkas`, a generated `example-family`
  row for recurring exact-rational QF_LRA/Farkas contradictions across
  rationals, linear algebra, LP thresholds, convexity, probability,
  Markov/hitting-time equations, regression, real-analysis bounds, Euler
  steps, affine/orientation geometry, numerical residuals, random matrices,
  inner products, spectral rows, matrix invariants, and stochastic-kernel row
  normalization. The row is tied to
  [`math_resource_lra_routes`](crates/axeyum-solver/tests/math_resource_lra_routes.rs),
  which requires `Evidence::UnsatFarkas`, independently rechecks the evidence,
  and records the certified Farkas trust step. It is scoped to
  `optimization_and_convexity` as the LP/Farkas proof-route lane rather than
  claiming full subject-field coverage for every referenced pack.

- **Boolean CNF/LRAT example-family row landed.**
  [`foundational-concepts.json`](artifacts/ontology/foundational-concepts.json)
  now includes `family_boolean_cnf_lrat`, a generated `example-family` row for
  recurring finite Boolean refutations across logic, proof methods, counting,
  finite predicates, finite sets, finite cardinality, graph, and finite
  topology packs. The row is tied to
  [`math_resource_boolean_routes`](crates/axeyum-cnf/tests/math_resource_boolean_routes.rs),
  which parses the committed DIMACS artifacts, emits DRAT, elaborates LRAT,
  checks both proof objects, and rejects corrupted proof hints. It is scoped to
  the fields where the Boolean encoding is part of the educational proof route,
  not as a broad claim about graph or topology theorem coverage.

- **Integer Diophantine example-family row landed.**
  [`foundational-concepts.json`](artifacts/ontology/foundational-concepts.json)
  now includes `family_integer_diophantine`, a generated `example-family` row
  for recurring integer equalities, count contradictions, coefficient
  obstructions, bounded arithmetic claims, and checked arithmetic-evidence rows across
  modular arithmetic, gcd/Bezout, integer and natural arithmetic, induction,
  cardinality, generating functions, polynomial identities, statistics,
  finite homology, and graph-search runtime packs. The row is tied to
  [`math_resource_lia_routes`](crates/axeyum-solver/tests/math_resource_lia_routes.rs),
  which parses committed SMT-LIB artifacts and requires either
  `UnsatDiophantine` or checked QF_LIA arithmetic evidence before accepting the
  row.

- **Fixed-width QF_BV/DRAT example-family row landed.**
  [`foundational-concepts.json`](artifacts/ontology/foundational-concepts.json)
  now includes `family_fixed_width_bv_drat`, a generated `example-family` row
  for fixed-width finite algebra, residue, and one-bit graph contradictions
  across finite fields, finite rings, graph coloring, and bounded
  number-theory residue search/bad-witness packs. The row is tied to
  [`math_resource_bv_routes`](crates/axeyum-solver/tests/math_resource_bv_routes.rs),
  which parses committed SMT-LIB artifacts, exports DIMACS/DRAT witnesses,
  rechecks the proof route, and rejects truncated DRAT certificates.

- **Generated R0-R6 gate columns landed.**
  [`gen-foundational-dashboards.py`](scripts/gen-foundational-dashboards.py)
  now derives conservative acceptance-gate levels and next gates for concept
  rows and example packs. The generated coverage, field, proof-gap, and
  learner/proof-upgrade dashboards now expose `Gate` / `Next Gate` columns so
  the resource lane can distinguish row-level R4 proof/evidence coverage from
  pack-level R6 consumer-boundary rows that already have source-linked solver
  regressions. The current pack split is 52 `R6 consumer boundary` rows and
  32 `R4 checked evidence` rows, making solver-reuse state explicit.

- **Structured solver-reuse candidate tags landed.**
  [`foundational-example-pack.schema.json`](artifacts/ontology/foundational-example-pack.schema.json)
  now admits an optional `solver_reuse` metadata object with status, target,
  pressure, evidence rows, and next step. The example-pack validator checks
  that candidate evidence points only at deterministic checked/replay rows.
  The first candidate batch now has no remaining `candidate` rows.
  Generated dashboards show 10 `promoted` rows for `logic-basics-v0`,
  `finite-cardinality-v0`, `graph-matching-v0`, `graph-reachability-v0`,
  `graph-cut-v0`, `graph-d-separation-v0`, `graph-search-runtime-v0`, and
  `integer-lia-v0`, `natural-arithmetic-v0`, and `number-theory-v0`.

- **First solver-reuse candidate promoted: logic basics.**
  [`logic-basics-v0`](artifacts/examples/math/logic-basics-v0/) now has a
  source-linked DIMACS artifact for `tiny-cnf-refutation`:
  [`tiny-cnf-refutation.cnf`](artifacts/examples/math/logic-basics-v0/cnf/tiny-cnf-refutation.cnf).
  [`math_resource_boolean_routes.rs`](crates/axeyum-cnf/tests/math_resource_boolean_routes.rs)
  parses that artifact, emits DRAT, elaborates to LRAT, and independently
  checks both proof objects. The pack metadata now marks `solver_reuse.status`
  as `promoted` for that row only; the validator enforces the artifact path,
  exact DIMACS shape, regression name, and DRAT/LRAT trust-boundary note.

- **Second solver-reuse candidate promoted: finite cardinality.**
  [`finite-cardinality-v0`](artifacts/examples/math/finite-cardinality-v0/) now
  has a source-linked DIMACS artifact for `no-injection-four-to-three`:
  [`no-injection-four-to-three.cnf`](artifacts/examples/math/finite-cardinality-v0/cnf/no-injection-four-to-three.cnf).
  The same Boolean resource regression parses the 4-into-3 injective-function
  CNF, emits DRAT, elaborates to LRAT, and independently checks both proof
  objects. The pack metadata now marks `solver_reuse.status` as `promoted` for
  that row only; the validator enforces the fixed 4-into-3 DIMACS shape,
  regression name, and DRAT/LRAT trust-boundary note.

- **Third solver-reuse candidate promoted: graph matching.**
  [`graph-matching-v0`](artifacts/examples/math/graph-matching-v0/) now has a
  source-linked DIMACS artifact for `triangle-no-perfect-matching`:
  [`triangle-no-perfect-matching.cnf`](artifacts/examples/math/graph-matching-v0/cnf/triangle-no-perfect-matching.cnf).
  The shared Boolean resource regression parses the `K3` exact-cover
  contradiction, emits DRAT, elaborates to LRAT, and independently checks both
  proof objects. The pack metadata now marks `solver_reuse.status` as
  `promoted` for that row only; the validator enforces the fixed `K3` DIMACS
  shape, regression name, and DRAT/LRAT trust-boundary note.

- **Fourth solver-reuse candidate promoted: graph reachability.**
  [`graph-reachability-v0`](artifacts/examples/math/graph-reachability-v0/)
  now has a source-linked DIMACS artifact for `disconnected-no-path`:
  [`disconnected-no-path.cnf`](artifacts/examples/math/graph-reachability-v0/cnf/disconnected-no-path.cnf).
  The shared Boolean resource regression parses the bounded reachability
  fixed-point contradiction for the disconnected `s-a` / `b-t` graph, emits
  DRAT, elaborates to LRAT, and independently checks both proof objects. The
  pack metadata now marks `solver_reuse.status` as `promoted` for that row
  only; the validator enforces the fixed graph, depth bound, DIMACS shape,
  regression name, and DRAT/LRAT trust-boundary note.

- **Fifth solver-reuse candidate promoted: graph cuts.**
  [`graph-cut-v0`](artifacts/examples/math/graph-cut-v0/) now has a
  source-linked DIMACS artifact for `one-edge-cut-rejected`:
  [`one-edge-cut-rejected.cnf`](artifacts/examples/math/graph-cut-v0/cnf/one-edge-cut-rejected.cnf).
  The shared Boolean resource regression parses the bounded post-removal
  reachability contradiction for the diamond graph after removing `(s,a)`,
  emits DRAT, elaborates to LRAT, and independently checks both proof objects.
  The pack metadata now marks `solver_reuse.status` as `promoted` for that row
  only; the validator enforces the fixed graph, removed edge, depth bound,
  DIMACS shape, regression name, and DRAT/LRAT trust-boundary note.

- **Sixth solver-reuse candidate promoted: graph d-separation.**
  [`graph-d-separation-v0`](artifacts/examples/math/graph-d-separation-v0/)
  now has a source-linked DIMACS artifact for `chain-conditioned-blocks`:
  [`chain-conditioned-blocks.cnf`](artifacts/examples/math/graph-d-separation-v0/cnf/chain-conditioned-blocks.cnf).
  The shared Boolean resource regression parses the conditioned non-collider
  blocking contradiction for the fixed chain `a -> b -> c | b`, emits DRAT,
  elaborates to LRAT, and independently checks both proof objects. The pack
  metadata now marks `solver_reuse.status` as `promoted` for that row only; the
  validator enforces the fixed chain, conditioning set, DIMACS shape,
  regression name, and DRAT/LRAT trust-boundary note.

- **Seventh solver-reuse candidate promoted: graph search runtime.**
  [`graph-search-runtime-v0`](artifacts/examples/math/graph-search-runtime-v0/)
  now has a source-linked SMT-LIB artifact for `bad-dfs-cost-bound-rejected`:
  [`bad-dfs-cost-bound-lia-conflict.smt2`](artifacts/examples/math/graph-search-runtime-v0/smt2/bad-dfs-cost-bound-lia-conflict.smt2).
  The shared LIA resource regression parses the fixed length-four
  shortcut-tail DFS cost conflict, requires checked QF_LIA arithmetic evidence,
  and independently rechecks the proof object. The pack metadata now marks
  `solver_reuse.status` as `promoted` for that row only; the validator enforces
  the fixed tail length, traversal counts, SMT-LIB artifact path, regression
  name, and checked-arithmetic trust-boundary note.

- **Eighth solver-reuse candidate promoted: integer LIA.**
  [`integer-lia-v0`](artifacts/examples/math/integer-lia-v0/) now has a
  source-linked SMT-LIB artifact for `diophantine-gcd-obstruction`:
  [`diophantine-gcd-obstruction-conflict.smt2`](artifacts/examples/math/integer-lia-v0/smt2/diophantine-gcd-obstruction-conflict.smt2).
  The shared LIA resource regression parses the fixed `2*x + 4*y = 3`
  Diophantine obstruction, requires checked `UnsatDiophantine` evidence, and
  independently rechecks the certificate. The pack metadata now marks
  `solver_reuse.status` as `promoted` for that row only; the validator enforces
  the fixed coefficients, target, SMT-LIB artifact path, regression name, and
  Diophantine trust-boundary note.

- **Ninth solver-reuse candidate promoted: natural arithmetic.**
  [`natural-arithmetic-v0`](artifacts/examples/math/natural-arithmetic-v0/)
  now has a source-linked SMT-LIB artifact for
  `bounded-natural-negative-rejected`:
  [`bounded-natural-negative-lia-conflict.smt2`](artifacts/examples/math/natural-arithmetic-v0/smt2/bounded-natural-negative-lia-conflict.smt2).
  The shared LIA resource regression parses the fixed `0 <= n <= 7` plus
  `n < 0` contradiction, requires checked QF_LIA arithmetic evidence, and
  independently rechecks the proof object. The pack metadata now marks
  `solver_reuse.status` as `promoted` for that row only; the validator enforces
  the fixed bound, SMT-LIB artifact path, regression name, and checked-arithmetic
  trust-boundary note.

- **Tenth solver-reuse candidate promoted: number theory.**
  [`number-theory-v0`](artifacts/examples/math/number-theory-v0/) now has a
  source-linked SMT-LIB artifact for `quadratic-nonresidue-qf-bv-drat`:
  [`quadratic-nonresidue-mod7-bitblast-conflict.smt2`](artifacts/examples/math/number-theory-v0/smt2/quadratic-nonresidue-mod7-bitblast-conflict.smt2).
  The shared BV resource regression parses the fixed 3-bit residue equation
  `x < 7` and `x^2 mod 7 = 3`, proves it `unsat`, exports the bit-blasted
  DIMACS plus DRAT refutation, and independently rechecks the certificate. The
  pack metadata now marks `solver_reuse.status` as `promoted` for that row only;
  the validator enforces the prime modulus, residue, width bounds, SMT-LIB
  artifact path, regression name, and bit-blast/Tseitin trust-boundary note.

- **Consumer-facing foundational-resource queries landed.**
  [`query-foundational-resources.py`](scripts/query-foundational-resources.py)
  is a dependency-free read-only consumer over the committed atlas,
  `metadata.json`, and `expected.json` data contract. It supports `summary`,
  `packs`, `checks`, `concepts`, and `fields` queries for pack discovery,
  checked-row mining, field-plus-proof-route discovery, solver-reuse rows,
  atlas concept lookup, and curriculum field-readiness summaries, with examples in
  [`CONSUMER-QUERIES.md`](docs/foundational-resources/CONSUMER-QUERIES.md).
  `check-foundational-resources.sh` now runs a small query smoke set for
  summary output, promoted solver-reuse rows, probability/Farkas route pack
  discovery, graph-theory UNSAT rows, example-family atlas rows, and
  probability/Farkas, dynamics/Farkas, and measure/Farkas field-readiness rows,
  plus measure bridge concept lookup and checked measure-theory Farkas rows.

- **Foundational example-pack negative fixtures landed.**
  [`check-foundational-negative-fixtures.py`](scripts/check-foundational-negative-fixtures.py)
  now requires three intentionally invalid example-pack fixtures under
  [`artifacts/fixtures/foundational-example-pack-invalid/`](artifacts/fixtures/foundational-example-pack-invalid/)
  to fail for the expected reasons: unknown `field_ids`,
  `metadata.expected_results` drift from `expected.json`, and check rows that
  cite missing witnesses. The normal
  [`check-foundational-resources.sh`](scripts/check-foundational-resources.sh)
  gate runs the negative-fixture check after validating the real math packs.

- **First QF_BV resource proof-route row landed.**
  [`finite-rings-v0`](artifacts/examples/math/finite-rings-v0/) now has a
  source-linked SMT-LIB artifact for its bad distributivity row:
  [`non-distributive-table-bitblast-conflict.smt2`](artifacts/examples/math/finite-rings-v0/smt2/non-distributive-table-bitblast-conflict.smt2).
  The new `math_resource_bv_routes` regression parses it, proves it `unsat`,
  exports the bit-blasted DIMACS plus DRAT refutation, and rechecks the
  certificate. The pack validator now enforces the concrete table
  counterexample, artifact path, regression command, and bit-blast/Tseitin
  trust-boundary note. Next QF_BV resource targets are `finite-fields-v0` and
  the BV side of `graph-coloring-v0`.

- **Second QF_BV resource proof-route row landed.**
  [`finite-fields-v0`](artifacts/examples/math/finite-fields-v0/) now has a
  source-linked SMT-LIB artifact for the composite-modulus no-inverse row:
  [`composite-modulus-nonfield-bitblast-conflict.smt2`](artifacts/examples/math/finite-fields-v0/smt2/composite-modulus-nonfield-bitblast-conflict.smt2).
  The same `math_resource_bv_routes` regression now also parses the finite-field
  artifact, proves the 3-bit residue inverse equation `unsat`, exports the
  bit-blasted DIMACS plus DRAT refutation, and rechecks the certificate. The
  pack validator enforces the modulus/element, exact product-width encoding,
  artifact path, regression command, and bit-blast/Tseitin trust-boundary note.
  Next QF_BV resource target is the BV side of `graph-coloring-v0` where it
  adds a distinct fixed-width educational claim beyond the existing CNF/LRAT
  route.

- **QF_BV first-target resource set covered.**
  [`graph-coloring-v0`](artifacts/examples/math/graph-coloring-v0/) now has a
  source-linked SMT-LIB artifact for the one-bit triangle two-coloring
  obstruction:
  [`triangle-not-2-colorable-bitblast-conflict.smt2`](artifacts/examples/math/graph-coloring-v0/smt2/triangle-not-2-colorable-bitblast-conflict.smt2).
  The `math_resource_bv_routes` regression now checks finite-rings,
  finite-fields, and graph-coloring QF_BV resource artifacts by parsing each
  SMT-LIB file, proving it `unsat`, exporting the bit-blasted DIMACS plus DRAT
  refutation, and rechecking the certificate. The validator enforces the K3
  two-color data, one-bit encoding, artifact path, regression command, and
  bit-blast/Tseitin trust-boundary note. The first QF_BV proof-frontier target
  set is now covered; continue with fixed-width BV promotions only when the
  encoding teaches a distinct finite-domain claim.

- **Bounded number-theory QF_BV resource row landed.**
  [`number-theory-v0`](artifacts/examples/math/number-theory-v0/) now extends
  the QF_BV resource lane with a fixed modulo-7 quadratic nonresidue artifact:
  [`quadratic-nonresidue-mod7-bitblast-conflict.smt2`](artifacts/examples/math/number-theory-v0/smt2/quadratic-nonresidue-mod7-bitblast-conflict.smt2).
  The `math_resource_bv_routes` regression now has four cases: finite rings,
  finite fields, graph coloring, and bounded number theory. The candidate
  query now returns no rows, so the foundational-resource smoke test requires a
  promoted row instead.

- **Finite Chebyshev-system Farkas promotion landed.**
  [`finite-chebyshev-systems-v0`](artifacts/examples/math/finite-chebyshev-systems-v0/)
  now has a source-linked SMT-LIB artifact for the duplicate-node determinant
  conflict:
  [`bad-duplicate-node-grid-farkas-conflict.smt2`](artifacts/examples/math/finite-chebyshev-systems-v0/smt2/bad-duplicate-node-grid-farkas-conflict.smt2).
  The `math_resource_lra_routes` regression checks the exact rational
  contradiction `determinant = 0` and `determinant = 1` with
  `Evidence::UnsatFarkas` plus independent `Evidence::check` rechecking. The
  pack metadata marks `solver_reuse.status` as `promoted`.

- **Metric-continuity Farkas promotion landed.**
  [`metric-continuity-v0`](artifacts/examples/math/metric-continuity-v0/)
  now has a source-linked SMT-LIB artifact for the finite metric-space
  bad-delta output-bound conflict:
  [`bad-delta-farkas-conflict.smt2`](artifacts/examples/math/metric-continuity-v0/smt2/bad-delta-farkas-conflict.smt2).
  The `math_resource_lra_routes` regression checks the exact rational
  contradiction `output_distance = 1` and `output_distance < 1` with
  `Evidence::UnsatFarkas` plus independent `Evidence::check` rechecking. The
  pack metadata marks `solver_reuse.status` as `promoted`.

- **Finite-compactness Boolean proof promotion landed.**
  [`finite-compactness-v0`](artifacts/examples/math/finite-compactness-v0/)
  now has a source-linked DIMACS artifact for the bad open-cover row:
  [`bad-open-cover-rejected.cnf`](artifacts/examples/math/finite-compactness-v0/cnf/bad-open-cover-rejected.cnf).
  The `math_resource_boolean_routes` regression checks the one-variable
  contradiction `c_covered = false` and `c_covered = true` by emitting DRAT,
  elaborating to LRAT, and independently checking both proof objects. The pack
  metadata marks `solver_reuse.status` as `promoted`.

- **Finite-connectedness Boolean proof promotion landed.**
  [`finite-connectedness-v0`](artifacts/examples/math/finite-connectedness-v0/)
  now has a source-linked DIMACS artifact for the bad connectedness row:
  [`bad-connected-claim-rejected.cnf`](artifacts/examples/math/finite-connectedness-v0/cnf/bad-connected-claim-rejected.cnf).
  The `math_resource_boolean_routes` regression checks the one-variable
  contradiction `no_nontrivial_clopen = false` and
  `no_nontrivial_clopen = true` by emitting DRAT, elaborating to LRAT, and
  independently checking both proof objects. The pack metadata marks
  `solver_reuse.status` as `promoted`; generated resource summary now reports
  `solver_reuse=promoted:14,unclassified:70`.

- **Finite-Markov-chain end-to-end lesson landed.** Added
  [`finite-markov-chain-end-to-end.md`](docs/learn/math/finite-markov-chain-end-to-end.md)
  as the learner-facing trace for the finite-Markov-chain pack: exact
  row-stochastic transition matrices, finite-horizon distribution replay,
  stationary distributions, replayed bad transition-row and stationary
  distribution rejections, separate checked QF_LRA/Farkas scalar refutations,
  and the
  Markov-chain convergence Lean horizon. The lesson is linked from the math
  learning index plus the probability/statistics and analysis/dynamics paths.

- **Finite-concentration end-to-end lesson landed.** Added
  [`finite-concentration-end-to-end.md`](docs/learn/math/finite-concentration-end-to-end.md)
  as the learner-facing trace for the finite-concentration pack: exact finite
  Markov, Chebyshev, and union-bound replay over rational atom tables, checked
  bad concentration-bound rejection, and the general concentration Lean
  horizon. The lesson is linked from the math learning index plus the
  probability/statistics path.

- **Finite-hitting-times end-to-end lesson landed.** Added
  [`finite-hitting-times-end-to-end.md`](docs/learn/math/finite-hitting-times-end-to-end.md)
  as the learner-facing trace for the finite-hitting-times pack: finite
  absorbing-chain first-hit distributions, survival mass, absorption
  equations, expected hitting-time equations, checked bad expected-time
  rejection, and the general hitting-theory Lean horizon. The lesson is linked
  from the math learning index plus the probability/statistics and
  analysis/dynamics paths.

- **Finite-stochastic-kernels end-to-end lesson landed.** Added
  [`finite-stochastic-kernels-end-to-end.md`](docs/learn/math/finite-stochastic-kernels-end-to-end.md)
  as the learner-facing trace for the finite-stochastic-kernels pack:
  row-normalized finite kernels, pushforward distributions, joint
  factorization/disintegration, kernel composition, replayed malformed
  kernel-row/composed-entry rejections, separate checked QF_LRA/Farkas
  proof-object rows, and the regular-conditional-probability Lean horizon. The
  lesson is linked from the math learning index plus the probability/statistics
  path.

- **Finite-martingales end-to-end lesson landed.** Added
  [`finite-martingales-end-to-end.md`](docs/learn/math/finite-martingales-end-to-end.md)
  as the learner-facing trace for the finite-martingales pack: finite
  filtrations, adaptedness, martingale conditional-expectation equalities,
  square-submartingale inequalities, bounded stopping replay, checked bad
  martingale rejection, and the general martingale Lean horizon. The lesson is
  linked from the math learning index plus the probability/statistics path.

- **Finite-conditional-expectation end-to-end lesson landed.** Added
  [`finite-conditional-expectation-end-to-end.md`](docs/learn/math/finite-conditional-expectation-end-to-end.md)
  as the learner-facing trace for the finite-conditional-expectation pack:
  finite conditioning partitions, blockwise conditional expectations, total
  expectation replay, tower-property replay, checked bad table and bad
  tower-property rejection, and the general conditional-expectation Lean
  horizon. The lesson is linked from the math learning index plus the
  probability/statistics path.

- **Finite-random-variables end-to-end lesson landed.** Added
  [`finite-random-variables-end-to-end.md`](docs/learn/math/finite-random-variables-end-to-end.md)
  as the learner-facing trace for the finite-random-variables pack:
  finite random-variable functions, pushforward distributions, expectation
  through pushforwards, finite independence, bad pushforward rejection, and the
  general random-variable Lean horizon. The lesson is
  linked from the math learning index plus the probability/statistics path.

- **Finite-product-measure end-to-end lesson landed.** Added
  [`finite-product-measure-end-to-end.md`](docs/learn/math/finite-product-measure-end-to-end.md)
  as the learner-facing trace for the finite-product-measure pack:
  Cartesian-product probability tables, rectangle probabilities, marginals,
  finite Fubini replay, checked bad product-probability rejection, and the
  Fubini/Tonelli Lean horizon. The lesson is linked from the math learning
  index plus the probability/statistics and analysis/topology paths.

- **Finite-integration end-to-end lesson landed.** Added
  [`finite-integration-end-to-end.md`](docs/learn/math/finite-integration-end-to-end.md)
  as the learner-facing trace for the finite-integration pack: finite
  simple-function integrals, indicator integrals, integral linearity, checked
  bad-expectation rejection, and the Lebesgue-integration Lean horizon. The
  lesson is linked from the math learning index plus the probability/statistics
  and analysis/topology paths.

- **Finite simplicial-homology end-to-end lesson landed.** Added
  [`finite-simplicial-homology-end-to-end.md`](docs/learn/math/finite-simplicial-homology-end-to-end.md)
  as the learner-facing trace for the finite-simplicial-homology pack:
  finite simplicial-complex closure, oriented-boundary replay,
  `boundary^2 = 0`, Betti-rank replay over `Q`, checked bad-boundary
  rejection, a checked QF_LIA bad-coefficient certificate, and the homology
  Lean horizon. The lesson is linked from the math learning index plus the
  finite-structures, analysis/topology, and linear-algebra paths.

- **Finite continuous-map end-to-end lesson landed.** Added
  [`finite-continuous-maps-end-to-end.md`](docs/learn/math/finite-continuous-maps-end-to-end.md)
  as the learner-facing trace for the finite-continuous-maps pack: finite
  open-preimage replay, continuity checking, homeomorphism replay, checked
  bad-continuity rejection, checked bad-homeomorphism rejection, and the
  continuous-map Lean horizon. The lesson is linked from the math learning
  index plus the finite-structures and analysis/topology paths.

- **Finite-connectedness end-to-end lesson landed.** Added
  [`finite-connectedness-end-to-end.md`](docs/learn/math/finite-connectedness-end-to-end.md)
  as the learner-facing trace for the finite-connectedness pack: finite
  connected-space replay, open-separation replay, clopen-subset disconnection,
  checked bad-connectedness rejection, and the connectedness Lean horizon. The
  lesson is linked from the math learning index plus the finite-structures and
  analysis/topology paths.

- **Finite-compactness end-to-end lesson landed.** Added
  [`finite-compactness-end-to-end.md`](docs/learn/math/finite-compactness-end-to-end.md)
  as the learner-facing trace for the finite-compactness pack: finite
  open-cover replay, subcover replay, minimal-subcover enumeration,
  finite-intersection-family replay, checked bad-cover rejection, and the
  compactness Lean horizon. The lesson is linked from the math learning index
  plus the finite-structures and analysis/topology paths.

- **Metric-continuity end-to-end lesson landed.** Added
  [`metric-continuity-end-to-end.md`](docs/learn/math/metric-continuity-end-to-end.md)
  as the learner-facing trace for the metric-continuity pack: finite
  metric-table replay, finite Lipschitz checks, epsilon-delta containment,
  open-ball preimage replay, checked bad-delta rejection, and the continuity
  Lean horizon. The lesson is linked from the math learning index plus the
  analysis/topology path.

- **Exact statistical-tests end-to-end lesson landed.** Added
  [`exact-statistical-tests-end-to-end.md`](docs/learn/math/exact-statistical-tests-end-to-end.md)
  as the learner-facing trace for the exact-statistical-tests pack: exact
  binomial-tail replay, hypergeometric point probability, one-sided Fisher
  tail replay, probability-ordered two-sided Fisher replay, checked
  QF_LRA/Farkas bad Fisher and multinomial p-value rejection, a checked QF_LIA
  bad tail-count certificate, and the statistical numerical-honesty horizon.
  The lesson is linked from the math learning index plus the
  probability/statistics path.

- **Complex-plane transform end-to-end lesson landed.** Added
  [`complex-plane-transforms-end-to-end.md`](docs/learn/math/complex-plane-transforms-end-to-end.md)
  as the learner-facing trace for the complex-plane transform pack: unit-root
  cycle replay, conjugation/product replay, rational Mobius-transform replay,
  checked bad unit-square rejection, and the complex-analysis Lean horizon. The
  lesson is linked from the math learning index plus the number-systems and
  algebra paths.

- **Finite dynamics/Euler end-to-end lesson landed.** Added
  [`finite-dynamics-euler-end-to-end.md`](docs/learn/math/finite-dynamics-euler-end-to-end.md)
  as the learner-facing trace for the bounded-dynamics and finite-Euler packs:
  recurrence replay, finite invariants, threshold reachability, explicit Euler
  step replay, exact finite error tables, checked bad error-bound and bad-step
  rejections, and the ODE/numerical-analysis Lean horizon. The lesson is linked from the math
  learning index plus the analysis/topology path.

- **Bounded-dynamics end-to-end lesson landed.** Added
  [`bounded-dynamics-end-to-end.md`](docs/learn/math/bounded-dynamics-end-to-end.md)
  as the learner-facing trace for the bounded-dynamics pack: exact recurrence
  trace replay, finite invariant checking, threshold reachability, checked
  QF_LRA/Farkas bad invariant-bound rejection, and the continuous-dynamics/ODE
  Lean horizon. The lesson is linked from the math learning index plus the
  finite dynamics/Euler and bounded-dynamics/operator bridge pages.

- **Finite-Euler-method end-to-end lesson landed.** Added
  [`finite-euler-method-end-to-end.md`](docs/learn/math/finite-euler-method-end-to-end.md)
  as the learner-facing trace for the finite-Euler pack: exact explicit-Euler
  transition replay, finite polynomial-solution error tables, monotone
  invariant checking, replay-only bad max-error, bad terminal-error, and
  bad-step rejection, separate checked QF_LRA/Farkas proof rows, and the
  ODE/numerical-analysis Lean horizon. The lesson is linked from the math
  learning index plus the finite dynamics/Euler and bounded-dynamics/operator
  bridge pages.

- **Finite-operator end-to-end lesson landed.** Added
  [`finite-operator-end-to-end.md`](docs/learn/math/finite-operator-end-to-end.md)
  as the learner-facing trace for the finite-operator pack:
  exact `l1` norm replay, row-sum operator-bound replay, finite Chebyshev
  recurrence replay, checked QF_LRA/Farkas bad-bound rejection, and the
  Banach/Hilbert/compact-operator Lean horizon. The lesson is linked from the
  math learning index plus the broad bounded-dynamics/operator bridge.

- **Finite topology/measure end-to-end lesson landed.** Added
  [`finite-topology-measure-end-to-end.md`](docs/learn/math/finite-topology-measure-end-to-end.md)
  as the learner-facing trace for the finite-topology and finite-measure packs:
  finite topology axioms, closure/interior replay, exact metric balls, finite
  sigma-algebra closure, exact additivity, event-complement replay, and the
  topology/measure Lean horizon. The lesson is linked from the math learning
  index plus the sets/finite-structures, probability/statistics, and
  analysis/topology paths.

- **Coordinate/affine geometry end-to-end lesson landed.** Added
  [`coordinate-affine-geometry-end-to-end.md`](docs/learn/math/coordinate-affine-geometry-end-to-end.md)
  as the learner-facing trace for the coordinate, affine, and orientation/area
  geometry packs: exact midpoint, collinearity, squared-distance, affine-map,
  midpoint-preservation, area-scaling, barycentric, checked bad-distance, and
  checked bad-orientation replay, plus the Lean horizon for general geometry.
  The lesson is linked from the math learning index plus the rational/real and
  linear-algebra/optimization paths.

- **Descriptive-statistics/regression end-to-end lesson landed.** Added
  [`descriptive-statistics-regression-end-to-end.md`](docs/learn/math/descriptive-statistics-regression-end-to-end.md)
  as the learner-facing trace for the descriptive-statistics and
  least-squares-regression packs: exact mean/variance replay,
  contingency-table margins, Simpson's paradox counts, least-squares normal
  equations, residual orthogonality, RSS comparison, checked bad-coefficients
  rejection, and the horizon for inference, asymptotics, and floating-point
  regression. The lesson is linked from the math learning index plus the
  probability/statistics and linear-algebra/optimization paths.

- **Numerical-linear-algebra end-to-end lesson landed.** Added
  [`numerical-linear-algebra-end-to-end.md`](docs/learn/math/numerical-linear-algebra-end-to-end.md)
  as the learner-facing trace for the numerical-linear-algebra pack: exact
  residual infinity-norm replay, rational solution-box checking, one-step
  Jacobi contraction replay, checked bad residual-bound rejection, and the
  horizon for floating-point stability, conditioning, and broad convergence
  theorems. The lesson is linked from the math learning index plus the
  linear-algebra/optimization and analysis/topology paths.

- **Finite random-matrix end-to-end lesson landed.** Added
  [`random-matrix-finite-end-to-end.md`](docs/learn/math/random-matrix-finite-end-to-end.md)
  as the learner-facing trace for the random-matrix pack: exact
  matrix-valued probability tables, trace/determinant moments, expected Gram
  matrices, rank probabilities, checked bad trace-square rejection, and the
  horizon for asymptotic random matrix theory and numerical simulation claims.
  The lesson is linked from the math learning index plus the
  linear-algebra/optimization and probability/statistics paths.

- **Spectral-linear-algebra end-to-end lesson landed.** Added
  [`spectral-linear-algebra-end-to-end.md`](docs/learn/math/spectral-linear-algebra-end-to-end.md)
  as the learner-facing trace for the spectral pack: exact eigenpair replay,
  orthogonal eigenbasis arithmetic, Rayleigh quotient checking, spectral
  decomposition reconstruction, checked bad-eigenpair rejection, and the
  horizon for general spectral theory and numerical eigensolver correctness.
  The lesson is linked from the math learning index plus the rational/real,
  linear-algebra/optimization, analysis/topology, and bounded-operators paths.

- **Finite Chebyshev-systems end-to-end lesson landed.** Added
  [`finite-chebyshev-systems-end-to-end.md`](docs/learn/math/finite-chebyshev-systems-end-to-end.md)
  as the learner-facing trace for the Chebyshev pack: exact Vandermonde
  unisolvence, interpolation replay, alternating residual signs, checked
  duplicate-node-grid rejection, and the Lean horizon for general
  Chebyshev/Haar/minimax approximation theorems. The lesson is linked from the
  math learning index plus the linear-algebra/optimization and
  analysis/topology paths.

- **Rational convexity end-to-end lesson landed.** Added
  [`convexity-rational-end-to-end.md`](docs/learn/math/convexity-rational-end-to-end.md)
  as the learner-facing trace for the convexity pack: exact midpoint Jensen
  replay, finite-grid second differences, affine threshold monotonicity,
  checked bad midpoint-convexity and affine-threshold rejections, and the Lean
  horizon for general convex analysis. The lesson is linked from the math
  learning index plus the rational/real and linear-algebra/optimization paths.

- **Rational multivariable-calculus end-to-end lesson landed.** Added
  [`multivariable-calculus-end-to-end.md`](docs/learn/math/multivariable-calculus-end-to-end.md)
  as the learner-facing trace for the multivariable-calculus pack: exact
  gradient and value replay, directional derivative dot product, Jacobian
  chain-rule matrix multiplication, Hessian positive-definiteness by minors,
  checked bad-gradient rejection, and the Lean horizon for analytic
  multivariable calculus. The lesson is linked from the math learning index
  plus the rational/real, linear-algebra, and analysis/topology paths.

- **Matrix-invariants end-to-end lesson landed.** Added
  [`matrix-invariants-end-to-end.md`](docs/learn/math/matrix-invariants-end-to-end.md)
  as the learner-facing trace for the matrix-invariants pack: exact trace,
  determinant and characteristic-polynomial replay, characteristic-root
  evaluation, Cayley-Hamilton replay, Gershgorin interval checking, and checked
  bad characteristic-polynomial rejection. The lesson is linked from the math
  learning index plus the rational/real and linear-algebra paths.

- **Rational polynomial-factorization end-to-end lesson landed.** Added
  [`polynomial-factorization-end-to-end.md`](docs/learn/math/polynomial-factorization-end-to-end.md)
  as the learner-facing trace for the polynomial-factorization pack:
  factor-list replay for `x^4 - 1`, checked long division, Euclidean GCD and
  square-free replay, negative-discriminant irreducibility rejection for
  `x^2 + 1`, and the Lean horizon for broad algebraic factorization theory.
  The lesson is linked from the math learning index plus the rational/real and
  algebra/number-theory paths.

- **Polynomial-identities end-to-end lesson landed.** Added
  [`polynomial-identities-end-to-end.md`](docs/learn/math/polynomial-identities-end-to-end.md)
  as the learner-facing trace for the polynomial-identities pack: coefficient
  multiplication replay for `(x + 1)^2`, factor-theorem root and quotient
  checking for `x^2 - 5x + 6`, checked false-root rejection for `x^2 + 1`, and
  the horizon for broad polynomial theorems. The lesson is linked from the math
  learning index plus the rational/real and algebra/number-theory paths.

- **Real-algebra RCF-shadow end-to-end lesson landed.** Added
  [`reals-rcf-shadow-end-to-end.md`](docs/learn/math/reals-rcf-shadow-end-to-end.md)
  as the learner-facing trace for the reals-RCF-shadow pack: ordered-field
  midpoint replay, nonlinear product replay, quadratic-root replay, checked
  square-nonnegative and negative-discriminant `unsat` rows, and the Lean
  horizon for real completeness. The lesson is linked from the math learning
  index plus the rational/real and analysis/topology paths.

- **Bounded rational real-analysis end-to-end lesson landed.** Added
  [`real-analysis-rational-end-to-end.md`](docs/learn/math/real-analysis-rational-end-to-end.md)
  as the learner-facing trace for the real-analysis-rational pack: exact
  rational interval/ball replay, bounded epsilon-delta sample replay,
  polynomial side-condition replay, a checked bad-delta counterexample, and
  the Lean horizon for fully quantified real-analysis theorem schemas. The
  lesson is linked from the math learning index plus the rational/real and
  analysis/topology paths.

- **Complex-algebraic end-to-end lesson landed.** Added
  [`complex-algebraic-end-to-end.md`](docs/learn/math/complex-algebraic-end-to-end.md)
  as the learner-facing trace for the complex-algebraic pack: exact rational
  real-pair addition and multiplication, conjugate/norm replay, the fixed `i`
  root witness for `x^2 + 1`, and the replay-only boundary for complex-analysis
  theorem horizons. The lesson is linked from the math learning index plus the
  number-systems and algebra/number-theory paths.

- **Bounded number-theory end-to-end lesson landed.** Added
  [`number-theory-end-to-end.md`](docs/learn/math/number-theory-end-to-end.md)
  as the learner-facing trace for the number-theory pack: compatible
  non-coprime CRT replay, quadratic residue and nonresidue checks,
  sum-of-two-squares replay and mod-4 rejection, Diophantine witness replay,
  and the Lean horizon for deeper number-theory theorems. The lesson is linked
  from the math learning index plus the number-systems and algebra/number-theory
  paths.

- **Modular-arithmetic end-to-end lesson landed.** Added
  [`modular-arithmetic-end-to-end.md`](docs/learn/math/modular-arithmetic-end-to-end.md)
  as the learner-facing trace for the modular-arithmetic pack: CRT witness
  replay, modular inverse replay, finite composite non-unit search, Fermat-style
  unit search modulo `5`, and the explicit replay-only proof gap. The lesson is
  linked from the math learning index plus the number-systems and
  algebra/number-theory paths.

- **GCD/Bezout end-to-end lesson landed.** Added
  [`gcd-bezout-end-to-end.md`](docs/learn/math/gcd-bezout-end-to-end.md)
  as the learner-facing trace for the gcd/Bezout pack: gcd/common-divisor
  replay, Bezout coefficient checking, divisibility quotient replay, and the
  fixed Diophantine gcd obstruction. The lesson is linked from the math
  learning index plus the number-systems and algebra/number-theory paths.

- **Integer-LIA end-to-end lesson landed.** Added
  [`integer-lia-end-to-end.md`](docs/learn/math/integer-lia-end-to-end.md)
  as the learner-facing trace for the integer-LIA pack: signed trichotomy and
  order-transitivity replay, integer ring and linear-equation witnesses,
  interval infeasibility, and the gcd-divisibility Diophantine refutation. The
  lesson is linked from the math learning index plus the number-systems path.

- **Natural-arithmetic end-to-end lesson landed.** Added
  [`natural-arithmetic-end-to-end.md`](docs/learn/math/natural-arithmetic-end-to-end.md)
  as the learner-facing trace for the natural-arithmetic pack: successor
  arithmetic replay, fixed addition and distributivity replay, bounded
  successor-fact enumeration over `0..7`, and the Lean horizon for universal
  Nat theorems. The lesson is linked from the math learning index plus the
  number-systems path.

- **Induction-patterns end-to-end lesson landed.** Added
  [`induction-patterns-end-to-end.md`](docs/learn/math/induction-patterns-end-to-end.md)
  as the learner-facing trace for the induction-patterns pack: finite weak
  induction replay, a checked QF_LIA even-product certificate,
  strong-induction Fibonacci-bound replay, loop-invariant trace replay,
  invalid-step counterexample checking, and the Lean horizon for the general
  induction schema. The lesson is linked from the math learning index plus the
  logic/proof path.

- **Induction-obligations end-to-end lesson landed.** Added
  [`induction-obligations-end-to-end.md`](docs/learn/math/induction-obligations-end-to-end.md)
  as the learner-facing trace for the induction-obligations pack: prefix-sum
  base-case replay, bounded step and conclusion enumeration, a bad-step
  counterexample for `n = 0`, and the Lean horizon for the full natural-number
  induction schema. The lesson is linked from the math learning index plus the
  logic/proof path.

- **Proof-method patterns end-to-end lesson landed.** Added
  [`proof-methods-patterns-end-to-end.md`](docs/learn/math/proof-methods-patterns-end-to-end.md)
  as the learner-facing trace for the proof-methods patterns pack: direct
  proof/modus-ponens replay, contrapositive equivalence, proof-by-cases,
  contradiction refutation, invalid-converse counterexample, and the Lean
  horizon for natural-deduction soundness. The lesson is linked from the math
  learning index plus the logic/proof path.

- **Proof-by-refutation end-to-end lesson landed.** Added
  [`proof-methods-refutation-end-to-end.md`](docs/learn/math/proof-methods-refutation-end-to-end.md)
  as the learner-facing trace for the proof-methods refutation pack:
  `PHP(2,2)` SAT witness replay, deterministic `PHP(3,2)` CNF truth-table
  refutation, and the DRAT/LRAT proof-object graduation route. The lesson is
  linked from the math learning index plus the logic/proof path.

- **Finite predicate logic end-to-end lesson landed.** Added
  [`finite-predicate-end-to-end.md`](docs/learn/math/finite-predicate-end-to-end.md)
  as the learner-facing trace for the finite-predicate pack: finite universal
  and existential predicate replay, bounded `forall -> exists` valuation
  enumeration, `exists`-but-not-`forall` counterexample replay, binary-relation
  symmetry counterexample, and the Lean horizon for arbitrary-domain
  first-order validity. The lesson is linked from the math learning index plus
  the logic/proof path.

- **Logic basics end-to-end lesson landed.** Added
  [`logic-basics-end-to-end.md`](docs/learn/math/logic-basics-end-to-end.md)
  as the learner-facing trace for the logic-basics pack: Boolean SAT witness
  replay, excluded-middle and contradiction truth-table checks, De Morgan
  equivalence checking, tiny CNF refutation by enumeration, and the DRAT/LRAT
  graduation route for stronger UNSAT evidence. The lesson is linked from the
  math learning index plus the logic/proof path.

- **Function-composition end-to-end lesson landed.** Added
  [`function-composition-end-to-end.md`](docs/learn/math/function-composition-end-to-end.md)
  as the learner-facing trace for the function-composition pack: finite
  composition-table replay, image/preimage recomputation, inverse-table
  replay, associativity-table replay, checked non-injective inverse
  counterexample, the QF_UF/Alethe composition-application proof row, and the
  Lean horizon for arbitrary function laws. The lesson is linked from the math
  learning index plus the sets/relations path.

- **Equivalence-classes end-to-end lesson landed.** Added
  [`equivalence-classes-end-to-end.md`](docs/learn/math/equivalence-classes-end-to-end.md)
  as the learner-facing trace for the equivalence-classes pack: parity
  equivalence-class replay, quotient-map fiber replay, partition-to-relation
  round-trip checking, checked non-transitivity rejection, and the QF_UF/Alethe
  quotient congruence proof row. The lesson is linked from the math learning
  index plus the sets/relations path.

- **Relations/functions end-to-end lesson landed.** Added
  [`relations-functions-end-to-end.md`](docs/learn/math/relations-functions-end-to-end.md)
  as the learner-facing trace for the relations/functions pack: finite
  divisibility partial-order replay, bijective function-table replay, checked
  rejection of a multi-valued graph, and the QF_UF/Alethe function
  single-valuedness proof row. The lesson is linked from the math learning
  index plus the sets/relations path.

- **Finite sets end-to-end lesson landed.** Added
  [`finite-sets-end-to-end.md`](docs/learn/math/finite-sets-end-to-end.md)
  as the learner-facing trace for the finite sets pack: explicit finite
  universe/subset replay, union/intersection identity replay, subset
  transitivity, fixed malformed-identity rejection, and the Bool/BV plus
  CNF/LRAT graduation route for stronger finite-set evidence. The lesson is
  linked from the math learning index plus the sets/relations path.

- **Cardinality-principles end-to-end lesson landed.** Added
  [`cardinality-principles-end-to-end.md`](docs/learn/math/cardinality-principles-end-to-end.md)
  as the learner-facing trace for the cardinality-principles pack:
  inclusion-exclusion replay, disjoint-union additivity with its side
  condition, bipartite-edge double counting, powerset enumeration, a checked
  overlapping-set counterexample to false additivity, and the Lean horizon for
  arbitrary cardinality theorems. The lesson is linked from the math learning
  index plus the sets/relations path.

- **Finite cardinality end-to-end lesson landed.** Added
  [`finite-cardinality-end-to-end.md`](docs/learn/math/finite-cardinality-end-to-end.md)
  as the learner-facing trace for the finite cardinality pack: finite
  bijection replay, proper-subset injection replay, checked no-injection and
  no-surjection enumeration refutations, and the Lean horizon for Cantor and
  infinite cardinality. The lesson is linked from the math learning index plus
  the sets/relations path.

- **Finite order-lattices end-to-end lesson landed.** Added
  [`finite-order-lattices-end-to-end.md`](docs/learn/math/finite-order-lattices-end-to-end.md)
  as the learner-facing trace for the finite order/lattice pack: Boolean
  lattice partial-order replay, meet/join recomputation, distributivity
  checks, monotone fixed-point replay, checked bad-order rejection, checked
  Bool/CNF/LRAT bad top-element refutation, and the Lean horizon for
  complete-lattice and infinite-order theory. The lesson is
  linked from the math learning index plus the sets/relations path.

- **Finite groups end-to-end lesson landed.** Added
  [`finite-groups-end-to-end.md`](docs/learn/math/finite-groups-end-to-end.md)
  as the learner-facing trace for the finite groups pack: `Z/4Z`
  Cayley-table replay, inverse-table replay, checked rejection of subtraction
  modulo `3` as a group operation, the QF_UF/Alethe operation-congruence proof
  row, and the Lean horizon for general group theory. The lesson is linked
  from the math learning index plus the algebra path.

- **Finite fields end-to-end lesson landed.** Added
  [`finite-fields-end-to-end.md`](docs/learn/math/finite-fields-end-to-end.md)
  as the learner-facing trace for the finite fields pack: `F_7` inverse-table
  replay, exhaustive no-distributivity-counterexample checking in `F_5`,
  checked no-inverse rejection for `2 mod 6`, and the proof horizon for
  general field theory. The lesson is linked from the math learning index plus
  the algebra and arithmetic paths.

- **Finite rings end-to-end lesson landed.** Added
  [`finite-rings-end-to-end.md`](docs/learn/math/finite-rings-end-to-end.md)
  as the learner-facing trace for the finite rings pack: `Z/4Z` ring-table
  replay, zero-divisor witness replay, checked non-distributive-table
  rejection, and the proof horizon for ideal/domain/Noetherian ring theory.
  The lesson is linked from the math learning index plus the algebra path.

- **Finite algebra-homomorphisms end-to-end lesson landed.** Added
  [`finite-algebra-homomorphisms-end-to-end.md`](docs/learn/math/finite-algebra-homomorphisms-end-to-end.md)
  as the learner-facing trace for the finite algebra homomorphisms pack:
  parity-map group-homomorphism replay, kernel/image recomputation,
  quotient/induced-map replay, unital ring-homomorphism replay, checked
  bad-homomorphism rejection, and the Lean horizon for general isomorphism
  theorems. The lesson is linked from the math learning index plus the algebra
  and finite-structure paths.

- **Rational inner-product end-to-end lesson landed.** Added
  [`inner-product-spaces-end-to-end.md`](docs/learn/math/inner-product-spaces-end-to-end.md)
  as the learner-facing trace for the exact rational inner-product pack:
  Gram-matrix/dot-product replay, positive-definite principal-minor checks,
  fixed Cauchy-Schwarz replay, orthogonal projection, Gram-Schmidt residuals,
  checked bad-inner-product rejection, and the Lean horizon for general
  inner-product and Hilbert-space theory. The lesson is linked from the math
  learning index plus the linear-algebra and analysis paths.

- **Finite tensor-products end-to-end lesson landed.** Added
  [`finite-tensor-products-end-to-end.md`](docs/learn/math/finite-tensor-products-end-to-end.md)
  as the learner-facing trace for the finite tensor-products pack: finite
  tensor-basis/dimension replay, bilinear-map checking, finite factorization
  through a tensor map, Kronecker-product replay, checked bad-bilinear
  rejection, and the Lean horizon for general tensor and multilinear algebra.
  The lesson is linked from the math learning index plus the algebra and
  linear-algebra paths.

- **Finite modules end-to-end lesson landed.** Added
  [`finite-modules-end-to-end.md`](docs/learn/math/finite-modules-end-to-end.md)
  as the learner-facing trace for the finite modules pack: `Z/4Z`
  module-action replay, generated submodule replay, multiplication-by-`2`
  homomorphism kernel/image replay, quotient-module table replay, checked
  bad-submodule rejection, and the Lean horizon for general module theory and
  homological algebra. The lesson is linked from the math learning index plus
  the algebra and linear-algebra paths.

- **Finite dual-spaces end-to-end lesson landed.** Added
  [`finite-dual-spaces-end-to-end.md`](docs/learn/math/finite-dual-spaces-end-to-end.md)
  as the learner-facing trace for the finite dual-spaces pack: covector
  linearity, pointwise dual operations, dual-basis pairing, annihilator
  recomputation, transpose-map replay, checked bad-covector rejection, and the
  Lean horizon for general duality and functional analysis. The lesson is
  linked from the math learning index plus the algebra and linear-algebra
  paths.

- **Finite vector-spaces end-to-end lesson landed.** Added
  [`finite-vector-spaces-end-to-end.md`](docs/learn/math/finite-vector-spaces-end-to-end.md)
  as the learner-facing trace for the finite vector-spaces pack: `F2^2`
  table-law replay, subspace/span recomputation, first-coordinate projection
  kernel/image replay, rank-nullity by finite cardinality, checked bad-subspace
  rejection, and the Lean horizon for general vector-space theory. The lesson
  is linked from the math learning index plus the algebra and linear-algebra
  paths.

- **Finite ideals and quotient-rings end-to-end lesson landed.** Added
  [`finite-ideals-quotient-rings-end-to-end.md`](docs/learn/math/finite-ideals-quotient-rings-end-to-end.md)
  as the learner-facing trace for the finite ideals pack: `Z/6Z` ideal
  closure, principal ideal generation by `2`, parity-map kernel/image replay,
  quotient-ring table replay, checked non-ideal rejection, checked quotient
  representative congruence, and the Lean horizon for general ideal and
  quotient-ring theory. The lesson is linked from the math learning index plus
  the algebra and arithmetic paths.

- **Finite monoid end-to-end lesson landed.** Added
  [`finite-monoids-end-to-end.md`](docs/learn/math/finite-monoids-end-to-end.md)
  as the learner-facing trace for the finite monoid pack: two-point
  endofunction encoding, monoid identity/associativity replay,
  composition-table replay from function maps, unit and idempotent
  recomputation, bad non-associative table rejection, and the Lean horizon for
  general semigroup/monoid theory. The lesson is linked from the math learning
  index plus the algebra and finite-structures paths.

- **Finite permutation-group end-to-end lesson landed.** Added
  [`finite-permutation-groups-end-to-end.md`](docs/learn/math/finite-permutation-groups-end-to-end.md)
  as the learner-facing trace for the finite permutation-group pack:
  point-map encoding, bijection/group-law replay, composition-table replay,
  cycle/sign recomputation, sign-homomorphism checking, natural-action
  orbit/stabilizer replay, bad-nonbijection rejection, and the Lean horizon for
  general permutation-group theory. The lesson is linked from the math learning
  index plus the algebra, discrete-reasoning, and finite-structures paths.

- **Finite permutation-group foundations pack landed.** Added
  [`finite-permutation-groups-v0`](artifacts/examples/math/finite-permutation-groups-v0/README.md)
  as the exact bridge from finite functions to group theory and finite
  symmetry counting. The pack validates `S3` as bijective function tables under
  composition, recomputes cycle lengths and parity/signs, checks the sign
  homomorphism, replays the natural action's orbit/stabilizer count, rejects a
  non-bijection, and records the general permutation-group theory
  Lean-horizon row. The foundational example-pack validator, concept atlas,
  resource docs, and learner-facing algebra/discrete/finite-structure pages now
  include the new pack.

- **Finite monoid foundations pack landed.** Added
  [`finite-monoids-v0`](artifacts/examples/math/finite-monoids-v0/README.md)
  as the exact finite bridge between functions and algebraic structures. The
  pack validates the full transformation monoid on a two-point set, monoid
  identity/associativity replay, composition-table replay from finite
  functions, unit and idempotent recomputation, checked rejection of a
  non-associative table, and a general monoid/semigroup Lean-horizon row. The
  foundational example-pack validator, concept atlas, resource docs, and
  learner-facing finite-structure/algebra pages now include the new pack.

- **Finite group-action end-to-end lesson landed.** Added
  [`finite-group-actions-end-to-end.md`](docs/learn/math/finite-group-actions-end-to-end.md)
  as the learner-facing trace for the finite group-action pack: action-table
  encoding, identity/compatibility replay, orbit/stabilizer recomputation,
  Burnside fixed-point counting, bad identity-action and compatibility
  rejection, and the Lean horizon for general group-action theory. The lesson is linked from the math learning
  index plus the algebra, discrete-reasoning, and finite-structures paths.

- **Finite group-action foundations pack landed.** Added
  [`finite-group-actions-v0`](artifacts/examples/math/finite-group-actions-v0/README.md)
  as the exact finite bridge between groups, functions, and counting. The pack
  validates a `C2` action on two-bit strings, action identity/compatibility
  laws, orbit and stabilizer recomputation, orbit-stabilizer cardinality replay,
  Burnside fixed-point counting, checked bad identity-action and compatibility
  rejection, and a general group-action-theory Lean-horizon row. The foundational example-pack validator,
  concept atlas, dashboards, library-boundary counts, and learner-facing math
  pages now include the new pack.

- **Exact rational polynomial-factorization pack landed.** Added
  [`polynomial-factorization-rational-v0`](artifacts/examples/math/polynomial-factorization-rational-v0/README.md)
  as the next curriculum-adjacent deepening of the polynomial and rational
  algebra path. The pack validates factor-list product replay for `x^4 - 1`,
  polynomial long-division replay, monic Euclidean GCD replay,
  square-free decomposition through `gcd(p,p')`, checked rejection of a
  rational linear factorization claim for `x^2 + 1`, and a general
  polynomial-factorization Lean-horizon row. The foundational example-pack
  validator now checks these rows with exact rational polynomial arithmetic.

- **Exact rational inner-product foundations pack landed.** Added
  [`inner-product-spaces-rational-v0`](artifacts/examples/math/inner-product-spaces-rational-v0/README.md)
  as the finite-dimensional bridge from linear algebra into projections,
  least squares, spectral methods, optimization, numerical analysis, and
  functional-analysis proof horizons. The pack validates symmetric
  positive-definite Gram matrices, exact Cauchy-Schwarz replay, orthogonal
  projection replay, Gram-Schmidt replay, checked rejection of an indefinite
  bilinear form, and a Hilbert/inner-product-theory Lean-horizon row. The
  foundational example-pack validator now checks these rows with exact
  rational fraction arithmetic and matrix/vector replay.

- **Finite dual-space foundations pack landed.** Added
  [`finite-dual-spaces-v0`](artifacts/examples/math/finite-dual-spaces-v0/README.md)
  as the exact finite bridge from vector spaces into duality and functional
  analysis. The pack validates `F2^2` covector linearity, pointwise dual-space
  operations, dual-basis pairing, annihilator recomputation, transpose-map
  replay, checked rejection of a bad covector, and a general duality/
  functional-analysis Lean-horizon row. The foundational example-pack
  validator now checks these rows by exact finite field, vector-space,
  evaluation-table, and linear-map replay.

- **Finite tensor-product foundations pack landed.** Added
  [`finite-tensor-products-v0`](artifacts/examples/math/finite-tensor-products-v0/README.md)
  as the exact finite bridge from vector spaces/modules into tensor and
  multilinear algebra. The pack validates `F2^2 tensor F2` basis/dimension
  replay, finite bilinear-map table replay, universal-factorization shadow
  through a linear map, Kronecker-product matrix replay over `F2`, checked
  rejection of a bad bilinear map, and a general tensor-theory Lean-horizon
  row. The foundational example-pack validator now checks these rows by exact
  finite vector-space, bilinear-map, and finite-matrix enumeration.

- **Multivariable calculus foundations pack landed.** Added
  [`multivariable-calculus-rational-v0`](artifacts/examples/math/multivariable-calculus-rational-v0/README.md)
  as the exact finite bridge from one-variable calculus into gradients,
  Jacobians, Hessians, optimization, and numerical-analysis shadows. The pack
  validates bivariate-polynomial value/gradient replay, directional
  derivative replay as a gradient dot product, Jacobian chain-rule matrix
  replay for a fixed polynomial map composition, Hessian
  positive-definiteness by exact principal minors, checked rejection of a bad
  gradient, and a general multivariable-calculus Lean-horizon row. The
  foundational example-pack validator now checks these rows by exact rational
  monomial differentiation and matrix replay.

- **Finite order/lattice foundations pack landed.** Added
  [`finite-order-lattices-v0`](artifacts/examples/math/finite-order-lattices-v0/README.md)
  as the exact finite bridge from relations to order and lattice theory. The
  pack validates a four-element Boolean-lattice partial order, bottom/top
  replay, meet/join table replay as greatest lower and least upper bounds,
  distributivity over all triples, monotone-map fixed-point replay, checked
  rejection of a bad partial order, and a general order/lattice Lean-horizon
  row. The foundational example-pack validator now checks these rows by exact
  finite relation and table enumeration.

- **Finite ideal foundations pack landed.** Added
  [`finite-ideals-v0`](artifacts/examples/math/finite-ideals-v0/README.md)
  as the exact finite quotient-ring bridge for modular algebra. The pack
  validates `Z/6Z` ideal table replay for `(2) = {0,2,4}`, principal ideal
  generation, reduction modulo `2` as a ring homomorphism, kernel/image
  recomputation, quotient-ring addition and multiplication replay, checked
  rejection of a bad ideal, checked quotient representative congruence, and a
  general ideal-theory Lean-horizon row. The foundational example-pack
  validator now checks replay rows by exact finite table enumeration and the
  congruence rows through the shared QF_UF/Alethe route.

- **Finite module foundations pack landed.** Added
  [`finite-modules-v0`](artifacts/examples/math/finite-modules-v0/README.md)
  as the exact finite bridge from ring actions to linear algebra. The pack
  validates `Z/4Z` regular-module table replay, submodule/span replay,
  multiplication-by-`2` as a module homomorphism, kernel/image recomputation,
  quotient-module addition and scalar-action replay, checked rejection of a
  bad submodule, and a general module-theory Lean-horizon row. The
  foundational example-pack validator now checks these rows by exact finite
  table enumeration.

- **Finite vector space foundations pack landed.** Added
  [`finite-vector-spaces-v0`](artifacts/examples/math/finite-vector-spaces-v0/README.md)
  as the exact finite bridge from finite fields to linear algebra. The pack
  validates `F2^2` vector-space table replay, one-dimensional subspace/span
  replay, first-coordinate projection as a linear map, kernel/image
  recomputation, rank-nullity by finite cardinality, checked rejection of a
  bad subspace, and a general vector-space/module Lean-horizon row. The
  foundational example-pack validator now checks these rows by exact finite
  table enumeration.

- **Finite algebra homomorphism foundations pack landed.** Added
  [`finite-algebra-homomorphisms-v0`](artifacts/examples/math/finite-algebra-homomorphisms-v0/README.md)
  as the exact finite bridge from group/ring tables to structure-preserving
  maps. The pack validates `Z/4Z -> Z/2Z` group-homomorphism replay,
  kernel/image recomputation, quotient and induced-map replay, unital
  ring-homomorphism replay, a checked QF_UF/Alethe
  homomorphism-preservation congruence row, checked rejection of a bad
  group-homomorphism map, and a general isomorphism-theorem Lean-horizon row.
  The foundational example-pack validator now checks the finite rows by exact
  table enumeration and enforces the linked proof artifact/regression for the
  QF_UF row.

- **Finite simplicial homology foundations pack landed.** Added
  [`finite-simplicial-homology-v0`](artifacts/examples/math/finite-simplicial-homology-v0/README.md)
  as the exact finite algebraic-topology bridge across topology, finite set
  data, linear algebra, and abstract algebra. The pack validates
  simplicial-complex closure, oriented-boundary replay, `boundary^2 = 0`,
  Betti-rank replay for a three-edge circle over `Q`, checked rejection of a
  bad boundary sign, a checked QF_LIA/Diophantine bad boundary coefficient
  row, and a general homology Lean-horizon row. The foundational example-pack
  validator now checks these rows by exact face enumeration, chain
  normalization, boundary-matrix rank replay, rational Gaussian elimination,
  and solver-form Diophantine certificate metadata for the promoted
  coefficient contradiction.

- **Finite Euler method foundations pack landed.** Added
  [`finite-euler-method-v0`](artifacts/examples/math/finite-euler-method-v0/README.md)
  as the next exact finite bridge across differential equations, numerical
  analysis, and calculus. The pack validates explicit Euler traces,
  polynomial-solution error replay, finite invariant checks, checked rejection
  of bad max-error, bad terminal-error, and bad Euler-step rows, and a general
  ODE-theory Lean-horizon row. The
  foundational example-pack validator now checks these rows by exact rational
  transition replay.

- **Generating functions foundations pack landed.** Added
  [`generating-functions-v0`](artifacts/examples/math/generating-functions-v0/README.md)
  as the next exact finite bridge across counting, polynomials, and sequence
  prefixes. The pack validates coefficient extraction, Cauchy product
  convolution, Fibonacci generating-function prefix replay, checked rejection
  of a bad convolution coefficient, and a general generating-functions
  Lean-horizon row. The foundational example-pack validator now checks these
  rows by exact rational polynomial replay.

- **Least-squares regression foundations pack landed.** Added
  [`least-squares-regression-v0`](artifacts/examples/math/least-squares-regression-v0/README.md)
  as the next exact finite statistics bridge across rational arithmetic,
  linear algebra, and optimization. The pack validates least-squares normal
  equations, residual orthogonality, mean-baseline RSS comparison, checked
  rejection of bad coefficients, and a general regression-statistics
  Lean-horizon row. The foundational example-pack validator now checks these
  rows by exact rational matrix replay.

- **Complex plane transform foundations pack landed.** Added
  [`complex-plane-transforms-v0`](artifacts/examples/math/complex-plane-transforms-v0/README.md)
  as the next exact finite complex-analysis bridge after the base real-pair
  complex arithmetic pack. The pack validates unit-root cycles,
  conjugation/product replay, rational Mobius-transform replay, checked
  rejection of a false unit-square real-part claim, and a general
  complex-analysis Lean-horizon row. The foundational example-pack validator
  now checks these rows by exact rational complex-pair arithmetic.

- **Orientation/area geometry foundations pack landed.** Added
  [`orientation-area-geometry-v0`](artifacts/examples/math/orientation-area-geometry-v0/README.md)
  as the exact finite signed-area bridge after coordinate and affine geometry.
  The pack validates triangle orientation/area replay, affine area scaling by
  determinant, barycentric point-inside replay, checked rejection of a false
  orientation claim, and a general oriented-geometry Lean-horizon row. The
  foundational example-pack validator now checks these rows by exact rational
  determinant and barycentric replay.

- **Affine geometry foundations pack landed.** Added
  [`affine-geometry-v0`](artifacts/examples/math/affine-geometry-v0/README.md)
  as the exact finite affine-map bridge after coordinate geometry. The pack
  validates affine point-image replay, midpoint preservation, collinearity
  preservation under an invertible affine map, checked rejection of false
  midpoint-coordinate, collinearity-determinant, and Euclidean
  distance-preservation claims, and a general affine-geometry Lean-horizon
  row. The foundational example-pack validator now checks the affine map,
  determinant, midpoint, collinearity, midpoint coordinate conflict,
  collinearity determinant conflict, and distance counterexample rows by exact
  rational replay.

- **Foundational resource library-boundary decision landed.** Added
  [`LIBRARY-BOUNDARY-DECISION.md`](docs/foundational-resources/LIBRARY-BOUNDARY-DECISION.md)
  for Phase M8: keep the foundational resources in-repo for now, expose the
  JSON/schema/metadata files as the stable data contract, and defer new crates
  or a repo split until external consumers or shared encoders justify them.
  Added `scripts/consume-foundational-resources.py` as a dependency-free
  consumer smoke test and wired it into `scripts/check-foundational-resources.sh`.

- **Foundational field dashboard now reflects actual pack coverage.** Updated
  the foundational concept generator to read non-template
  `artifacts/examples/math/*/metadata.json` and merge validated pack coverage
  into field-level atlas rows. Regenerated
  [`foundational-concepts.json`](artifacts/ontology/foundational-concepts.json)
  and the field dashboard so fields like graph theory, probability,
  topology, measure, statistics, and functional analysis now show all landed
  packs rather than only their starter pack. The foundational resource check
  hook now regenerates and freshness-checks the concept atlas as well as the
  dashboards.

- **Function composition foundations pack landed.** Added
  [`function-composition-v0`](artifacts/examples/math/function-composition-v0/README.md)
  as the finite function-operation bridge for the relations-and-functions
  curriculum row. The pack validates composition tables, image/preimage
  replay, inverse tables for bijections, composition associativity, checked
  non-injective inverse counterexample evidence, and a general function-law
  Lean-horizon row. The foundational example-pack validator now checks these
  rows by exact finite function-graph replay.

- **Calculus Riemann-sum foundations pack landed.** Added
  [`calculus-riemann-sum-v0`](artifacts/examples/math/calculus-riemann-sum-v0/README.md)
  as the exact finite integration-shadow bridge for the calculus curriculum
  row. The pack validates finite left/right/trapezoid Riemann sums, midpoint
  replay for an affine function, antiderivative endpoint replay, monotone
  lower/upper sums, checked false integral counterexample evidence, and a
  fundamental-theorem Lean-horizon row. The foundational example-pack validator
  now checks these rows by exact rational partition and polynomial replay.

- **Cardinality principles foundations pack landed.** Added
  [`cardinality-principles-v0`](artifacts/examples/math/cardinality-principles-v0/README.md)
  as the finite counting-principles bridge for the cardinality curriculum row.
  The pack validates inclusion-exclusion, disjoint-union additivity,
  bipartite-edge double counting, powerset cardinality, checked rejection of
  false disjoint-additivity over overlapping sets, and an arbitrary
  cardinality-theorem Lean-horizon row. The foundational example-pack
  validator now checks these rows by exact finite set and incidence-table
  replay.

- **Induction patterns foundations pack landed.** Added
  [`induction-patterns-v0`](artifacts/examples/math/induction-patterns-v0/README.md)
  as the finite weak/strong induction and loop-invariant bridge for the
  induction curriculum row. The pack validates even-product weak-induction
  prefixes, a checked QF_LIA/Diophantine even-product parity obstruction,
  Fibonacci strong-induction bounds, prefix-sum loop-invariant trace replay,
  checked bad-step counterexample evidence, and a full-schema Lean-horizon row.
  The foundational example-pack validator now checks these patterns by exact
  integer replay over fixed finite prefixes and solver-form Diophantine
  certificate metadata for the promoted parity contradiction.

- **Proof-method patterns foundations pack landed.** Added
  [`proof-methods-patterns-v0`](artifacts/examples/math/proof-methods-patterns-v0/README.md)
  as the finite Boolean proof-pattern bridge for the proof-methods curriculum
  row. The pack validates direct proof/modus ponens, contrapositive
  equivalence, proof by cases, contradiction/refutation, checked invalid
  converse counterexample evidence, and a natural-deduction Lean-horizon row.
  The foundational example-pack validator now checks these proof patterns by
  assignment replay and deterministic truth-table enumeration.

- **Equivalence-class foundations pack landed.** Added
  [`equivalence-classes-v0`](artifacts/examples/math/equivalence-classes-v0/README.md)
  as the finite quotient/equivalence-class bridge for the
  relations-and-functions curriculum row. The pack validates finite
  equivalence relations, quotient-map fibers, partition-to-relation round
  trips, checked rejection of a non-transitive relation, and a checked
  QF_UF/Alethe quotient-map congruence row. The foundational example-pack
  validator now checks exact finite equivalence classes, quotient fibers,
  induced partition relations, representatives, transitivity counterexamples,
  and the presence of the linked proof artifact/regression.

- **Convexity rational foundations pack landed.** Added
  [`convexity-rational-v0`](artifacts/examples/math/convexity-rational-v0/README.md)
  as the exact finite convexity bridge for the optimization-and-convexity
  field. The pack validates midpoint Jensen replay for `x^2`, finite-grid
  second differences, affine threshold monotonicity, checked rejection of bad
  midpoint-convexity and affine-threshold claims, and a general
  convex-analysis Lean-horizon row.
  The foundational example-pack validator now checks exact rational midpoint
  averages, equal-spaced convex grids, affine threshold samples, and finite
  convexity counterexamples.

- **Real-analysis rational foundations pack landed.** Added
  [`real-analysis-rational-v0`](artifacts/examples/math/real-analysis-rational-v0/README.md)
  as the bounded rational bridge for the delta-epsilon/real-analysis gap in
  the math field spine. The pack validates exact rational interval/ball
  inclusion, a finite linear epsilon-delta sample, squeeze-style polynomial
  side conditions, checked rejection of a false delta, and a general
  real-analysis Lean-horizon row. The foundational example-pack validator now
  checks exact rational intervals, open balls, linear epsilon-delta finite
  samples, bounded polynomial side conditions, and bad-delta counterexamples.

- **Graph search runtime foundations pack landed.** Added
  [`graph-search-runtime-v0`](artifacts/examples/math/graph-search-runtime-v0/README.md)
  as the finite traversal-cost bridge for the BFS-vs-DFS runtime gap in the
  math field spine. The pack validates BFS and DFS target-discovery
  visited-count replay, shortcut-tail family counters, checked rejection of a
  false DFS cost bound, and an asymptotic graph-search Lean-horizon row. The
  foundational example-pack validator now checks BFS pop order, DFS preorder,
  generated shortcut-tail graphs, and finite traversal-cost counters.

- **Finite Chebyshev-system foundations pack landed.** Added
  [`finite-chebyshev-systems-v0`](artifacts/examples/math/finite-chebyshev-systems-v0/README.md)
  as the exact finite bridge for the Chebyshev-space gap in the math field
  spine. The pack validates finite Vandermonde unisolvence, interpolation
  matrix replay, alternating residual signs, checked rejection of a
  duplicate-node grid, and a general Chebyshev-system Lean-horizon row. The
  foundational example-pack validator now checks exact rational polynomial
  basis matrices, determinants, interpolation products, residual signs, and
  finite null-vector refutations.

- **Finite concentration foundations pack landed.** Added
  [`finite-concentration-v0`](artifacts/examples/math/finite-concentration-v0/README.md)
  as the exact finite concentration bridge across probability, statistics,
  measure, and real-analysis proof horizons. The pack validates finite Markov,
  Chebyshev, and union-bound tail checks over rational atom tables, checked
  rejection of a false concentration bound, and a concentration/limit-theorem
  Lean-horizon row. The foundational example-pack validator now checks
  normalized atom tables, expectations, variances, finite tail events, union
  probabilities, and false tail-bound refutations.

- **Finite hitting-time foundations pack landed.** Added
  [`finite-hitting-times-v0`](artifacts/examples/math/finite-hitting-times-v0/README.md)
  as the exact finite Markov-chain bridge from transition matrices into
  first-hit, absorption, and expected-time reasoning. The pack validates
  first-hit probabilities through a finite horizon, survival mass,
  absorption-probability fixed-point equations, expected hitting-time
  equations, checked rejection of a false expected-time table, and a
  recurrence/transience Lean-horizon row. The foundational example-pack
  validator now checks finite state transition matrices, target-state hitting
  events, first-hit distributions, absorption-probability equations, and
  expected hitting-time equations.

- **Finite stochastic-kernel foundations pack landed.** Added
  [`finite-stochastic-kernels-v0`](artifacts/examples/math/finite-stochastic-kernels-v0/README.md)
  as the exact finite conditional-distribution bridge across probability,
  measure, Markov chains, and stochastic-process reasoning. The pack validates
  finite kernel row normalization, pushforward distributions, joint-table
  factorization and disintegration, finite kernel composition, checked
  rejection of a malformed kernel row, and a regular-conditional-probability
  Lean-horizon row. The foundational example-pack validator now checks labeled
  finite kernels, exact row sums, kernel pushforwards, joint marginals,
  kernel recovery by finite disintegration, and kernel composition.

- **Finite martingale foundations pack landed.** Added
  [`finite-martingales-v0`](artifacts/examples/math/finite-martingales-v0/README.md)
  as the exact finite filtration bridge from conditional expectation into
  stochastic-process reasoning. The pack validates finite adaptedness,
  martingale conditional-expectation equalities, square-submartingale
  inequalities, bounded stopping-time expectation replay, checked rejection of
  a false martingale table, and a general martingale Lean-horizon row. The
  foundational example-pack validator now checks finite filtrations,
  filtration refinement, adaptedness, martingale equalities, finite
  submartingale inequalities, stopping-time measurability, and stopped
  expectations.

- **Finite conditional-expectation foundations pack landed.** Added
  [`finite-conditional-expectation-v0`](artifacts/examples/math/finite-conditional-expectation-v0/README.md)
  as the exact finite partition-conditioning bridge between finite random
  variables, probability, measure, and statistics. The pack validates
  conditional expectations as blockwise weighted averages, the law of total
  expectation, a finite tower-property replay over nested partitions, checked
  rejection of false conditional-expectation and tower-property tables, and a general
  conditional-expectation/martingale Lean-horizon row. The foundational
  example-pack validator now checks finite partitions, exact block averages,
  total-expectation replay, refinement of nested partitions, and finite tower
  identities.

- **Finite random-variable foundations pack landed.** Added
  [`finite-random-variables-v0`](artifacts/examples/math/finite-random-variables-v0/README.md)
  as the exact finite random-variable bridge between finite probability,
  measure, functions, and statistics. The pack validates pushforward
  distributions, expectation through pushforward distributions, finite
  independence checks, replay rejection of false pushforward and
  expectation-through-pushforward claims, separate checked QF_LRA/Farkas rows,
  and a general
  random-variable/conditional-expectation Lean-horizon row. The
  foundational example-pack validator now checks finite atom-to-outcome maps,
  pushforward mass, exact source and pushforward expectations, joint
  distributions, and independence by product-of-marginals replay.

- **Finite product-measure foundations pack landed.** Added
  [`finite-product-measure-v0`](artifacts/examples/math/finite-product-measure-v0/README.md)
  as the exact finite product-measure bridge between finite probability,
  measure, integration, and statistics. The pack validates Cartesian-product
  probability tables, rectangle probabilities, left/right marginals, finite
  Fubini replay, checked rejection of a false product probability, and a
  Fubini/Tonelli Lean-horizon row. The foundational example-pack validator now
  checks finite product distributions, exact marginals, rectangle measures,
  direct finite integrals, and both iterated finite sums.

- **Finite integration foundations pack landed.** Added
  [`finite-integration-v0`](artifacts/examples/math/finite-integration-v0/README.md)
  as the exact finite simple-function bridge between finite measure,
  probability, and statistics. The pack validates exact rational
  simple-function integrals, indicator integrals, finite integral linearity,
  replay rejection of a false expectation, a checked QF_LRA/Farkas
  bad-expectation row, and a Lebesgue-integration Lean-horizon row. The
  foundational example-pack validator now checks finite atom probabilities,
  exact weighted sums, event measures, linear combinations, and
  bad-expectation counterexamples.

- **Finite continuous-map foundations pack landed.** Added
  [`finite-continuous-maps-v0`](artifacts/examples/math/finite-continuous-maps-v0/README.md)
  as the finite preimage/homeomorphism bridge for topology. The pack validates
  finite continuity by enumerating preimages of codomain open sets, replays a
  finite homeomorphism by checking bijectivity plus inverse continuity, rejects
  false continuity and homeomorphism claims, and records a general
  continuous-map Lean-horizon row. The foundational example-pack validator now
  checks finite topological-map totality, open-set preimages, continuity, and
  inverse-continuity obligations.

- **Finite connectedness foundations pack landed.** Added
  [`finite-connectedness-v0`](artifacts/examples/math/finite-connectedness-v0/README.md)
  as the finite clopen-subset/open-separation bridge for topology
  connectedness. The pack validates a connected Sierpinski-space witness, a
  disconnected discrete-space separation witness, a clopen-subset
  disconnection witness, checked rejection of a false connectedness claim, and
  a general connectedness Lean-horizon row. The foundational example-pack
  validator now enumerates finite subsets, recomputes clopen subsets, finds
  open separations, and checks connectedness counterexamples.

- **Finite compactness foundations pack landed.** Added
  [`finite-compactness-v0`](artifacts/examples/math/finite-compactness-v0/README.md)
  as the finite open-cover bridge for topology and compactness. The pack
  validates finite open-cover/subcover replay, checked minimal-subcover
  enumeration, finite-intersection-family replay, checked rejection of a bad
  open cover, and a general compactness Lean-horizon row. The foundational
  example-pack validator now checks finite topology cover unions, subcover
  membership, smaller-subcover enumeration, closed-family intersections, and
  bad-cover missing points.

- **Metric continuity foundations pack landed.** Added
  [`metric-continuity-v0`](artifacts/examples/math/metric-continuity-v0/README.md)
  as the first finite epsilon-delta continuity resource. The pack validates a
  finite Lipschitz witness, finite epsilon-delta containment, an open-ball
  preimage, checked rejection of an overlarge delta, and a general continuity
  Lean-horizon row. The foundational example-pack validator now checks exact
  rational finite metric tables, function-value distances, finite ball
  containment, and documented bad-delta counterexamples.

- **Matrix invariant foundations pack landed.** Added
  [`matrix-invariants-v0`](artifacts/examples/math/matrix-invariants-v0/README.md)
  as the characteristic-polynomial follow-up to the finite spectral slice. The
  pack validates exact trace/determinant characteristic-polynomial replay,
  characteristic root checks, a fixed Cayley-Hamilton replay, finite
  Gershgorin interval containment, and checked rejection of a false
  characteristic polynomial. The foundational example-pack validator now checks
  the required exact matrix arithmetic, fixed-degree polynomial evaluation, and
  finite interval containment over rationals.

- **Spectral linear algebra foundations pack landed.** Added
  [`spectral-linear-algebra-v0`](artifacts/examples/math/spectral-linear-algebra-v0/README.md)
  as the first exact finite spectral-linear-algebra resource. The pack
  validates exact eigenpair replay, orthogonal eigenbasis arithmetic, Rayleigh
  quotient replay, spectral decomposition reconstruction, and checked
  rejection of a false eigenpair. The foundational example-pack validator now
  checks exact matrix-vector products, scalar-vector products, dot products,
  Rayleigh quotients, and `P*D*P^-1` reconstruction over rational matrices.

- **Exact statistical tests foundations pack landed.** Added
  [`exact-statistical-tests-v0`](artifacts/examples/math/exact-statistical-tests-v0/README.md)
  as the first exact finite statistical-test resource. The pack validates a
  binomial right-tail p-value, a hypergeometric point probability, a one-sided
  Fisher exact-test p-value, a probability-ordered two-sided Fisher p-value,
  a probability-ordered exact multinomial p-value, checked QF_LRA/Farkas
  rejection of false Fisher and multinomial p-value rows, and a checked
  QF_LIA/Diophantine bad tail-count row. The
  foundational example-pack validator now checks binomial and hypergeometric
  p-values as rational finite sums over integer counts, requires solver-form
  SMT-LIB artifact and regression metadata for promoted proof rows, and stays
  clear of asymptotic or floating-point approximations.

- **Finite Markov-chain foundations pack landed.** Added
  [`finite-markov-chain-v0`](artifacts/examples/math/finite-markov-chain-v0/README.md)
  as the first exact stochastic-process bridge across probability, linear
  algebra, statistics, and dynamics. The pack validates row-stochastic
  transition matrices, finite-horizon distribution replay, stationary
  distribution replay, and checked rejection of a malformed transition row plus
  a false stationary-distribution row. The
  foundational example-pack validator now checks exact rational stochastic
  matrices, normalized distributions, row-vector transition multiplication,
  fixed-horizon absorption probability, and stationarity.

- **Finite random-matrix foundations pack landed.** Added
  [`random-matrix-finite-v0`](artifacts/examples/math/random-matrix-finite-v0/README.md)
  as the first exact random-matrix bridge across linear algebra, probability,
  statistics, and numerical analysis. The pack validates normalized
  matrix-valued probability tables, exact trace/determinant moments, expected
  Gram matrices, exact rank probabilities, and checked rejection of a false
  trace-square moment. The foundational example-pack validator now checks
  finite matrix distributions, exact weighted matrix expectations, rational row
  reduction rank, and moment refutations without asymptotic or floating-point
  claims.

- **Numerical linear algebra foundations pack landed.** Added
  [`numerical-linear-algebra-v0`](artifacts/examples/math/numerical-linear-algebra-v0/README.md)
  as the first exact numerical-analysis error-bound resource. The pack validates
  residual infinity-norm replay, rational solution-box replay, one Jacobi step
  with an exact row-sum contraction bound, and checked rejection of a false
  residual bound. The foundational example-pack validator now checks exact
  residual vectors, infinity norms, interval membership, Jacobi updates, and
  finite contraction inequalities without using floating-point tolerances.

- **Graph cut foundations pack landed.** Added
  [`graph-cut-v0`](artifacts/examples/math/graph-cut-v0/README.md)
  to close the first richer-cut slice in the graph lane. The pack validates a
  minimum `s-t` edge cut with a partition certificate, rejection of a
  non-separating one-edge cut, a minimum internal vertex cut, and rejection of a
  non-separating one-vertex cut. The foundational example-pack validator now
  checks cut partition crossing edges, reachability after removals, and
  exhaustive smaller edge/vertex cut enumeration.

- **Graph d-separation foundations pack landed.** Added
  [`graph-d-separation-v0`](artifacts/examples/math/graph-d-separation-v0/README.md)
  as the next graph/probability bridge resource. The pack validates active
  chain replay, chain/fork blocking by conditioned non-colliders, unconditioned
  collider blocking, and descendant-conditioned collider opening. The
  foundational example-pack validator now checks finite DAG acyclicity,
  skeleton-path enumeration, collider detection, descendant activation, and
  d-separation by exhaustive path blocking.

- **Graph matching foundations pack landed.** Added
  [`graph-matching-v0`](artifacts/examples/math/graph-matching-v0/README.md)
  as the next graph-theory resource after reachability. The pack validates
  finite matching replay, invalid overlapping-edge rejection, an augmenting
  path flip, and a checked `K3` no-perfect-matching obstruction by exhaustive
  enumeration. The foundational example-pack validator now checks finite
  matching disjointness, maximum size by enumeration, augmenting-path
  alternation, and perfect-matching absence.

- **Graph reachability foundations pack landed.** Added
  [`graph-reachability-v0`](artifacts/examples/math/graph-reachability-v0/README.md)
  as the second graph-theory resource after coloring. The pack validates finite
  BFS shortest-distance replay, deterministic DFS traversal replay, a checked
  disconnected no-path refutation, and edge-cut separation replay. The
  foundational example-pack validator now recomputes graph reachability,
  traversal order, distance maps, and cut separation from the raw finite graph.

- **Proof-methods finite CNF route landed.** Updated
  [`proof-methods-refutation-v0`](artifacts/examples/math/proof-methods-refutation-v0/README.md)
  from an explicit proof-gap pack to checked finite evidence: the validator now
  replays the `PHP(2,2)` witness, verifies the deterministic `PHP(3,2)` CNF,
  and enumerates all 64 assignments to reject every placement. The pack does
  not claim emitted LRAT/DRAT evidence yet; that remains the proof-object
  graduation target and cookbook route.

- **Calculus algebraic-shadow foundations pack landed.** Added
  [`calculus-algebraic-shadow-v0`](artifacts/examples/math/calculus-algebraic-shadow-v0/README.md)
  with polynomial derivative coefficient replay, a checked product-rule
  polynomial identity, tangent-line replay, convex quadratic critical-point
  replay, false derivative rejection, and a general calculus Lean-horizon row.
  The foundational example-pack validator now checks polynomial addition,
  derivatives, product-rule identities, tangent values, critical-point
  arithmetic, and analytic theorem-horizon metadata.

- **Sequence/limit shadow foundations pack landed.** Added
  [`sequence-limit-shadow-v0`](artifacts/examples/math/sequence-limit-shadow-v0/README.md)
  with finite reciprocal-tail epsilon replay, a finite counterexample to a
  proposed limit, monotone bounded prefix replay, a fixed geometric partial-sum
  identity, bounded Cauchy-tail no-counterexample checking, and a general
  convergence Lean-horizon row. The foundational example-pack validator now
  checks exact finite sequence values, bounded epsilon inequalities, finite
  pairwise tail enumeration, geometric sums, and limit theorem-horizon
  metadata. Continue by closing the remaining `proof-methods-refutation-v0`
  CNF/LRAT proof gap or by adding `calculus-algebraic-shadow-v0`.

- **Real algebra / RCF-shadow foundations pack landed.** Added
  [`reals-rcf-shadow-v0`](artifacts/examples/math/reals-rcf-shadow-v0/README.md)
  with exact ordered-field midpoint replay, nonlinear real product replay, a
  quadratic real-root witness, checked `x^2 < 0` infeasibility, checked
  negative-discriminant no-root infeasibility, and a real-completeness /
  epsilon-delta Lean-horizon row. The foundational example-pack validator now
  checks the real pack with exact rational arithmetic, polynomial evaluation,
  fixed square-nonnegativity metadata, quadratic discriminants, and theorem
  horizon metadata. Continue by closing the remaining
  `proof-methods-refutation-v0` CNF/LRAT proof gap or by adding
  `sequence-limit-shadow-v0`.

- **Finite predicate-logic foundations pack landed.** Added
  [`finite-predicate-v0`](artifacts/examples/math/finite-predicate-v0/README.md)
  with finite-domain universal and existential predicate replay, exhaustive
  non-empty finite `forall -> exists` checking, an `exists`-not-`forall`
  counterexample, finite binary-relation asymmetry replay, and a general
  first-order Lean-horizon row. The foundational example-pack validator now
  checks finite unary predicate tables, finite quantifier expansion by
  enumeration, binary predicate counterexamples, and the first-order
  theorem-horizon metadata. Continue by closing the remaining
  `proof-methods-refutation-v0` CNF/LRAT proof gap or by adding
  `reals-rcf-shadow-v0`.

- **Logic basics foundations pack landed.** Added
  [`logic-basics-v0`](artifacts/examples/math/logic-basics-v0/README.md)
  with SAT witness replay for `p and q`, checked excluded-middle
  no-counterexample enumeration, checked contradiction UNSAT enumeration,
  checked De Morgan equivalence enumeration, and a tiny CNF refutation
  `(p) and (!p or q) and (!q)` by truth-table enumeration. The foundational
  example-pack validator now checks Boolean assignments, truth-table
  enumeration, literal/CNF evaluation, and the documented CNF row. Continue by
  closing the remaining `proof-methods-refutation-v0` CNF/LRAT proof gap or by
  adding `finite-predicate-v0`.

- **Induction obligations foundations pack landed.** Added
  [`induction-obligations-v0`](artifacts/examples/math/induction-obligations-v0/README.md)
  with exact prefix-sum base-case replay, bounded step-obligation
  no-counterexample checking, bounded conclusion checking, a bad-step
  counterexample witness for the false property `n = 0`, and the full induction
  schema kept as Lean-horizon metadata. The foundational example-pack validator
  now checks bounded induction limits, exact prefix-sum arithmetic, step and
  conclusion enumeration, and theorem-horizon metadata. Continue by closing the
  remaining `proof-methods-refutation-v0` CNF/LRAT proof gap or by adding
  `logic-basics-v0`, which is now the propositional-logic follow-on.

- **Finite cardinality foundations pack landed.** Added
  [`finite-cardinality-v0`](artifacts/examples/math/finite-cardinality-v0/README.md)
  with finite bijection replay, proper-subset injection replay, checked
  no-injection `4 -> 3`, checked no-surjection `2 -> 3`, and a
  Cantor-diagonal infinite-cardinality row explicitly kept as Lean-horizon. The
  foundational example-pack validator now checks finite function graphs,
  injection/surjection/bijection properties, bounded function-space
  enumeration, and the theorem-horizon metadata row. `induction-obligations-v0`
  is now the bounded induction follow-on.

- **Natural arithmetic core number-system pack landed.** Added
  [`natural-arithmetic-v0`](artifacts/examples/math/natural-arithmetic-v0/README.md)
  with successor-addition replay, addition commutativity replay,
  multiplication distributivity replay, checked bounded successor injectivity,
  checked zero-not-successor, and a checked nonnegative-domain row. The
  foundational example-pack validator now checks nonnegative natural-number
  witnesses and bounded-domain enumeration for Peano-style no-counterexample
  rows; generated dashboards mark the naturals curriculum row's first pack as
  validated. `finite-cardinality-v0` is the follow-on finite foundations pack.

- **Integer LIA core number-system pack landed.** Added
  [`integer-lia-v0`](artifacts/examples/math/integer-lia-v0/README.md) with
  signed trichotomy replay, order-transitivity replay, integer ring-identity
  replay, a linear equation witness, a checked infeasible interval, and the
  `2*x + 4*y = 3` GCD obstruction from the integers curriculum row. The
  foundational example-pack validator now checks fixed integer comparisons,
  exact integer identities, linear dot-product witnesses, interval
  contradictions, and GCD non-divisibility; generated dashboards mark the
  integers curriculum row's first pack as validated. `natural-arithmetic-v0`
  is the follow-on bounded natural-number pack.

- **Bounded number-theory destination pack landed.** Added
  [`number-theory-v0`](artifacts/examples/math/number-theory-v0/README.md)
  with a compatible non-coprime CRT witness, quadratic-residue witness,
  checked quadratic nonresidue, sum-of-two-squares witness, checked mod-4
  two-squares obstruction, and bounded linear Diophantine witness. The
  foundational example-pack validator now checks CRT compatibility, finite
  residue-square enumeration, square-sum replay, the mod-4 obstruction, and
  exact Diophantine replay; generated dashboards mark the number-theory
  curriculum row's first pack as validated. Continue by closing the remaining
  `proof-methods-refutation-v0` CNF/LRAT proof gap or by adding
  `integer-lia-v0` / `natural-arithmetic-v0`.

- **GCD/Bezout core arithmetic pack landed.** Added
  [`gcd-bezout-v0`](artifacts/examples/math/gcd-bezout-v0/README.md) with exact
  `gcd(252,198)` common-divisor replay, Bezout coefficient replay, a direct
  divisibility quotient witness, and a checked `6*x + 10*y = 15`
  Diophantine obstruction. The foundational example-pack validator now checks
  gcd/common-divisor lists, Bezout equations, quotient divisibility, and the
  fixed gcd non-divisibility criterion; generated dashboards mark the
  divisibility-and-Euclid curriculum row's first pack as validated. Continue
  with `number-theory-v0` as the bounded destination pack.

- **Finite rings core-structure pack landed.** Added
  [`finite-rings-v0`](artifacts/examples/math/finite-rings-v0/README.md) with
  `Z/4Z` addition/multiplication table replay, a checked zero-divisor witness,
  and a checked non-distributive table rejection. The foundational example-pack
  validator now checks additive abelian group structure, multiplication
  associativity, multiplicative identity, distributivity, and finite
  zero-divisor witnesses; generated dashboards mark the rings curriculum row's
  first pack as validated. `gcd-bezout-v0` is the follow-on arithmetic core
  pack.

- **Finite groups core-structure pack landed.** Added
  [`finite-groups-v0`](artifacts/examples/math/finite-groups-v0/README.md)
  with `Z/4Z` Cayley-table replay, inverse-table replay, and a checked
  subtraction-mod-3 non-group rejection. It now also carries a checked
  QF_UF/Alethe binary-operation congruence artifact. The foundational
  example-pack validator now checks finite operation tables, identity,
  inverses, associativity, and the linked proof artifact/regression. Generated
  dashboards include the pack and mark the groups curriculum row's first pack
  as validated. `finite-rings-v0` is the follow-on finite algebra table pack.

- **Counting core curriculum pack landed.** Added
  [`counting-v0`](artifacts/examples/math/counting-v0/README.md) with fixed
  permutation count replay, Pascal/binomial identity replay, and an exhaustive
  checked `3 -> 2` pigeonhole refutation. The foundational example-pack
  validator now computes factorial/permutation/combination counts and enumerates
  finite pigeonhole placements; generated dashboards mark `counting-v0` as
  validated. The recommended Phase M3 pack list has landed; continue by closing
  the remaining `proof-methods-refutation-v0` CNF/LRAT proof gap or by adding
  the next arithmetic core packs.

- **Polynomial identities core curriculum pack landed.** Added
  [`polynomial-identities-v0`](artifacts/examples/math/polynomial-identities-v0/README.md)
  with exact coefficient replay for `(x + 1)^2`, a factor-theorem witness for
  `x^2 - 5x + 6` at `2`, and a checked false-root rejection for `x^2 + 1` over
  the rationals. The foundational example-pack validator now checks exact
  polynomial coefficient normalization, multiplication, and evaluation;
  generated dashboards mark `polynomial-identities-v0` as validated. Continue
  Phase M3 with `counting-v0`, or close the remaining
  `proof-methods-refutation-v0` CNF/LRAT proof gap.

- **Finite fields core curriculum pack landed.** Added
  [`finite-fields-v0`](artifacts/examples/math/finite-fields-v0/README.md)
  with `F_7` inverse-table replay, exhaustive `F_5` distributivity
  no-counterexample checking, and a checked `Z/6Z` non-field contrast. The
  foundational example-pack validator now checks prime moduli, inverse-table
  coverage, finite distributivity enumeration, and composite no-inverse rows;
  generated dashboards mark `finite-fields-v0` as validated. Continue Phase M3
  with `polynomial-identities-v0` or `counting-v0`, or close the remaining
  `proof-methods-refutation-v0` CNF/LRAT proof gap.

- **Relations/functions core curriculum pack landed.** Added
  [`relations-functions-v0`](artifacts/examples/math/relations-functions-v0/README.md)
  with finite relation-property replay, bijective function-table replay, and a
  checked rejection of a multi-valued graph. It now also carries a checked
  QF_UF/Alethe function single-valuedness artifact. The foundational
  example-pack validator now checks relation pairs, partial-order properties,
  function totality/single-valuedness, injectivity, surjectivity, and the linked
  proof artifact/regression. Continue Phase M3 with
  `finite-fields-v0`, or close the remaining `proof-methods-refutation-v0`
  CNF/LRAT proof gap.

- **Finite sets core curriculum pack landed.** Added
  [`finite-sets-v0`](artifacts/examples/math/finite-sets-v0/README.md) with
  exact finite-universe replay for union/intersection distributivity, subset
  transitivity, and a bounded rejection of a malformed fixed set identity.
  [`scripts/validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py)
  now validates the finite-set semantics, and generated foundational dashboards
  mark `finite-sets-v0` as validated. Continue Phase M3 with
  `relations-functions-v0`, or close the remaining
  `proof-methods-refutation-v0` CNF/LRAT proof gap.

- **Foundational resource check hook landed.** Added
  [`scripts/check-foundational-resources.sh`](scripts/check-foundational-resources.sh)
  and wired it into `just foundational-resources`, `just check`,
  [`scripts/check.sh`](scripts/check.sh), and the CI docs resources/link job.
  The gate validates the concept atlas, validates all math example packs,
  regenerates dashboards, and fails if generated dashboard files are stale.
  Continue by closing the remaining `proof-methods-refutation-v0` CNF/LRAT proof
  gap or by adding the next Phase M3 core curriculum pack.

- **Pack-level proof-gap dashboard generation landed.** Extended
  [`scripts/gen-foundational-dashboards.py`](scripts/gen-foundational-dashboards.py)
  so
  [`docs/foundational-resources/generated/proof-gap-dashboard.md`](docs/foundational-resources/generated/proof-gap-dashboard.md)
  now includes math example-pack route coverage, validator commands, per-pack
  proof-status counts, and concrete replay/proof-gap rows from `expected.json`.
  Continue Phase M7 by adding a normal check target for these validators once
  the generated views stabilize.

- **Phase M6 proof-route links widened.** Added
  [Finite Model Replay Evidence](docs/proof-cookbook/recipes/finite-model-replay.md),
  [QF_LIA Diophantine Evidence](docs/proof-cookbook/recipes/qf-lia-diophantine.md),
  and [Lean Horizon Template](docs/proof-cookbook/recipes/lean-horizon-template.md)
  to the Proof Certificate Cookbook, then linked every current non-template
  math example pack to its replay/checking route or graduation target. Continue
  by making the proof-gap dashboard derive pack-level gaps instead of only
  concept-atlas gaps.

- **Proof cookbook Boolean CNF recipe landed.** Added
  [`docs/proof-cookbook/recipes/boolean-cnf-lrat.md`](docs/proof-cookbook/recipes/boolean-cnf-lrat.md)
  and linked it from `graph-coloring-v0` and
  `proof-methods-refutation-v0`. Continue Phase M6 by linking cookbook recipes
  from the remaining example packs and adding missing recipes for repeated
  evidence gaps.

- **Phase M5 end-to-end lesson coverage completed.** Added finite
  topology/measure and bounded dynamics/operator end-to-end lessons under
  [`docs/learn/math/`](docs/learn/math/), and linked them from the finite
  structures and analysis/topology cluster pages. Phase M5 now has scaffold,
  walkthroughs, and end-to-end lessons for every planned math cluster. Continue
  Phase M6 with proof-cookbook recipe links from example packs.

- **Math end-to-end lesson set widened.** Added rational midpoint,
  linear-system/LP, and finite conditional-probability end-to-end lessons under
  [`docs/learn/math/`](docs/learn/math/), and linked them from the relevant
  cluster pages. These trace validated pack data through exact replay and
  proof/evidence status. Continue Phase M5 with finite-structures and
  analysis/topology end-to-end lessons.

- **First math end-to-end lesson landed.** Added
  [`docs/learn/math/graph-coloring-end-to-end.md`](docs/learn/math/graph-coloring-end-to-end.md)
  to trace `graph-coloring-v0` from finite data row through replayed `sat`,
  checked finite `unsat`, and proof/evidence status. Continue Phase M5 with
  end-to-end lessons for rational arithmetic, linear algebra/optimization, and
  probability/statistics.

- **Math learner walkthrough layer landed.** Expanded all nine
  [`docs/learn/math/`](docs/learn/math/) cluster pages with concrete
  encode/check walkthroughs using validated pack data and repo-root validation
  commands. Continue Phase M5 by adding richer end-to-end lessons that trace one
  example from data row through replay result and proof/evidence status.

- **Math learner path scaffold landed.** Added
  [`docs/learn/math/README.md`](docs/learn/math/README.md) and the nine Phase
  M5 cluster pages for logic/proof, finite structures, number systems, algebra,
  rational/real algebra, graph/discrete reasoning, linear algebra/optimization,
  probability/statistics, and analysis/topology horizons. Each page links
  concept rows, validated example packs, current Axeyum-checkable slices, and
  the Lean/numerical horizon. Continue Phase M5 by turning these scaffolds into
  concrete encode/check walkthroughs.

- **Complex algebraic pack landed.** Added
  [`artifacts/examples/math/complex-algebraic-v0/`](artifacts/examples/math/complex-algebraic-v0/)
  for exact complex arithmetic, conjugate/norm replay, and a fixed
  polynomial-root witness over real-pair algebra. The foundational example-pack
  validator now checks exact complex pair addition/multiplication, conjugation,
  norm-squared products, and `i^2 + 1 = 0` replay. Continue Phase M5 with
  `docs/learn/math/README.md`.

- **Finite operator pack landed.** Added
  [`artifacts/examples/math/finite-operator-v0/`](artifacts/examples/math/finite-operator-v0/)
  for exact finite-dimensional norm, matrix-operator, and Chebyshev recurrence
  checks. The foundational example-pack validator now checks `l1` triangle
  witnesses, infinity-norm row-sum operator bounds, and finite Chebyshev
  recurrence values.

- **Bounded dynamics pack landed.** Added
  [`artifacts/examples/math/bounded-dynamics-v0/`](artifacts/examples/math/bounded-dynamics-v0/)
  for exact rational recurrence traces, bounded invariant witnesses, and
  threshold reachability replay. The foundational example-pack validator now
  checks finite recurrence traces, invariant bounds over traces, and first
  threshold-reaching steps.

- **Finite measure pack landed.** Added
  [`artifacts/examples/math/finite-measure-v0/`](artifacts/examples/math/finite-measure-v0/)
  for finite sigma-algebra axioms, exact finite additivity, and
  event/complement measure replay. The foundational example-pack validator now
  checks finite measurable families, complement/union closure, rational measure
  tables, normalization, and additivity over disjoint measurable sets.

- **Finite topology pack landed.** Added
  [`artifacts/examples/math/finite-topology-v0/`](artifacts/examples/math/finite-topology-v0/)
  for finite topology axioms, closure/interior computation, and exact finite
  metric-ball replay. The foundational example-pack validator now checks finite
  set families, topology closure under union/intersection, closure/interior via
  complements, and rational finite metric balls.

- **Coordinate geometry pack landed.** Added
  [`artifacts/examples/math/coordinate-geometry-v0/`](artifacts/examples/math/coordinate-geometry-v0/)
  for exact midpoint, collinearity, and squared-distance coordinate checks. The
  foundational example-pack validator now checks rational 2D points, determinant
  collinearity, and squared Euclidean distance exactly.

- **Linear optimization pack landed.** Added
  [`artifacts/examples/math/linear-optimization-v0/`](artifacts/examples/math/linear-optimization-v0/)
  for exact LP feasibility witnesses, objective-threshold replay, and a tiny
  checked Farkas infeasibility certificate. The foundational example-pack
  validator now checks exact rational linear inequalities and nonnegative
  Farkas multipliers that derive a contradictory bound.

- **Descriptive statistics pack landed.** Added
  [`artifacts/examples/math/descriptive-statistics-v0/`](artifacts/examples/math/descriptive-statistics-v0/)
  for exact mean/variance identities, contingency-table margins, and a
  Simpson's paradox count-table witness. The foundational example-pack
  validator now checks exact rational moments, integer margins, and finite
  success-rate inequalities. The first ten math-resource commits are complete.

- **Finite probability pack landed.** Added
  [`artifacts/examples/math/finite-probability-v0/`](artifacts/examples/math/finite-probability-v0/)
  for exact finite probability mass tables, conditional probability, and Bayes
  posterior replay. The foundational example-pack validator now checks
  rational probability atoms, normalization, event conditioning, and Bayes rule
  exactly.

- **Graph coloring pack landed.** Added
  [`artifacts/examples/math/graph-coloring-v0/`](artifacts/examples/math/graph-coloring-v0/)
  as the first pure field-extension pack for graph theory. The pack validates a
  proper `K3` three-coloring witness, rejects an invalid same-edge coloring, and
  exhaustively checks that `K3` has no two-coloring.

- **Linear algebra rational pack landed.** Added
  [`artifacts/examples/math/linear-algebra-rational-v0/`](artifacts/examples/math/linear-algebra-rational-v0/)
  for exact rational matrix-vector solution replay, LU factorization replay,
  and a row-scaling inconsistency certificate for a singular system. The
  foundational example-pack validator now has exact rational matrix helpers for
  this pack, and the next planned math-resource increment is
  `graph-coloring-v0`.

- **Rationals LRA pack landed.** Added
  [`artifacts/examples/math/rationals-lra-v0/`](artifacts/examples/math/rationals-lra-v0/)
  for exact rational density, additive inverse, trichotomy, and order
  transitivity checks. The foundational example-pack validator now parses
  rational strings with exact arithmetic and replays the pack without
  floating-point tolerances. The concept atlas and generated dashboard now mark
  `rationals-lra-v0` as validated for the `rationals` curriculum row.

- **Modular arithmetic pack landed.** Added
  [`artifacts/examples/math/modular-arithmetic-v0/`](artifacts/examples/math/modular-arithmetic-v0/)
  for small CRT, modular inverse, composite non-unit, and Fermat-style finite
  checks, plus a checked QF_LIA/Diophantine nonunit obstruction. The
  foundational example-pack validator now replays this pack's arithmetic:
  congruence witnesses, modular inverse witnesses, exhaustive non-invertibility
  over a composite modulus, the solver-form gcd obstruction, and exhaustive
  absence of Fermat-counterexamples over units modulo 5. The concept atlas and
  generated dashboards now mark `modular-arithmetic-v0` as validated.

- **First substantive math example pack landed.** Added
  [`artifacts/examples/math/proof-methods-refutation-v0/`](artifacts/examples/math/proof-methods-refutation-v0/)
  for proof-by-refutation over finite pigeonhole examples. The pack validates
  structurally, records a `PHP(2,2)` SAT witness, records `PHP(3,2)` as UNSAT,
  and keeps deterministic CNF plus checked LRAT/DRAT evidence as an explicit
  proof gap. The concept atlas generator now marks referenced packs as
  `validated` when their metadata exists.

- **Foundational example-pack scaffold landed.** Added
  [`artifacts/ontology/foundational-example-pack.schema.json`](artifacts/ontology/foundational-example-pack.schema.json),
  [`scripts/validate-foundational-example-pack.py`](scripts/validate-foundational-example-pack.py),
  and the validating
  [`artifacts/examples/math/template-v0/`](artifacts/examples/math/template-v0/)
  scaffold. The validator checks required pack files, concept IDs, field IDs,
  curriculum-node references, source links, expected-result IDs, witness
  references, claim status, trust status, and graduation criteria.

- **Foundational Concept Atlas seed landed.** Added
  [`artifacts/ontology/foundational-concepts.schema.json`](artifacts/ontology/foundational-concepts.schema.json)
  and
  [`artifacts/ontology/foundational-concepts.json`](artifacts/ontology/foundational-concepts.json),
  generated by
  [`scripts/gen-foundational-concepts.py`](scripts/gen-foundational-concepts.py)
  and validated by
  [`scripts/validate-foundational-concepts.py`](scripts/validate-foundational-concepts.py).
  The seed validates **41 rows**: all **23** curriculum nodes plus all **18**
  university math fields. Added generated dashboards for curriculum coverage,
  field coverage, and proof gaps under
  [`docs/foundational-resources/generated/`](docs/foundational-resources/generated/).

- **Math curriculum resource buildout planned.** Added
  [`docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md`](docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md)
  as the operational plan from the 23-node curriculum DAG and 18-field taxonomy
  to validated concept rows, math example packs, learner pages, proof/certificate
  hooks, generated dashboards, and eventual library/repository boundary
  decisions. The plan defines resource lanes, node-to-pack mappings, field
  extensions, eight build phases, and the first ten commit-sized increments.

- **Foundational math field taxonomy added.** Added
  [`docs/foundational-resources/MATH-FIELDS.md`](docs/foundational-resources/MATH-FIELDS.md)
  as the university-style mathematics spine for the Foundational Concept Atlas.
  It records 18 undergraduate/graduate fields, priority bands, source
  grounding, atlas schema implications, first example-pack targets, and honest
  proof horizons for examples such as delta-epsilon limits, Chebyshev spaces,
  graph coloring, traversal runtime, random matrices, and LU decomposition.
  The foundational resource roadmap now treats those fields as the math
  `field_id` authority for future concept rows.

- **Foundational resource expansion researched and planned.** Added
  [`docs/foundational-resources/`](docs/foundational-resources/) with a source
  research ledger and roadmap for expanding foundational mathematics, computer
  science, logic, and statistics resources. The plan is grounded in web sources,
  GitHub metadata/search, and shallow ignored reference clones, and it defines
  artifact families, schemas, example-pack requirements, domain tracks,
  validation strategy, phased delivery, and graduation criteria.

- **Rules-as-Code first pack landed.** Added
  [`docs/rules-as-code/examples/benefit-eligibility-v0/`](docs/rules-as-code/examples/benefit-eligibility-v0/)
  with source citations, formal model notes, expected checks, replayed
  witnesses, and explicit proof gaps. Added
  [`artifacts/ontology/rules-core.schema.json`](artifacts/ontology/rules-core.schema.json)
  plus [`scripts/validate-rules-as-code.py`](scripts/validate-rules-as-code.py),
  which replays every documented witness and finite-sample checks consistency,
  coverage, and income monotonicity.

- **Proof Certificate Cookbook first recipes landed.** Added the first four
  route recipes under [`docs/proof-cookbook/recipes/`](docs/proof-cookbook/recipes/):
  QF_BV bit-blast/DRAT evidence, QF_UF congruence/Alethe evidence, QF_LRA
  Farkas evidence, and array read-over-write axiom evidence. Each recipe names
  a tiny formula, solver route, evidence artifact, checker, Lean status, trust
  boundary, focused test commands, and links to the atlas/support/trust docs.

- **SMT Fragment Atlas first artifact landed.** Added
  [`artifacts/ontology/smt-fragments.json`](artifacts/ontology/smt-fragments.json)
  with ten initial fragment rows (`QF_BV`, `QF_ABV`, `QF_UF`, `QF_UFBV`,
  `QF_LRA`, `QF_LIA`, `QF_DT`, `QF_FP`, `QF_NRA`, `QF_NIA`), plus
  [`smt-fragments.schema.json`](artifacts/ontology/smt-fragments.schema.json)
  and [`scripts/validate-smt-fragment-atlas.py`](scripts/validate-smt-fragment-atlas.py).
  The validator checks stable IDs, required evidence fields, local source links,
  benchmark references, and dominance-audit citations.

- **First sibling incubator roadmaps drafted.** Added structured roadmaps for
  the three recommended incubators:
  [`SMT Fragment Atlas`](docs/atlas/ROADMAP.md),
  [`Proof Certificate Cookbook`](docs/proof-cookbook/ROADMAP.md), and
  [`Rules-as-Code Verification Lab`](docs/rules-as-code/ROADMAP.md). Each plan
  defines audience, schema/content shape, examples, validation checks, Axeyum
  capability links, and graduation criteria; [`docs/sibling-projects.md`](docs/sibling-projects.md)
  now links to the detailed plans.

- **Sibling project notes documented.** Added
  [`docs/sibling-projects.md`](docs/sibling-projects.md) with the ranked top-30
  sibling project ideas, family taxonomy, inside-vs-separate-repo guidance,
  law/rules reasoning notes, and recommended first incubators
  (`SMT Fragment Atlas`, `Proof Certificate Cookbook`, and
  `Rules-as-Code Verification Lab`). Linked it from `PLAN.md`, the docs hub,
  and the mdBook summary.

- **Multi-agent worktree protocol documented.** Added
  [`docs/contributor-guide/multi-agent-worktrees.md`](docs/contributor-guide/multi-agent-worktrees.md)
  as the standing note for side-by-side agent work: separate worktrees, topic
  branches, one `main` integration owner, explicit high-conflict file ownership,
  safe push rules, conflict handling, and cleanup. Linked it from `PLAN.md`,
  the docs hub, the contributor guide, and the mdBook summary.
