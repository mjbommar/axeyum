# Probability And Statistics Resource Consumer Queries

This guide turns the finite probability, measure, stochastic-process, and
statistics rows in the foundational-resource JSON contract into copyable
downstream queries. It is a consumer-discovery layer, not a new proof route and
not a claim of continuous probability, asymptotic statistics, or inference
coverage.

Use it when a learner page, catalog, solver contributor, or sibling resource
wants to ask:

```text
Which checked finite-table probability or statistics packs match this proof route?
```

The current probability/statistics surface is finite and exact-rational:
probability mass tables, finite measure additivity, product measures,
pushforward distributions, simple-function integration, conditional
expectation, finite martingale/stopping rows, finite distribution-distance
rows, stochastic kernels, finite Markov chains, finite hitting times,
concentration/tail-count rows, exact tests, finite covariance matrices, and
finite Schur conditional-variance shadows, ordinary and ridge regression, and
finite PCA, finite k-means clustering, finite linear-discriminant/classification
replay, finite Naive Bayes classifier posterior replay, finite
confusion-matrix classifier metrics, finite ROC/AUC score-ranking rows, and
finite precision-recall score-ranking rows, finite calibration/Brier scoring
rows, finite decision-tree Gini split rows, finite dyadic entropy/information-gain
rows, finite nearest-neighbor classification rows, finite perceptron
training traces, finite hard-margin SVM primal-dual rows, finite
value-iteration Bellman backups, finite policy-iteration
evaluation/improvement rounds, and finite random-matrix moments.
Continuous distributions, sampling
guarantees, asymptotic inference, MCMC/VI, stochastic-process limits,
random-matrix limit laws, clustering consistency, Lloyd convergence, global
clustering optimality, regularization-path theory, conditional-independence
validity, classifier calibration/generalization, general ROC/AUC theory,
general precision-recall theory, general calibration/scoring-rule theory,
confidence intervals, threshold policy, tie/interpolation conventions beyond
committed finite rows, binning-policy claims, decision-tree greedy optimality,
pruning, non-dyadic entropy and log-loss splitting, nearest-neighbor
consistency and tie policy, perceptron mistake bounds and convergence,
SVM strong duality, KKT sufficiency, and maximum-margin optimality,
Bellman fixed-point uniqueness and value-iteration convergence, the
policy-improvement theorem and policy-iteration termination,
continuous score
distributions,
and floating-point statistical-library behavior remain in proof-horizon or
numerical-honesty lanes.

## Query Shape

Start with field summaries by route:

```sh
python3 scripts/query-foundational-resources.py fields \
  --field probability_theory \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field measure_theory \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py fields \
  --field statistics \
  --route Farkas \
  --require-any
```

Then drill into bridge concepts by finite-table family:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_probability_mass_table \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_tail_count_obstruction \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Use `packs` for catalog rows and pack paths. Use `checks` when the consumer
needs concrete checked rows to display.

## Probability Query Families

| Family | Concept Filter | Route Filter | Start Query |
|---|---|---|---|
| Probability mass, finite measure, normalization, Bayes, independence, total variation, and concentration rows | `bridge_probability_mass_table` | `Farkas` | `checks --concept bridge_probability_mass_table --route Farkas --proof-status checked` |
| Finite measure additivity, monotonicity, complement, and subadditivity rows | `bridge_finite_measure_additivity` | `Farkas` | `checks --concept bridge_finite_measure_additivity --route Farkas --proof-status checked` |
| Product measure, simple integration, conditional expectation, and martingale rows | `bridge_finite_product_integration` | `Farkas` | `checks --concept bridge_finite_product_integration --route Farkas --proof-status checked` |
| Pushforward distributions and expectation-through-pushforward rows | `bridge_pushforward_distribution` | `Farkas` | `checks --concept bridge_pushforward_distribution --route Farkas --proof-status checked` |
| Conditional expectation, total expectation, tower property, and stopped expectation rows | `bridge_conditional_expectation` | `Farkas` | `checks --concept bridge_conditional_expectation --route Farkas --proof-status checked` |
| Conditional-expectation theorem boundary | pack `finite-conditional-expectation-v0` | `Lean horizon` | `horizon-frontier --pack finite-conditional-expectation-v0`; `checks --pack finite-conditional-expectation-v0 --proof-status lean-horizon` |
| Stochastic kernels, finite Markov chains, hitting times, and recurrence rows | `bridge_stochastic_kernel` | `Farkas` | `checks --concept bridge_stochastic_kernel --route Farkas --proof-status checked` |
| Tail counts, exact tests, finite concentration, and variance rows | `bridge_tail_count_obstruction` | `Farkas` | `checks --concept bridge_tail_count_obstruction --route Farkas --proof-status checked` |
| Ordinary and ridge regression residual/objective rows | packs `least-squares-regression-v0`, `finite-ridge-regression-v0`; concepts `bridge_residual_bound`, `bridge_inner_product_projection`, `bridge_exact_vs_floating_arithmetic` | `Farkas` | `checks --pack finite-ridge-regression-v0 --route Farkas --proof-status checked`; `checks --pack finite-ridge-regression-v0 --proof-status replay-only`; `horizon-frontier --text ridge` |
| Finite PCA covariance/eigenpair/projection rows | `bridge_finite_pca_shadow`; pack `finite-principal-components-v0` | `Farkas` | `checks --concept bridge_finite_pca_shadow --route Farkas --proof-status checked`; `checks --pack finite-principal-components-v0 --proof-status replay-only`; `horizon-frontier --text pca` |
| Finite k-means assignment, centroid, WCSS, and clustering-objective rows | `bridge_finite_k_means_shadow`; pack `finite-k-means-clustering-v0` | `Farkas` | `checks --concept bridge_finite_k_means_shadow --route Farkas --proof-status checked`; `checks --pack finite-k-means-clustering-v0 --proof-status replay-only`; `horizon-frontier --text clustering` |
| Finite linear-discriminant and classification rows | `bridge_finite_linear_discriminant_shadow`; pack `finite-linear-discriminant-v0` | `Farkas` | `checks --concept bridge_finite_linear_discriminant_shadow --route Farkas --proof-status checked`; `checks --pack finite-linear-discriminant-v0 --proof-status replay-only`; `horizon-frontier --text discriminant` |
| Finite Naive Bayes classifier posterior rows | `bridge_finite_naive_bayes_shadow`; pack `finite-naive-bayes-classifier-v0` | `Farkas` | `checks --concept bridge_finite_naive_bayes_shadow --route Farkas --proof-status checked`; `checks --pack finite-naive-bayes-classifier-v0 --proof-status replay-only`; `horizon-frontier --text "naive bayes"` |
| Finite classifier metric and confusion-matrix rows | `bridge_finite_classifier_metrics_shadow`; pack `finite-confusion-matrix-v0` | `Farkas` | `checks --concept bridge_finite_classifier_metrics_shadow --route Farkas --proof-status checked`; `checks --pack finite-confusion-matrix-v0 --proof-status replay-only`; `horizon-frontier --text "classifier metrics"` |
| Finite ROC/AUC ranking and threshold rows | `bridge_finite_roc_auc_shadow`; pack `finite-roc-auc-v0` | `Farkas` | `checks --concept bridge_finite_roc_auc_shadow --route Farkas --proof-status checked`; `checks --pack finite-roc-auc-v0 --proof-status replay-only`; `horizon-frontier --text "roc auc"` |
| Finite precision-recall ranking and average-precision rows | `bridge_finite_precision_recall_shadow`; pack `finite-precision-recall-v0` | `Farkas` | `checks --concept bridge_finite_precision_recall_shadow --route Farkas --proof-status checked`; `checks --pack finite-precision-recall-v0 --proof-status replay-only`; `horizon-frontier --text "precision recall"` |
| Finite calibration bins, ECE, and Brier-score rows | `bridge_finite_calibration_brier_shadow`; pack `finite-calibration-brier-v0` | `Farkas` | `checks --concept bridge_finite_calibration_brier_shadow --route Farkas --proof-status checked`; `checks --pack finite-calibration-brier-v0 --proof-status replay-only`; `horizon-frontier --text calibration` |
| Finite decision-tree feature/class partitions, Gini impurities, and split selection | `bridge_finite_decision_tree_gini_shadow`; pack `finite-decision-tree-gini-v0` | `Farkas` | `checks --concept bridge_finite_decision_tree_gini_shadow --route Farkas --proof-status checked`; `checks --pack finite-decision-tree-gini-v0 --proof-status replay-only`; `horizon-frontier --text decision-tree` |
| Finite dyadic entropy, weighted split entropy, and information-gain selection | `bridge_finite_entropy_information_gain_shadow`; pack `finite-entropy-information-gain-v0` | `Farkas` | `checks --concept bridge_finite_entropy_information_gain_shadow --route Farkas --proof-status checked`; `checks --pack finite-entropy-information-gain-v0 --proof-status replay-only`; `horizon-frontier --text entropy` |
| Finite squared distances, neighbor ranking, and majority-vote classification | `bridge_finite_nearest_neighbor_shadow`; pack `finite-k-nearest-neighbors-v0` | `Farkas` | `checks --concept bridge_finite_nearest_neighbor_shadow --route Farkas --proof-status checked`; `checks --pack finite-k-nearest-neighbors-v0 --proof-status replay-only`; `horizon-frontier --text neighbor` |
| Finite perceptron dot products, mistake updates, and strict-margin convergence | `bridge_finite_perceptron_shadow`; pack `finite-perceptron-v0` | `Farkas` | `checks --concept bridge_finite_perceptron_shadow --route Farkas --proof-status checked`; `checks --pack finite-perceptron-v0 --proof-status replay-only`; `horizon-frontier --text perceptron` |
| Finite hard-margin SVM hyperplane, KKT identities, and zero duality gap | `bridge_finite_hard_margin_svm_shadow`; pack `finite-hard-margin-svm-v0` | `Farkas` | `checks --concept bridge_finite_hard_margin_svm_shadow --route Farkas --proof-status checked`; `checks --pack finite-hard-margin-svm-v0 --proof-status replay-only`; `horizon-frontier --text svm` |
| Finite value-iteration Bellman backups, greedy policies, and exact fixed point | `bridge_finite_value_iteration_shadow`; pack `finite-value-iteration-v0` | `Farkas` | `checks --concept bridge_finite_value_iteration_shadow --route Farkas --proof-status checked`; `checks --pack finite-value-iteration-v0 --proof-status replay-only`; `horizon-frontier --text bellman` |
| Finite policy-iteration evaluation solves, improvement rounds, and stability | `bridge_finite_policy_iteration_shadow`; pack `finite-policy-iteration-v0` | `Farkas` | `checks --concept bridge_finite_policy_iteration_shadow --route Farkas --proof-status checked`; `checks --pack finite-policy-iteration-v0 --proof-status replay-only`; `horizon-frontier --text policy-iteration` |
| Random-matrix finite moments, covariance matrices, PCA shadows, Schur conditional-variance shadows, and expected-rank rows | `bridge_random_matrix_finite_moment`; `bridge_schur_complement`; `bridge_finite_pca_shadow` | `Farkas` | `checks --concept bridge_random_matrix_finite_moment --route Farkas --proof-status checked`; `checks --concept bridge_schur_complement --route Farkas --proof-status checked`; `checks --concept bridge_finite_pca_shadow --route Farkas --proof-status checked`; `checks --pack finite-covariance-matrix-v0 --route Farkas --proof-status checked`; `checks --pack finite-principal-components-v0 --route Farkas --proof-status checked`; `checks --pack finite-schur-complement-v0 --route Farkas --proof-status checked` |

## Copyable Examples

Display checked finite probability rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field probability_theory \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked finite distribution-distance rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-probability-v0 \
  --route Farkas \
  --proof-status checked \
  --text "total variation" \
  --require-any
```

Display finite Bayes update rows, then the checked malformed-posterior row:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-probability-v0 \
  --text Bayes \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-probability-v0 \
  --text Bayes \
  --proof-status checked \
  --require-any
```

Display finite Naive Bayes classifier rows, then the checked malformed
posterior row and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-naive-bayes-classifier-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_naive_bayes_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "naive bayes" \
  --require-any
```

Display finite classifier-metric rows, then the checked malformed precision
row and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-confusion-matrix-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_classifier_metrics_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "classifier metrics" \
  --require-any
```

Display finite ROC/AUC rows, then the checked malformed AUC row and theorem
boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-roc-auc-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_roc_auc_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "roc auc" \
  --require-any
```

Display finite precision-recall rows, then the checked malformed average
precision row and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-precision-recall-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_precision_recall_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text "precision recall" \
  --require-any
```

Display finite calibration/Brier rows, then the checked malformed Brier row
and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-calibration-brier-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_calibration_brier_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text calibration \
  --require-any
```

Display finite decision-tree Gini rows, then the checked malformed
weighted-Gini row and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-decision-tree-gini-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_decision_tree_gini_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text decision-tree \
  --require-any
```

Display finite dyadic entropy/information-gain rows, then the checked
malformed weighted-entropy row and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-entropy-information-gain-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_entropy_information_gain_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text entropy \
  --require-any
```

Display finite nearest-neighbor rows, then the checked malformed
squared-distance row and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-k-nearest-neighbors-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_nearest_neighbor_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text neighbor \
  --require-any
```

Display finite perceptron rows, then the checked malformed weight-update row
and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-perceptron-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_perceptron_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text perceptron \
  --require-any
```

Display finite hard-margin SVM rows, then the checked malformed bias row and
theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-hard-margin-svm-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_hard_margin_svm_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text svm \
  --require-any
```

Display finite value-iteration rows, then the checked malformed backup row
and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-value-iteration-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_value_iteration_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text bellman \
  --require-any
```

Display finite policy-iteration rows, then the checked malformed
policy-value row and theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-policy-iteration-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_policy_iteration_shadow \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text policy-iteration \
  --require-any
```

Display finite random-variable rows, then the theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-random-variables-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text random-variable \
  --require-any
```

Display finite stochastic-kernel rows, then the theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-stochastic-kernels-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text stochastic-kernel \
  --require-any
```

Display finite concentration rows, then the theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-concentration-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text concentration \
  --require-any
```

Display finite hitting-time rows, then the theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-hitting-times-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text hitting \
  --require-any
```

Display finite martingale rows, then the theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-martingales-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text martingale \
  --require-any
```

Display checked finite measure rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field measure_theory \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display checked statistics rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field statistics \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display finite ridge-regression rows, then the checked bad-coefficient row and
the theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-ridge-regression-v0 \
  --proof-status replay-only \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-ridge-regression-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-ridge-beta0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text ridge \
  --require-any
```

Display finite linear-discriminant rows, then the checked bad-direction row and
the theorem boundary:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-linear-discriminant-v0 \
  --proof-status replay-only \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-linear-discriminant-v0 \
  --route Farkas \
  --proof-status checked \
  --text qf-lra-bad-fisher-direction \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --text discriminant \
  --require-any
```

Display finite probability-mass and finite-measure table rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_probability_mass_table \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_measure_additivity \
  --route Farkas \
  --proof-status checked \
  --require-any
```

Display product, integration, pushforward, and conditional-expectation rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_product_integration \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_pushforward_distribution \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_conditional_expectation \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-conditional-expectation-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-conditional-expectation-v0 \
  --proof-status lean-horizon \
  --require-any
```

Display stochastic-kernel, tail-count, and random-matrix rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --concept bridge_stochastic_kernel \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_tail_count_obstruction \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_random_matrix_finite_moment \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-covariance-matrix-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-principal-components-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_finite_k_means_shadow \
  --pack finite-k-means-clustering-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --concept bridge_schur_complement \
  --route Farkas \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-schur-complement-v0 \
  --route Farkas \
  --proof-status checked \
  --require-any
```

## Current Boundary

These queries prove discoverability of finite checked probability/statistics
rows, not theorem coverage. They can support a catalog, learner page,
solver-regression search, or sibling resource that needs examples by finite
probability object family.

For the finite concentration boundary in particular, read
[Concentration Theorem Boundary](../learn/math/concentration-theorem-boundary.md)
before displaying Chernoff, Hoeffding, martingale concentration, limit-theorem,
or asymptotic-statistics language next to the finite rows.

For the finite random-variable boundary, read
[Random Variable Theorem Boundary](../learn/math/random-variable-theorem-boundary.md)
before displaying measurable-function, distribution-law, convergence,
continuous-random-variable, or density-calculus language next to finite
pushforward, expectation, and independence rows.

For the finite conditional-expectation boundary, read
[Conditional Expectation Theorem Boundary](../learn/math/conditional-expectation-theorem-boundary.md)
before displaying Radon-Nikodym construction, general conditional expectation,
regular conditional probabilities, stopping-time theorems, or martingale
theorem language next to finite partition averages, total-expectation, tower,
variance-decomposition, or checked bad-row resources.

For the finite stochastic-kernel boundary, read
[Stochastic Kernel Theorem Boundary](../learn/math/stochastic-kernel-theorem-boundary.md)
before displaying regular conditional probability, disintegration,
measurable-kernel, Markov-process, or stochastic-process convergence language
next to finite row-normalization, pushforward, joint-table, and composition
rows.

For the finite hitting-time boundary, read
[Hitting-Time Theorem Boundary](../learn/math/hitting-time-theorem-boundary.md)
before displaying recurrence, transience, optional-stopping, mixing, or
potential-theory language next to finite first-hit and expected-time rows.

For the finite martingale boundary, read
[Martingale Theorem Boundary](../learn/math/martingale-theorem-boundary.md)
before displaying martingale convergence, optional-stopping,
Doob-inequality, stochastic-integration, or continuous-time martingale
language next to finite filtration and bounded-stopping rows.

They do not prove:

- continuous distributions, density calculus, or measure construction;
- countable additivity beyond committed finite tables;
- convergence theorems, laws of large numbers, CLT, or martingale convergence;
- statistical inference guarantees, sampling quality, MCMC, VI, or model
  calibration;
- general ridge-regression optimality, bias/variance guarantees,
  regularization paths, model selection, or cross-validation;
- Fisher LDA optimality, Gaussian classifier assumptions, Bayes risk,
  multiclass LDA, classifier generalization, classifier calibration, general
  ROC/AUC theory, general precision-recall theory, confidence intervals,
  threshold selection, tie/interpolation conventions, continuous score
  distributions, or floating-point classifiers;
- random-matrix asymptotics, universality, or concentration theorems;
- floating-point statistical-library behavior;
- benchmark performance, PAR-2, or Z3/cvc5 parity.

Those claims need new proof-horizon rows, theorem-prover reconstruction,
numeric-honesty artifacts, or benchmark evidence before they can graduate.
