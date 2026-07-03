#!/usr/bin/env bash
# Validate foundational resource data and ensure generated dashboards are current.
set -euo pipefail

cd "$(dirname "$0")/.."

python3 scripts/gen-foundational-concepts.py
python3 scripts/validate-foundational-concepts.py
python3 scripts/validate-foundational-example-pack.py
python3 scripts/check-foundational-negative-fixtures.py
python3 scripts/consume-foundational-resources.py
python3 scripts/consume-foundational-resources.py --format json >/dev/null
python3 scripts/query-foundational-resources.py summary >/dev/null
python3 scripts/query-foundational-resources.py coverage --by field --require-any >/dev/null
python3 scripts/query-foundational-resources.py coverage --by fragment --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py coverage --by proof-status --require-any >/dev/null
python3 scripts/query-foundational-resources.py coverage --by expected-result --require-any >/dev/null
python3 scripts/query-foundational-resources.py coverage --by decidability --require-any >/dev/null
python3 scripts/query-foundational-resources.py coverage --by curriculum-node --field topology --require-any >/dev/null
python3 scripts/query-foundational-resources.py coverage-frontier --by field --require-any >/dev/null
python3 scripts/query-foundational-resources.py coverage-frontier --by field --action proof-review --require-any >/dev/null
python3 scripts/query-foundational-resources.py coverage-frontier --by fragment --min-replay-unsat 1 --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py coverage-frontier --by curriculum-node --field topology --min-horizon 1 --require-any >/dev/null
python3 scripts/query-foundational-resources.py pack-frontier --field real_analysis --require-any >/dev/null
python3 scripts/query-foundational-resources.py pack-frontier --field topology --action theorem-horizon --shadow-state checked-finite-shadow --require-any >/dev/null
python3 scripts/query-foundational-resources.py pack-frontier --field measure_theory --max-checked-ratio 0.35 --require-any >/dev/null
python3 scripts/query-foundational-resources.py pack-frontier --field real_analysis --action proof-review --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route Diophantine --field number_theory --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route Farkas --field linear_algebra --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route Alethe --field abstract_algebra --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route lean --field topology --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route lean --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --route lean-horizon-template --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --fragment Bool --field logic_and_proof --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --fragment Bool --field logic_and_proof --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --fragment QF_BV --field number_theory --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --fragment QF_BV --field number_theory --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --fragment QF_LIA --field statistics --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --fragment QF_LIA --field statistics --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --fragment QF_LRA --field probability_theory --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --fragment QF_LRA --field probability_theory --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --fragment QF_UF --field abstract_algebra --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --fragment QF_UF --field abstract_algebra --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --fragment finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --fragment finite --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --fragment Lean --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --fragment Lean --proof-status lean-horizon --expected-result not-run --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --fragment QF_LRA --solver-reuse promoted --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --fragment QF_UF --solver-reuse promoted --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --text rejected --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --text rejected --proof-status replay-only --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --text rejected --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --text rejected --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --text bad --route Farkas --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --text bad --route Alethe --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --text bad --route qf-bv --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --text bad --route boolean --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --text bad --route Diophantine --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --proof-status checked --expected-result sat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --proof-status replay-only --expected-result sat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --proof-status lean-horizon --expected-result not-run --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --expected-result not-run --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py labels --require-any >/dev/null
python3 scripts/query-foundational-resources.py labels --scope rows --label "checked witness" --require-any >/dev/null
python3 scripts/query-foundational-resources.py labels --scope rows --label "checked refutation" --require-any >/dev/null
python3 scripts/query-foundational-resources.py labels --scope rows --label "finite witness replay" --require-any >/dev/null
python3 scripts/query-foundational-resources.py labels --scope rows --label "finite rejection replay" --require-any >/dev/null
python3 scripts/query-foundational-resources.py labels --scope rows --label "theorem horizon" --require-any >/dev/null
python3 scripts/query-foundational-resources.py labels --scope packs --label "checked evidence pack" --require-any >/dev/null
python3 scripts/query-foundational-resources.py labels --scope packs --label "mixed trust story" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field probability_theory --proof-status replay-only --expected-result sat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --proof-status lean-horizon --expected-result not-run --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --text convergence --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --field topology --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --field topology --shadow-state checked-finite-shadow --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-compactness-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-connectedness-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-continuous-maps-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-quotient-topology-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-specialization-order-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --shadow-state no-finite-shadow --format json >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --curriculum-node calculus --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text convergence --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse promoted --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse promoted --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse promoted --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse promoted --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse promoted --field graph_theory --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --route Farkas --expected-result unsat --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --route Alethe --expected-result unsat --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --proof-status replay-only --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field probability_theory --proof-status replay-only --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field abstract_algebra --proof-status replay-only --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --proof-status replay-only --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --proof-status replay-only --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --proof-status replay-only --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --proof-status replay-only --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --proof-status replay-only --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --proof-status replay-only --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --curriculum-node linear-algebra --promotion-state covered-by-route-contrast --require-any >/dev/null
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --solver-reuse promoted --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py upgrade-frontier --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py upgrade-frontier --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py upgrade-frontier --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py upgrade-frontier --route Alethe --promotion-state covered-by-route-contrast --require-any >/dev/null
python3 scripts/query-foundational-resources.py upgrade-frontier --route Farkas --promotion-state no-route-contrast --format json >/dev/null
python3 scripts/query-foundational-resources.py packs --field probability_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --kind example-family --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --kind curriculum-node --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --curriculum-node sets --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --curriculum-node sets --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --curriculum-node linear-algebra --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --curriculum-node linear-algebra --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --curriculum-node modular-arithmetic --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --curriculum-node modular-arithmetic --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --curriculum-node calculus --route lean-horizon-template --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field probability_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field probability_theory --text probability --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field probability_theory --text random --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field probability_theory --text covariance --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field probability_theory --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --text Bayes --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --text Bayes --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --route Farkas --proof-status checked --text independence --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --route Farkas --proof-status checked --text "total variation" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-random-variables-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-random-variables-v0 --route Farkas --proof-status checked --text qf-lra-bad-pushforward --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-random-variables-v0 --route Farkas --proof-status checked --text qf-lra-bad-expectation-through-pushforward --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text random-variable --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-random-variables-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --route Farkas --proof-status checked --text total --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --route Farkas --proof-status checked --text variance --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-conditional-expectation-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-martingales-v0 --route Farkas --proof-status checked --text qf-lra-bad-stopped-expectation --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-martingales-v0 --route Farkas --proof-status checked --text qf-lra-bad-martingale --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-markov-chain-v0 --route Farkas --proof-status checked --text qf-lra-bad-stochastic-row --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-markov-chain-v0 --route Farkas --proof-status checked --text qf-lra-bad-stationary-distribution --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-markov-chain-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-concentration-v0 --route Farkas --proof-status checked --text qf-lra-bad-concentration-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-concentration-v0 --route Farkas --proof-status checked --text qf-lra-bad-union-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --route Farkas --proof-status checked --text qf-lra-bad-survival-mass --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --route Farkas --proof-status checked --text qf-lra-bad-expected-time --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_probability_mass_table --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_measure_additivity --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_product_integration --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-integration-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_pushforward_distribution --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_conditional_expectation --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_stochastic_kernel --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_tail_count_obstruction --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_random_matrix_finite_moment --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_random_matrix_finite_moment --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack random-matrix-finite-v0 --route Farkas --proof-status checked --text rank --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-covariance-matrix-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_random_matrix_finite_moment --route Farkas --proof-status checked --text covariance --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field linear_algebra --text Gaussian --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-gaussian-elimination-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field linear_algebra --text LU --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-lu-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-pivoted-lu-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lu_replay --pack finite-pivoted-lu-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-pivoted-lu-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-ldlt-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lu_replay --pack finite-ldlt-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-ldlt-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field linear_algebra --text Schur --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_schur_complement --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_schur_complement --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-schur-complement-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-schur-complement-v0 --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-schur-complement-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field logic_and_proof --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field logic_and_proof --text proof --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field logic_and_proof --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_boolean_cnf_lrat_anatomy --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_refutation_query --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_countermodel_replay --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_countermodel_replay --solver-reuse promoted --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_countermodel_replay --pack finite-predicate-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_countermodel_replay --pack proof-methods-patterns-v0 --expected-result sat --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_countermodel_replay --pack relations-functions-v0 --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_countermodel_replay --pack finite-order-lattices-v0 --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_proof_pattern --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_bounded_induction_obligation --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field set_theory_and_foundations --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field set_theory_and_foundations --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field set_theory_and_foundations --text partition --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field set_theory_and_foundations --text Boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field set_theory_and_foundations --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_quantifier_expansion --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_bijection_cardinality --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cardinality-v0 --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack cardinality-principles-v0 --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text Cantor --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cardinality-v0 --proof-status lean-horizon --expected-result not-run --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack cardinality-principles-v0 --proof-status lean-horizon --expected-result not-run --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cardinality-v0 --proof-status checked --text injection --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack cardinality-principles-v0 --proof-status checked --text powerset --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack cardinality-principles-v0 --proof-status checked --text overlap --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_boolean_algebra --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-order-lattices-v0 --route Alethe --proof-status checked --text antisymmetry --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-permutation-groups-v0 --route Alethe --proof-status checked --text injectivity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_partition_relation_roundtrip --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_image_preimage_inverse --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field discrete_math --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field discrete_math --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field discrete_math --text counting --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field discrete_math --text asymptotic --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field discrete_math --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_counting_replay --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_counting_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_counting_replay --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_bounded_family_asymptotic_boundary --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_bounded_family_asymptotic_boundary --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field differential_equations_and_dynamical_systems --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text Euler --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text "Runge-Kutta" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text Heun --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text "backward Euler" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text "Crank-Nicolson" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text "Adams-Bashforth" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text BDF2 --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text asymptotic --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text stochastic --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_dynamics_euler_replay --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-recurrence-prefix-v0 --route Farkas --proof-status checked --text qf-lra-bad-fibonacci-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-recurrence-prefix-v0 --route Farkas --proof-status checked --text qf-lra-bad-affine-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-recurrence-prefix-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text recurrence --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-recurrence-prefix-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_stochastic_kernel --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack bounded-dynamics-v0 --route Farkas --proof-status checked --text qf-lra-bad-transition-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack bounded-dynamics-v0 --route Farkas --proof-status checked --text qf-lra-bad-threshold-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack bounded-dynamics-v0 --route Farkas --proof-status checked --text qf-lra-bad-invariant-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack bounded-dynamics-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-euler-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-euler-method-v0 --route Farkas --proof-status checked --text qf-lra-bad-max-error-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-euler-method-v0 --route Farkas --proof-status checked --text qf-lra-bad-terminal-error --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-euler-method-v0 --route Farkas --proof-status checked --text qf-lra-bad-euler-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-euler-method-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-runge-kutta-midpoint-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-runge-kutta-midpoint-v0 --route Farkas --proof-status checked --text qf-lra-bad-rk-midpoint-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --pack finite-runge-kutta-midpoint-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-runge-kutta-midpoint-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-heun-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-heun-method-v0 --route Farkas --proof-status checked --text qf-lra-bad-heun-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --pack finite-heun-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-heun-method-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-backward-euler-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-backward-euler-method-v0 --route Farkas --proof-status checked --text qf-lra-bad-backward-euler-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --pack finite-backward-euler-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-backward-euler-method-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-crank-nicolson-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-crank-nicolson-method-v0 --route Farkas --proof-status checked --text qf-lra-bad-crank-nicolson-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --pack finite-crank-nicolson-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-crank-nicolson-method-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-adams-bashforth-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-adams-bashforth-method-v0 --route Farkas --proof-status checked --text qf-lra-bad-adams-bashforth-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --pack finite-adams-bashforth-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-adams-bashforth-method-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-bdf2-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-bdf2-method-v0 --route Farkas --proof-status checked --text qf-lra-bad-bdf2-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --pack finite-bdf2-method-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-bdf2-method-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text ODE --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-euler-method-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-runge-kutta-midpoint-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-heun-method-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-backward-euler-method-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-crank-nicolson-method-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-adams-bashforth-method-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-bdf2-method-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text martingale --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-martingales-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-markov-chain-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-stochastic-kernels-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text stochastic-kernel --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-stochastic-kernels-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-algebraic-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-riemann-sum-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-simpson-rule-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked --text qf-lra-bad-romberg-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_integration_horizon --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-romberg-extrapolation-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-romberg-extrapolation-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-divided-differences-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-divided-differences-v0 --route Farkas --proof-status checked --text qf-lra-bad-interpolation-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_polynomial_coefficient_factor_replay --pack finite-divided-differences-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-divided-differences-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-divided-differences-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-barycentric-interpolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-barycentric-interpolation-v0 --route Farkas --proof-status checked --text qf-lra-bad-barycentric-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_polynomial_coefficient_factor_replay --pack finite-barycentric-interpolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-barycentric-interpolation-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-barycentric-interpolation-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-difference-derivatives-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-difference-derivatives-v0 --route Farkas --proof-status checked --text qf-lra-bad-finite-difference-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_derivative_identity_shadow --pack finite-difference-derivatives-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-difference-derivatives-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-difference-derivatives-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-taylor-polynomials-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-taylor-polynomials-v0 --route Farkas --proof-status checked --text qf-lra-bad-taylor-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_derivative_identity_shadow --pack finite-taylor-polynomials-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_polynomial_coefficient_factor_replay --pack finite-taylor-polynomials-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-taylor-polynomials-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-taylor-polynomials-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cubic-hermite-interpolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cubic-hermite-interpolation-v0 --route Farkas --proof-status checked --text qf-lra-bad-hermite-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_derivative_identity_shadow --pack finite-cubic-hermite-interpolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_polynomial_coefficient_factor_replay --pack finite-cubic-hermite-interpolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cubic-hermite-interpolation-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cubic-hermite-interpolation-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cubic-spline-interpolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cubic-spline-interpolation-v0 --route Farkas --proof-status checked --text qf-lra-bad-spline-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_derivative_identity_shadow --pack finite-cubic-spline-interpolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_polynomial_coefficient_factor_replay --pack finite-cubic-spline-interpolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cubic-spline-interpolation-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cubic-spline-interpolation-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text calculus --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field topology --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field topology --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field topology --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text compactness --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text metric --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text preimage --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text closure --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text homeomorphism --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text quotient --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text specialization --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text boundary --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text homology --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text torsion --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text cohomology --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text universal --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field topology --text cup --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field topology --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_metric_ball --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_bounded_epsilon_delta_shadow --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_bounded_epsilon_delta_shadow --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack metric-continuity-v0 --route Farkas --proof-status checked --text preimage --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_compactness_shadow --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_connectedness_shadow --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-topology-v0 --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-compactness-v0 --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-connectedness-v0 --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_topology_operator_homeomorphism --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_topology_operator_homeomorphism --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-continuous-maps-v0 --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-continuous-maps-v0 --route Alethe --proof-status checked --text preimage --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_quotient_topology_replay --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_quotient_topology_replay --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-quotient-topology-v0 --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-quotient-topology-v0 --route Alethe --proof-status checked --text representative --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_specialization_order_replay --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_specialization_order_replay --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-specialization-order-v0 --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_boundary_operator_replay --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_boundary_operator_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_chain_homology_replay --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_chain_homology_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-simplicial-homology-v0 --route Diophantine --proof-status checked --text boundary-square --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_torsion_homology_replay --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_torsion_homology_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-chain-complex-torsion-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chain-complex-torsion-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chain-complex-torsion-v0 --route Diophantine --proof-status checked --text torsion --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_cohomology_replay --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_cohomology_replay --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_universal_coefficient_shadow --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_universal_coefficient_shadow --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_cup_product_replay --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_cup_product_replay --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field measure_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field measure_theory --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field measure_theory --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-measure-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-measure-v0 --route Farkas --proof-status checked --text complement --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-measure-monotonicity-v0 --route Farkas --proof-status checked --text union --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-measure-monotonicity-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-product-measure-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-product-measure-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-product-measure-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-integration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-integration-v0 --route Farkas --proof-status checked --text qf-lra-bad-expectation --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-integration-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-martingales-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-martingales-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field statistics --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text tail --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text covariance --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text random --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field statistics --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-covariance-matrix-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack descriptive-statistics-v0 --route Farkas --proof-status checked --text qf-lra-bad-variance --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack least-squares-regression-v0 --route Farkas --proof-status checked --text RSS --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack exact-statistical-tests-v0 --route Farkas --proof-status checked --text Fisher --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack exact-statistical-tests-v0 --route Farkas --proof-status checked --text two-sided --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack exact-statistical-tests-v0 --route Farkas --proof-status checked --text multinomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-concentration-v0 --route Farkas --proof-status checked --text qf-lra-bad-concentration-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-concentration-v0 --route Farkas --proof-status checked --text qf-lra-bad-union-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-concentration-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-stochastic-kernels-v0 --route Farkas --proof-status checked --text qf-lra-bad-kernel-row --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-stochastic-kernels-v0 --route Farkas --proof-status checked --text qf-lra-bad-kernel-composition --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-stochastic-kernels-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field statistics --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field linear_algebra --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field linear_algebra --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field linear_algebra --text rank --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field linear_algebra --text projection --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field linear_algebra --text covariance --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field linear_algebra --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field linear_algebra --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-covariance-matrix-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lu_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack linear-algebra-rational-v0 --route Farkas --proof-status checked --text product-entry --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack linear-algebra-rational-v0 --route Farkas --proof-status checked --text nullspace --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_rank_nullity --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-vector-spaces-v0 --route Alethe --proof-status checked --text addition-closure --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-vector-spaces-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-dual-spaces-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-modules-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-tensor-products-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field abstract_algebra --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text "equality certificate" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text homomorphism --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text ideal --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text action --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text tensor --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field abstract_algebra --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_algebra_equality_certificate_boundary --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_algebra_equality_certificate_boundary --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-algebra-homomorphisms-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-ideals-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-algebra-homomorphisms-v0 --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-algebra-homomorphisms-v0 --text quotient --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-ideals-v0 --text quotient --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-monoids-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-monoids-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-monoids-v0 --route Alethe --proof-status checked --text associativity --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-permutation-groups-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-permutation-groups-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_homomorphism_preservation --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_group_action --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-group-actions-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-group-actions-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-group-actions-v0 --route Alethe --proof-status checked --text identity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-group-actions-v0 --route Alethe --proof-status checked --text compatibility --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_module_action --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-modules-v0 --route Alethe --proof-status checked --text scalar-closure --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-vector-spaces-v0 --route Alethe --proof-status checked --text addition-closure --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-tensor-products-v0 --route Alethe --proof-status checked --text left-additivity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_ideal_closure --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-ideals-v0 --route Alethe --proof-status checked --text additive-closure --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_quotient_map --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_tensor_bilinearity --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text polynomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_polynomial_coefficient_factor_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_polynomial_coefficient_factor_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field abstract_algebra --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_modular_crt_inverse_witness --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_modular_crt_inverse_witness --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field number_theory --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field number_theory --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack modular-arithmetic-v0 --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field number_theory --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field number_theory --text totality --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field number_theory --text gcd --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field number_theory --text CRT --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field number_theory --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field number_theory --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_gcd_divisibility_witness --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_gcd_divisibility_witness --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_modular_crt_inverse_witness --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_modular_crt_inverse_witness --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_totality_conventions --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field graph_theory --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field graph_theory --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field graph_theory --route LIA --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field graph_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text graph --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text reachability --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text runtime --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text asymptotic --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field graph_theory --text flow --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-flow-cut-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-flow-cut-v0 --route Farkas --proof-status checked --text qf-lra-bad-flow-value-cut-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-flow-cut-v0 --expected-result not-run --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text "max-flow" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-flow-cut-v0 --proof-status checked --text "respects every edge" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-flow-cut-v0 --proof-status checked --text saturates --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-flow-cut-v0 --proof-status checked --text "value 4" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field graph_theory --text shortest --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --expected-result not-run --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text shortest --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --proof-status checked --text "exact length" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --proof-status checked --text potentials --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --proof-status checked --text "at most 4" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-shortest-path-v0 --route Farkas --proof-status checked --text qf-lra-bad-shorter-distance-potential-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field graph_theory --text topological --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --expected-result not-run --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text "topological-sort" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --proof-status checked --text "every vertex appears once" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --proof-status checked --text "no edge between algebra and analysis" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --proof-status checked --text "algebra must precede" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --route LIA --proof-status checked --text qf-lia-bad-topological-edge-order --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-dag-topological-order-v0 --proof-status checked --text "directed cycle" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_graph_replay_obstruction --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_graph_replay_obstruction --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --text "same-color" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --text "proper 2-coloring" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-coloring-v0 --text "1-bit BV" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --proof-status checked --expected-result sat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --proof-status checked --text "shortest path" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --proof-status checked --text DFS --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --proof-status checked --text disconnected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-reachability-v0 --proof-status checked --text "edge cut" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --proof-status checked --expected-result sat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --proof-status checked --text augmenting --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-matching-v0 --proof-status checked --text "triangle K3" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --proof-status checked --expected-result sat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --proof-status checked --text "minimum s-t edge cut" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-cut-v0 --proof-status checked --text "one internal vertex" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --proof-status checked --expected-result sat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --route boolean --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --proof-status checked --text fork --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --route boolean --proof-status checked --text collider --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --proof-status checked --expected-result sat --text "conditioning on a descendant" --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_graph_replay_obstruction --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_graph_replay_obstruction --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_graph_replay_obstruction --route LIA --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_graph_replay_obstruction --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --proof-status checked --expected-result sat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --proof-status checked --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --proof-status lean-horizon --expected-result not-run --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text BFS --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --proof-status checked --text BFS --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --proof-status checked --text DFS --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --text shortcut --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-search-runtime-v0 --text "at most three" --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field real_analysis --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text epsilon --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text metric --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text gradient --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Rational Interval" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-interval-arithmetic-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_rational_interval_replay --pack finite-interval-arithmetic-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Sequence Tail" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Cauchy Tail" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Squeeze Shadow" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Derivative Identity" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Integration Horizon" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text Simpson --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text polynomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field real_analysis --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_metric_ball --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_metric_ball --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack metric-continuity-v0 --route Farkas --proof-status checked --text preimage --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_bounded_epsilon_delta_shadow --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack sequence-limit-shadow-v0 --route Farkas --proof-status checked --text reciprocal --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack bounded-monotone-sequence-v0 --route Farkas --proof-status checked --text qf-lra-bad-upper-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack bounded-monotone-sequence-v0 --route Farkas --proof-status checked --text qf-lra-bad-tail-gap --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack bounded-monotone-sequence-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-algebraic-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-riemann-sum-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-simpson-rule-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-simpson-rule-v0 --route Farkas --proof-status checked --text qf-lra-bad-simpson-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_integration_horizon --pack finite-simpson-rule-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-simpson-rule-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked --text qf-lra-bad-romberg-value --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_integration_horizon --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-romberg-extrapolation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-romberg-extrapolation-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack multivariable-calculus-rational-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text calculus --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-algebraic-shadow-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-riemann-sum-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-simpson-rule-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-romberg-extrapolation-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack multivariable-calculus-rational-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-root-finding-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-root-finding-v0 --route Farkas --proof-status checked --text qf-lra-bad-newton-step --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-root-finding-v0 --route Farkas --proof-status checked --text qf-lra-bad-bisection-width --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-root-finding-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text root-finding --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-root-finding-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-newton-step-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-newton-step-v0 --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-newton-step-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-rounding-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-rounding-shadow-v0 --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-rounding-shadow-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-interval-arithmetic-shadow-v0 --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-interval-arithmetic-shadow-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-condition-number-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-condition-number-v0 --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-condition-number-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-singular-value-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-singular-value-shadow-v0 --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-singular-value-shadow-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-jordan-chain-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-jordan-chain-v0 --proof-status replay-only --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-jordan-chain-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field numerical_analysis --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text residual --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text operator --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text polynomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text Newton --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text condition --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text floating --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field numerical_analysis --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack numerical-linear-algebra-v0 --route Farkas --proof-status checked --text solution --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack numerical-linear-algebra-v0 --route Farkas --proof-status checked --text Jacobi --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field complex_analysis --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field complex_analysis --text real-pair --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field complex_analysis --text polynomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field complex_analysis --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --field complex_analysis --shadow-state checked-finite-shadow --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack complex-plane-transforms-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-cauchy-riemann-shadow-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --pack polynomial-factorization-rational-v0 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack complex-algebraic-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack complex-plane-transforms-v0 --route Farkas --proof-status checked --text conjugation --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack complex-plane-transforms-v0 --route Farkas --proof-status checked --text unit --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cauchy-riemann-shadow-v0 --route Farkas --proof-status checked --text derivative --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack polynomial-identities-v0 --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack polynomial-factorization-rational-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_complex_real_pair_transform --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_complex_real_pair_transform --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_derivative_identity_shadow --pack finite-cauchy-riemann-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field optimization_and_convexity --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field optimization_and_convexity --text objective --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field optimization_and_convexity --text convexity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field optimization_and_convexity --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_lp_objective_farkas --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lp_objective_farkas --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_rational_convexity_shadow --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_rational_convexity_shadow --route Farkas --proof-status checked --text Newton --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack convexity-rational-v0 --route Farkas --proof-status checked --text threshold --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text convex-analysis --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack convexity-rational-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-separation-v0 --route Farkas --proof-status checked --text qf-lra-bad-convex-combination-point --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-separation-v0 --route Farkas --proof-status checked --text qf-lra-bad-separator --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-separation-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text separation --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-separation-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --route Farkas --proof-status checked --text Newton --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --route Farkas --proof-status checked --text condition --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --pack finite-conjugate-gradient-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --pack finite-arnoldi-iteration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --pack finite-gmres-residual-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --pack finite-lanczos-iteration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-rounding-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-interval-arithmetic-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-kkt-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text KKT --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-kkt-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --text inactive --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --text degenerate --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text active-set --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-active-set-qp-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-sdp-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-sdp-v0 --route Farkas --proof-status checked --text gap --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text SDP --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-sdp-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-gradient-descent-v0 --route Farkas --proof-status checked --text coordinate --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-gradient-descent-v0 --route Farkas --proof-status checked --text bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-conjugate-gradient-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text gradient --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-gradient-descent-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-line-search-v0 --route Farkas --proof-status checked --text direction --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-line-search-v0 --route Farkas --proof-status checked --text candidate --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text line-search --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-line-search-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-wolfe-line-search-v0 --route Farkas --proof-status checked --text minimizer --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-wolfe-line-search-v0 --route Farkas --proof-status checked --text sufficient-decrease --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text "Wolfe line-search" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-wolfe-line-search-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-projected-gradient-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-projected-gradient-v0 --route Farkas --proof-status checked --text projection --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-projected-gradient-v0 --route Farkas --proof-status checked --text decrease --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text projected-gradient --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-projected-gradient-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --text proximal --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --text decrease --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --text box --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text proximal-gradient --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field geometry --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field geometry --text coordinate --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field geometry --text circle --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field geometry --text polynomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field geometry --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack affine-geometry-v0 --route Farkas --proof-status checked --text collinearity --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text "affine geometry" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack affine-geometry-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack affine-geometry-v0 --route Farkas --proof-status checked --text midpoint --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack affine-geometry-v0 --route Farkas --proof-status checked --text distance --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text "incidence geometry" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack incidence-geometry-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack incidence-geometry-v0 --route Farkas --proof-status checked --text intersection --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack incidence-geometry-v0 --route Farkas --proof-status checked --text incidence --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text rigidity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack rigid-configuration-geometry-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack rigid-configuration-geometry-v0 --route Farkas --proof-status checked --text translation --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack rigid-configuration-geometry-v0 --route Farkas --proof-status checked --text distance --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text oriented --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack orientation-area-geometry-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack orientation-area-geometry-v0 --route Farkas --proof-status checked --text area --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack orientation-area-geometry-v0 --route Farkas --proof-status checked --text orientation --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_coordinate_orientation_geometry --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_coordinate_orientation_geometry --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_circle_inversion_cyclic_replay --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_circle_inversion_cyclic_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text "circle geometry" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-circle-geometry-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-circle-geometry-v0 --route Farkas --proof-status checked --text radius --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-circle-geometry-v0 --route Farkas --proof-status checked --text intersection --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text "inversion geometry" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-inversion-geometry-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-inversion-geometry-v0 --route Farkas --proof-status checked --text "x-coordinate" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-inversion-geometry-v0 --route Farkas --proof-status checked --text product --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text "cyclic geometry" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cyclic-geometry-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cyclic-geometry-v0 --route Farkas --proof-status checked --text diagonal --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cyclic-geometry-v0 --route Farkas --proof-status checked --text "dot product" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cyclic-geometry-v0 --route Farkas --proof-status checked --text Ptolemy --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field functional_analysis_and_operator_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field functional_analysis_and_operator_theory --text operator --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field functional_analysis_and_operator_theory --text Chebyshev --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_operator_chebyshev --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_operator_chebyshev --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field linear_algebra --text "power-iteration" --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field numerical_analysis --text "conjugate-gradient" --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field numerical_analysis --text "Arnoldi" --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field numerical_analysis --text "GMRES" --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field numerical_analysis --text "Lanczos" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-orthogonal-diagonalization-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-orthogonal-diagonalization-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-orthogonal-diagonalization-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-real-schur-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-real-schur-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-real-schur-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-polar-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-polar-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-polar-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-qr-iteration-step-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-qr-iteration-step-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-qr-iteration-step-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-shifted-qr-step-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-shifted-qr-step-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-shifted-qr-step-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-power-iteration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-arnoldi-iteration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-lanczos-iteration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-jordan-chain-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --pack finite-gmres-residual-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --pack finite-lanczos-iteration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-walsh-hadamard-transform-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-gram-schmidt-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --pack finite-gram-schmidt-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-gram-schmidt-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-givens-rotation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --pack finite-givens-rotation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-householder-reflection-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --pack finite-householder-reflection-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-householder-reflection-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --route Farkas --proof-status checked --text transform --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-qr-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lu_replay --pack finite-lu-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --pack finite-lu-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lu_replay --pack finite-gram-schmidt-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lu_replay --pack finite-givens-rotation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lu_replay --pack finite-householder-reflection-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-cholesky-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lu_replay --route Farkas --proof-status checked --text product-entry --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_tensor_bilinearity --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_tensor_bilinearity --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --route Farkas --proof-status checked --text qf-lra-bad-l1-sum-norm --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --route Farkas --proof-status checked --text qf-lra-bad-operator-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --route Farkas --proof-status checked --text qf-lra-bad-chebyshev-t3 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_operator_chebyshev --pack finite-arnoldi-iteration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_operator_chebyshev --pack finite-gmres-residual-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_operator_chebyshev --pack finite-lanczos-iteration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked --text qf-lra-bad-duplicate-node-grid --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked --text qf-lra-bad-interpolation-sample --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked --text qf-lra-bad-alternating-residual --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text Chebyshev --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text concentration --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-concentration-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text monotone --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack bounded-monotone-sequence-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py horizon-frontier --text hitting --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --proof-status lean-horizon --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack spectral-linear-algebra-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-orthogonal-diagonalization-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-real-schur-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-polar-decomposition-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-qr-iteration-step-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-shifted-qr-step-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-power-iteration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --pack finite-singular-value-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-jordan-chain-v0 --route Farkas --proof-status checked --text qf-lra-bad-jordan-chain --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack inner-product-spaces-rational-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-dual-spaces-v0 --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-dual-spaces-v0 --route Alethe --proof-status checked --text additivity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field functional_analysis_and_operator_theory --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/gen-foundational-dashboards.py

git diff --exit-code -- \
  artifacts/ontology/foundational-concepts.json \
  docs/foundational-resources/generated/math-coverage.md \
  docs/foundational-resources/generated/curriculum-status-audit.md \
  docs/foundational-resources/generated/math-field-dashboard.md \
  docs/foundational-resources/generated/proof-gap-dashboard.md \
  docs/foundational-resources/generated/learner-proof-upgrade-dashboard.md \
  docs/foundational-resources/generated/curriculum-pressure-by-fragment.md \
  docs/foundational-resources/generated/solver-reuse-disposition-audit.md
