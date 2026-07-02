#!/usr/bin/env bash
# Validate foundational resource data and ensure generated dashboards are current.
set -euo pipefail

cd "$(dirname "$0")/.."

python3 scripts/gen-foundational-concepts.py
python3 scripts/validate-foundational-concepts.py
python3 scripts/validate-foundational-example-pack.py
python3 scripts/check-foundational-negative-fixtures.py
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary >/dev/null
python3 scripts/query-foundational-resources.py routes --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route Diophantine --field number_theory --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route Farkas --field linear_algebra --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route Alethe --field abstract_algebra --require-any >/dev/null
python3 scripts/query-foundational-resources.py routes --route lean --field topology --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse promoted --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field probability_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --kind example-family --format json --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field probability_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field probability_theory --text probability --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field probability_theory --text random --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field probability_theory --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --route Farkas --proof-status checked --text independence --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-probability-v0 --route Farkas --proof-status checked --text "total variation" --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-random-variables-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-random-variables-v0 --route Farkas --proof-status checked --text qf-lra-bad-pushforward --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-random-variables-v0 --route Farkas --proof-status checked --text qf-lra-bad-expectation-through-pushforward --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --route Farkas --proof-status checked --text total --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-conditional-expectation-v0 --route Farkas --proof-status checked --text variance --require-any >/dev/null
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
python3 scripts/query-foundational-resources.py checks --concept bridge_pushforward_distribution --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_conditional_expectation --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_stochastic_kernel --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_tail_count_obstruction --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_random_matrix_finite_moment --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_random_matrix_finite_moment --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack random-matrix-finite-v0 --route Farkas --proof-status checked --text rank --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field logic_and_proof --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field logic_and_proof --text proof --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field logic_and_proof --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_boolean_cnf_lrat_anatomy --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_refutation_query --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_proof_pattern --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_bounded_induction_obligation --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field set_theory_and_foundations --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field set_theory_and_foundations --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field set_theory_and_foundations --text partition --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field set_theory_and_foundations --text Boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field set_theory_and_foundations --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_quantifier_expansion --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_bijection_cardinality --proof-status checked --require-any >/dev/null
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
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text asymptotic --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field differential_equations_and_dynamical_systems --text stochastic --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_dynamics_euler_replay --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-recurrence-prefix-v0 --route Farkas --proof-status checked --text affine --require-any >/dev/null
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
python3 scripts/query-foundational-resources.py checks --pack finite-markov-chain-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-stochastic-kernels-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-algebraic-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-riemann-sum-v0 --route Farkas --proof-status checked --require-any >/dev/null
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
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_topology_operator_homeomorphism --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_topology_operator_homeomorphism --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-continuous-maps-v0 --route Alethe --proof-status checked --text preimage --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_quotient_topology_replay --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_quotient_topology_replay --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-quotient-topology-v0 --route Alethe --proof-status checked --text representative --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_specialization_order_replay --route alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_specialization_order_replay --route alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_boundary_operator_replay --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_boundary_operator_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_chain_homology_replay --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_chain_homology_replay --route Diophantine --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-simplicial-homology-v0 --route Diophantine --proof-status checked --text boundary-square --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_torsion_homology_replay --route Diophantine --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_torsion_homology_replay --route Diophantine --proof-status checked --require-any >/dev/null
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
python3 scripts/query-foundational-resources.py checks --pack finite-integration-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-integration-v0 --route Farkas --proof-status checked --text qf-lra-bad-expectation --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-martingales-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-martingales-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-hitting-times-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field statistics --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text tail --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text finite --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field statistics --text random --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field statistics --route Farkas --proof-status checked --require-any >/dev/null
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
python3 scripts/query-foundational-resources.py checks --field linear_algebra --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field linear_algebra --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lu_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack linear-algebra-rational-v0 --route Farkas --proof-status checked --text product-entry --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack linear-algebra-rational-v0 --route Farkas --proof-status checked --text nullspace --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_rank_nullity --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-vector-spaces-v0 --route Alethe --proof-status checked --text addition-closure --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field abstract_algebra --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text "equality certificate" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text homomorphism --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text ideal --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text action --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field abstract_algebra --text tensor --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field abstract_algebra --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_algebra_equality_certificate_boundary --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_algebra_equality_certificate_boundary --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-monoids-v0 --route Alethe --proof-status checked --text associativity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_homomorphism_preservation --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_group_action --route Alethe --proof-status checked --require-any >/dev/null
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
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text graph --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text reachability --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text runtime --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field graph_theory --text asymptotic --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_graph_replay_obstruction --route boolean --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_graph_replay_obstruction --route boolean --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack graph-d-separation-v0 --route boolean --proof-status checked --text collider --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_graph_replay_obstruction --route qf-bv --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_graph_replay_obstruction --route qf-bv --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_graph_replay_obstruction --route LIA --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_graph_replay_obstruction --route LIA --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field real_analysis --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text epsilon --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text metric --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text gradient --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Rational Interval" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Sequence Tail" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Cauchy Tail" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Squeeze Shadow" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Derivative Identity" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text "Integration Horizon" --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field real_analysis --text polynomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field real_analysis --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_metric_ball --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_metric_ball --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack metric-continuity-v0 --route Farkas --proof-status checked --text preimage --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_bounded_epsilon_delta_shadow --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack sequence-limit-shadow-v0 --route Farkas --proof-status checked --text reciprocal --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack bounded-monotone-sequence-v0 --route Farkas --proof-status checked --text tail --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-algebraic-shadow-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack calculus-riemann-sum-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-root-finding-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-root-finding-v0 --route Farkas --proof-status checked --text width --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_dynamics_euler_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field numerical_analysis --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text residual --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text operator --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text polynomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field numerical_analysis --text floating --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field numerical_analysis --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack numerical-linear-algebra-v0 --route Farkas --proof-status checked --text solution --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack numerical-linear-algebra-v0 --route Farkas --proof-status checked --text Jacobi --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field complex_analysis --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field complex_analysis --text real-pair --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field complex_analysis --text polynomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field complex_analysis --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack complex-plane-transforms-v0 --route Farkas --proof-status checked --text conjugation --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_complex_real_pair_transform --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_complex_real_pair_transform --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field optimization_and_convexity --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field optimization_and_convexity --text objective --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field optimization_and_convexity --text convexity --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field optimization_and_convexity --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_lp_objective_farkas --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_lp_objective_farkas --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_rational_convexity_shadow --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack convexity-rational-v0 --route Farkas --proof-status checked --text threshold --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-separation-v0 --route Farkas --proof-status checked --text combination --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_residual_bound --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_exact_vs_floating_arithmetic --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-kkt-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --text inactive --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-active-set-qp-v0 --route Farkas --proof-status checked --text degenerate --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-sdp-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-sdp-v0 --route Farkas --proof-status checked --text gap --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-gradient-descent-v0 --route Farkas --proof-status checked --text coordinate --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-gradient-descent-v0 --route Farkas --proof-status checked --text bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-line-search-v0 --route Farkas --proof-status checked --text direction --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-line-search-v0 --route Farkas --proof-status checked --text candidate --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-wolfe-line-search-v0 --route Farkas --proof-status checked --text minimizer --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-wolfe-line-search-v0 --route Farkas --proof-status checked --text sufficient-decrease --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-projected-gradient-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --text decrease --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-proximal-gradient-v0 --route Farkas --proof-status checked --text box --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field geometry --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field geometry --text coordinate --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field geometry --text circle --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field geometry --text polynomial --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field geometry --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack affine-geometry-v0 --route Farkas --proof-status checked --text collinearity --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_coordinate_orientation_geometry --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_coordinate_orientation_geometry --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_circle_inversion_cyclic_replay --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_circle_inversion_cyclic_replay --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py fields --field functional_analysis_and_operator_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field functional_analysis_and_operator_theory --text operator --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --field functional_analysis_and_operator_theory --text Chebyshev --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_finite_operator_chebyshev --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_finite_operator_chebyshev --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_eigenpair --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_inner_product_projection --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --concept bridge_tensor_bilinearity --route Alethe --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --concept bridge_tensor_bilinearity --route Alethe --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --route Farkas --proof-status checked --text qf-lra-bad-l1-sum-norm --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --route Farkas --proof-status checked --text qf-lra-bad-operator-bound --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --route Farkas --proof-status checked --text qf-lra-bad-chebyshev-t3 --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-operator-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked --text qf-lra-bad-duplicate-node-grid --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked --text qf-lra-bad-interpolation-sample --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --route Farkas --proof-status checked --text qf-lra-bad-alternating-residual --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack finite-chebyshev-systems-v0 --proof-status replay-only --text rejected --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --pack spectral-linear-algebra-v0 --route Farkas --proof-status checked --require-any >/dev/null
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
