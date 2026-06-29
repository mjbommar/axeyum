//! Resource-backed `QF_LRA` proof-route regressions for math curriculum packs.
//!
//! These tests keep the educational resources tied to Axeyum's checked evidence
//! path: the pack-level replay remains useful, but an upgraded `unsat` row must
//! also produce independently rechecked Farkas evidence.

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{Evidence, TrustId, produce_lra_evidence};

fn real(arena: &mut TermArena, name: &str) -> TermId {
    arena.real_var(name).unwrap()
}

fn eq_ratio(arena: &mut TermArena, term: TermId, numerator: i128, denominator: i128) -> TermId {
    let value = arena.real_ratio(numerator, denominator);
    arena.eq(term, value).unwrap()
}

fn assert_farkas_checked(label: &str, arena: &TermArena, assertions: &[TermId]) {
    let report = produce_lra_evidence(arena, assertions).unwrap();
    assert!(
        matches!(&report.evidence, Evidence::UnsatFarkas(_)),
        "{label}: expected Farkas-certified unsat, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified(), "{label}: not certified");
    assert!(
        report.evidence.check(arena, assertions).unwrap(),
        "{label}: evidence failed independent recheck"
    );
    assert_eq!(
        report.provenance.backend, "lra-fourier-motzkin-farkas",
        "{label}: unexpected backend"
    );
    assert!(
        report
            .trusted_steps
            .iter()
            .any(|step| step.id == TrustId::Farkas && step.certified),
        "{label}: missing certified Farkas trust step"
    );
}

#[test]
fn rationals_trichotomy_fixed_unsat_branches_emit_checked_farkas() {
    let mut arena = TermArena::new();
    let left = real(&mut arena, "left");
    let right = real(&mut arena, "right");
    let left_is_quarter = eq_ratio(&mut arena, left, 1, 4);
    let right_is_three_quarters = eq_ratio(&mut arena, right, 3, 4);

    // `1/4 < 3/4`, so every non-less/equality/greater branch of a fixed
    // trichotomy violation closes as an exact-rational Farkas contradiction.
    let not_less = arena.real_ge(left, right).unwrap();
    assert_farkas_checked(
        "rationals-lra-v0 trichotomy non-less branch",
        &arena,
        &[left_is_quarter, right_is_three_quarters, not_less],
    );

    let equal = arena.eq(left, right).unwrap();
    assert_farkas_checked(
        "rationals-lra-v0 trichotomy equality branch",
        &arena,
        &[left_is_quarter, right_is_three_quarters, equal],
    );

    let greater = arena.real_gt(left, right).unwrap();
    assert_farkas_checked(
        "rationals-lra-v0 trichotomy greater-than branch",
        &arena,
        &[left_is_quarter, right_is_three_quarters, greater],
    );
}

#[test]
fn rationals_order_transitivity_fixed_unsat_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let a = real(&mut arena, "a");
    let b = real(&mut arena, "b");
    let c = real(&mut arena, "c");
    let a_is_one_fifth = eq_ratio(&mut arena, a, 1, 5);
    let b_is_two_fifths = eq_ratio(&mut arena, b, 2, 5);
    let c_is_three_fifths = eq_ratio(&mut arena, c, 3, 5);
    let a_lt_b = arena.real_lt(a, b).unwrap();
    let b_lt_c = arena.real_lt(b, c).unwrap();
    let not_a_lt_c = arena.real_ge(a, c).unwrap();

    assert_farkas_checked(
        "rationals-lra-v0 order-transitivity violation",
        &arena,
        &[
            a_is_one_fifth,
            b_is_two_fifths,
            c_is_three_fifths,
            a_lt_b,
            b_lt_c,
            not_a_lt_c,
        ],
    );
}

#[test]
fn linear_algebra_singular_system_inconsistent_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");

    let x_plus_y = arena.real_add(x, y).unwrap();
    let first_row = eq_ratio(&mut arena, x_plus_y, 1, 1);

    let two_x = arena.real_add(x, x).unwrap();
    let two_y = arena.real_add(y, y).unwrap();
    let two_x_plus_two_y = arena.real_add(two_x, two_y).unwrap();
    let second_row = eq_ratio(&mut arena, two_x_plus_two_y, 3, 1);

    assert_farkas_checked(
        "linear-algebra-rational-v0 singular-system-inconsistent",
        &arena,
        &[first_row, second_row],
    );
}

#[test]
fn linear_optimization_objective_threshold_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let x_plus_y = arena.real_add(x, y).unwrap();
    let four = arena.real_ratio(4, 1);
    let five = arena.real_ratio(5, 1);
    let budget = arena.real_le(x_plus_y, four).unwrap();
    let threshold = arena.real_ge(x_plus_y, five).unwrap();

    assert_farkas_checked(
        "linear-optimization-v0 objective-threshold-farkas-infeasible",
        &arena,
        &[budget, threshold],
    );
}

#[test]
fn convexity_bad_midpoint_claim_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let left_value = real(&mut arena, "left_value");
    let midpoint_value = real(&mut arena, "midpoint_value");
    let right_value = real(&mut arena, "right_value");
    let left_is_zero = eq_ratio(&mut arena, left_value, 0, 1);
    let midpoint_is_one = eq_ratio(&mut arena, midpoint_value, 1, 1);
    let right_is_zero = eq_ratio(&mut arena, right_value, 0, 1);

    // Midpoint convexity at weight 1/2 is checked in division-free form:
    // 2*f(midpoint) <= f(left) + f(right). For the bad row this says 2 <= 0.
    let twice_midpoint = arena.real_add(midpoint_value, midpoint_value).unwrap();
    let endpoint_sum = arena.real_add(left_value, right_value).unwrap();
    let midpoint_convexity_claim = arena.real_le(twice_midpoint, endpoint_sum).unwrap();

    assert_farkas_checked(
        "convexity-rational-v0 bad-midpoint-convexity-rejected",
        &arena,
        &[
            left_is_zero,
            midpoint_is_one,
            right_is_zero,
            midpoint_convexity_claim,
        ],
    );
}

#[test]
fn finite_concentration_bad_tail_bound_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let tail_probability = real(&mut arena, "tail_probability");
    let tail_is_quarter = eq_ratio(&mut arena, tail_probability, 1, 4);
    let claimed_bound = arena.real_ratio(1, 8);
    let false_tail_bound = arena.real_le(tail_probability, claimed_bound).unwrap();

    assert_farkas_checked(
        "finite-concentration-v0 bad-concentration-bound-rejected",
        &arena,
        &[tail_is_quarter, false_tail_bound],
    );
}

#[test]
fn finite_probability_bad_normalization_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let heads = real(&mut arena, "heads");
    let tails = real(&mut arena, "tails");
    let total = real(&mut arena, "total");
    let heads_is_half = eq_ratio(&mut arena, heads, 1, 2);
    let tails_is_half = eq_ratio(&mut arena, tails, 1, 2);
    let mass_sum = arena.real_add(heads, tails).unwrap();
    let total_matches_sum = arena.eq(total, mass_sum).unwrap();
    let total_is_three_halves = eq_ratio(&mut arena, total, 3, 2);

    assert_farkas_checked(
        "finite-probability-v0 bad-normalization-rejected",
        &arena,
        &[
            heads_is_half,
            tails_is_half,
            total_matches_sum,
            total_is_three_halves,
        ],
    );
}

#[test]
fn finite_probability_bad_bayes_posterior_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let posterior = real(&mut arena, "posterior");

    // For prior=1/100, sensitivity=9/10, and false_positive_rate=1/20:
    // P(disease and positive)=9/1000 and P(positive)=117/2000. Bayes requires
    // (117/2000)*posterior = 9/1000. The bad row claims posterior=1/5.
    let evidence_probability = arena.real_ratio(117, 2000);
    let weighted_posterior = arena.real_mul(evidence_probability, posterior).unwrap();
    let bayes_equation = eq_ratio(&mut arena, weighted_posterior, 9, 1000);
    let false_posterior = eq_ratio(&mut arena, posterior, 1, 5);

    assert_farkas_checked(
        "finite-probability-v0 bad-bayes-posterior-rejected",
        &arena,
        &[bayes_equation, false_posterior],
    );
}

#[test]
fn finite_markov_chain_bad_stochastic_row_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let p10 = real(&mut arena, "p10");
    let p11 = real(&mut arena, "p11");
    let row_sum = real(&mut arena, "row_sum");
    let p10_is_third = eq_ratio(&mut arena, p10, 1, 3);
    let p11_is_third = eq_ratio(&mut arena, p11, 1, 3);
    let row_entries_sum = arena.real_add(p10, p11).unwrap();
    let row_sum_matches_entries = arena.eq(row_sum, row_entries_sum).unwrap();
    let row_sum_is_one = eq_ratio(&mut arena, row_sum, 1, 1);

    assert_farkas_checked(
        "finite-markov-chain-v0 bad-stochastic-row-rejected",
        &arena,
        &[
            p10_is_third,
            p11_is_third,
            row_sum_matches_entries,
            row_sum_is_one,
        ],
    );
}

#[test]
fn finite_hitting_times_bad_expected_time_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let h_start = real(&mut arena, "h_start");
    let h_middle = real(&mut arena, "h_middle");
    let h_start_is_three = eq_ratio(&mut arena, h_start, 3, 1);
    let h_middle_is_two = eq_ratio(&mut arena, h_middle, 2, 1);

    // Clear denominators from h_start = 1 + (1/2)h_start + (1/2)h_middle:
    // 2*h_start = 2 + h_start + h_middle. With the malformed table this says
    // 6 = 7, an exact-rational Farkas contradiction.
    let two = arena.real_ratio(2, 1);
    let two_h_start = arena.real_mul(two, h_start).unwrap();
    let two_plus_h_start = arena.real_add(two, h_start).unwrap();
    let rhs = arena.real_add(two_plus_h_start, h_middle).unwrap();
    let cleared_equation = arena.eq(two_h_start, rhs).unwrap();

    assert_farkas_checked(
        "finite-hitting-times-v0 bad-expected-time-rejected",
        &arena,
        &[h_start_is_three, h_middle_is_two, cleared_equation],
    );
}

#[test]
fn least_squares_bad_coefficients_emit_checked_farkas() {
    let mut arena = TermArena::new();
    let beta0 = real(&mut arena, "beta0");
    let beta1 = real(&mut arena, "beta1");
    let beta0_is_one = eq_ratio(&mut arena, beta0, 1, 1);
    let beta1_is_one = eq_ratio(&mut arena, beta1, 1, 1);

    // First normal equation for X = [[1,0],[1,1],[1,2]] and y = [1,2,4]:
    // 3*beta0 + 3*beta1 = 7. The bad coefficients (1,1) force 6 = 7.
    let three = arena.real_ratio(3, 1);
    let three_beta0 = arena.real_mul(three, beta0).unwrap();
    let three_beta1 = arena.real_mul(three, beta1).unwrap();
    let lhs = arena.real_add(three_beta0, three_beta1).unwrap();
    let first_normal_equation = eq_ratio(&mut arena, lhs, 7, 1);

    assert_farkas_checked(
        "least-squares-regression-v0 bad-regression-coefficients-rejected",
        &arena,
        &[beta0_is_one, beta1_is_one, first_normal_equation],
    );
}

#[test]
fn real_analysis_bad_linear_delta_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let output_distance = real(&mut arena, "output_distance");
    let output_distance_is_four_thirds = eq_ratio(&mut arena, output_distance, 4, 3);
    let epsilon = arena.real_ratio(1, 1);
    let false_output_bound = arena.real_lt(output_distance, epsilon).unwrap();

    assert_farkas_checked(
        "real-analysis-rational-v0 bad-linear-delta-rejected",
        &arena,
        &[output_distance_is_four_thirds, false_output_bound],
    );
}

#[test]
fn finite_conditional_expectation_bad_table_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let high_block_expectation = real(&mut arena, "high_block_expectation");
    let half = arena.real_ratio(1, 2);
    let weighted_expectation = arena.real_mul(half, high_block_expectation).unwrap();
    let block_average_equation = eq_ratio(&mut arena, weighted_expectation, 3, 1);
    let false_claim = eq_ratio(&mut arena, high_block_expectation, 5, 1);

    assert_farkas_checked(
        "finite-conditional-expectation-v0 bad-conditional-expectation-rejected",
        &arena,
        &[block_average_equation, false_claim],
    );
}

#[test]
fn finite_euler_bad_step_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let state = real(&mut arena, "state");
    let derivative = real(&mut arena, "derivative");
    let next_state = real(&mut arena, "next_state");
    let state_is_one = eq_ratio(&mut arena, state, 1, 1);
    let derivative_is_minus_one = eq_ratio(&mut arena, derivative, -1, 1);

    // Fixed explicit-Euler transition for y' = -y after derivative replay:
    // next_state = state + (1/2)*derivative. The bad row claims 3/4, while the
    // transition forces 1/2.
    let half = arena.real_ratio(1, 2);
    let half_derivative = arena.real_mul(half, derivative).unwrap();
    let transition_rhs = arena.real_add(state, half_derivative).unwrap();
    let euler_step = arena.eq(next_state, transition_rhs).unwrap();
    let false_next_state = eq_ratio(&mut arena, next_state, 3, 4);

    assert_farkas_checked(
        "finite-euler-method-v0 bad-euler-step-rejected",
        &arena,
        &[
            state_is_one,
            derivative_is_minus_one,
            euler_step,
            false_next_state,
        ],
    );
}

#[test]
fn orientation_area_bad_orientation_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let signed_double_area = real(&mut arena, "signed_double_area");
    let area_is_negative_one = eq_ratio(&mut arena, signed_double_area, -1, 1);
    let zero = arena.real_ratio(0, 1);
    let false_ccw_claim = arena.real_gt(signed_double_area, zero).unwrap();

    assert_farkas_checked(
        "orientation-area-geometry-v0 bad-orientation-rejected",
        &arena,
        &[area_is_negative_one, false_ccw_claim],
    );
}

#[test]
fn numerical_linear_algebra_bad_residual_bound_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let residual_inf_norm = real(&mut arena, "residual_inf_norm");
    let norm_is_one = eq_ratio(&mut arena, residual_inf_norm, 1, 1);
    let claimed_bound = arena.real_ratio(1, 2);
    let false_bound = arena.real_le(residual_inf_norm, claimed_bound).unwrap();

    assert_farkas_checked(
        "numerical-linear-algebra-v0 bad-residual-bound-rejected",
        &arena,
        &[norm_is_one, false_bound],
    );
}

#[test]
fn random_matrix_bad_trace_moment_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let expected_trace_square = real(&mut arena, "expected_trace_square");
    let actual_moment = eq_ratio(&mut arena, expected_trace_square, 2, 1);
    let false_moment = eq_ratio(&mut arena, expected_trace_square, 1, 1);

    assert_farkas_checked(
        "random-matrix-finite-v0 bad-trace-moment-rejected",
        &arena,
        &[actual_moment, false_moment],
    );
}

#[test]
fn affine_geometry_bad_distance_preservation_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let original_distance_squared = real(&mut arena, "original_distance_squared");
    let transformed_distance_squared = real(&mut arena, "transformed_distance_squared");
    let original_is_one = eq_ratio(&mut arena, original_distance_squared, 1, 1);
    let transformed_is_five = eq_ratio(&mut arena, transformed_distance_squared, 5, 1);
    let false_preservation = arena
        .eq(original_distance_squared, transformed_distance_squared)
        .unwrap();

    assert_farkas_checked(
        "affine-geometry-v0 bad-distance-preservation-rejected",
        &arena,
        &[original_is_one, transformed_is_five, false_preservation],
    );
}

#[test]
fn inner_product_bad_norm_square_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let norm_square = real(&mut arena, "norm_square");
    let norm_is_negative_one = eq_ratio(&mut arena, norm_square, -1, 1);
    let zero = arena.real_ratio(0, 1);
    let positivity_for_nonzero_vector = arena.real_gt(norm_square, zero).unwrap();

    assert_farkas_checked(
        "inner-product-spaces-rational-v0 bad-inner-product-rejected",
        &arena,
        &[norm_is_negative_one, positivity_for_nonzero_vector],
    );
}

#[test]
fn spectral_bad_eigenpair_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let eigen_image_0 = real(&mut arena, "eigen_image_0");
    let actual_component = eq_ratio(&mut arena, eigen_image_0, 3, 1);
    let false_claimed_component = eq_ratio(&mut arena, eigen_image_0, 2, 1);

    assert_farkas_checked(
        "spectral-linear-algebra-v0 bad-eigenpair-rejected",
        &arena,
        &[actual_component, false_claimed_component],
    );
}

#[test]
fn matrix_invariants_bad_characteristic_polynomial_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let characteristic_value_at_witness = real(&mut arena, "characteristic_value_at_witness");
    let actual_value = eq_ratio(&mut arena, characteristic_value_at_witness, 0, 1);
    let false_claimed_value = eq_ratio(&mut arena, characteristic_value_at_witness, 2, 1);

    assert_farkas_checked(
        "matrix-invariants-v0 bad-characteristic-polynomial-rejected",
        &arena,
        &[actual_value, false_claimed_value],
    );
}
