//! Resource-backed `QF_LRA` proof-route regressions for math curriculum packs.
//!
//! These tests keep the educational resources tied to Axeyum's checked evidence
//! path: the pack-level replay remains useful, but an upgraded `unsat` row must
//! also produce independently rechecked Farkas evidence.

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, TrustId, check_auto, produce_lra_evidence,
};

const LINEAR_ALGEBRA_SINGULAR_SYSTEM: &str = include_str!(
    "../../../artifacts/examples/math/linear-algebra-rational-v0/smt2/singular-system-inconsistent-farkas-conflict.smt2"
);
const LINEAR_OPTIMIZATION_OBJECTIVE_THRESHOLD: &str = include_str!(
    "../../../artifacts/examples/math/linear-optimization-v0/smt2/objective-threshold-farkas-conflict.smt2"
);
const CONVEXITY_BAD_MIDPOINT: &str = include_str!(
    "../../../artifacts/examples/math/convexity-rational-v0/smt2/bad-midpoint-convexity-farkas-conflict.smt2"
);
const CALCULUS_RIEMANN_FALSE_INTEGRAL: &str = include_str!(
    "../../../artifacts/examples/math/calculus-riemann-sum-v0/smt2/false-integral-farkas-conflict.smt2"
);
const CALCULUS_ALGEBRAIC_FALSE_DERIVATIVE: &str = include_str!(
    "../../../artifacts/examples/math/calculus-algebraic-shadow-v0/smt2/false-derivative-farkas-conflict.smt2"
);
const POLYNOMIAL_FACTORIZATION_IRREDUCIBLE_QUADRATIC_DISCRIMINANT: &str = include_str!(
    "../../../artifacts/examples/math/polynomial-factorization-rational-v0/smt2/irreducible-quadratic-discriminant-farkas-conflict.smt2"
);
const REALS_RCF_NEGATIVE_DISCRIMINANT: &str = include_str!(
    "../../../artifacts/examples/math/reals-rcf-shadow-v0/smt2/negative-discriminant-farkas-conflict.smt2"
);
const COMPLEX_ALGEBRAIC_BAD_NORM_SQUARED: &str = include_str!(
    "../../../artifacts/examples/math/complex-algebraic-v0/smt2/bad-norm-squared-farkas-conflict.smt2"
);
const COMPLEX_PLANE_BAD_UNIT_SQUARE_REAL_PART: &str = include_str!(
    "../../../artifacts/examples/math/complex-plane-transforms-v0/smt2/bad-unit-square-real-part-farkas-conflict.smt2"
);
const SEQUENCE_LIMIT_BOUNDED_CAUCHY: &str = include_str!(
    "../../../artifacts/examples/math/sequence-limit-shadow-v0/smt2/bounded-cauchy-tail-farkas-conflict.smt2"
);
const BOUNDED_MONOTONE_SEQUENCE_BAD_UPPER_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/bounded-monotone-sequence-v0/smt2/bad-upper-bound-farkas-conflict.smt2"
);
const FINITE_RECURRENCE_PREFIX_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-recurrence-prefix-v0/smt2/bad-fibonacci-value-farkas-conflict.smt2"
);
const FINITE_ROOT_FINDING_BAD_NEWTON_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-root-finding-v0/smt2/bad-newton-step-farkas-conflict.smt2"
);
const FINITE_SEPARATION_BAD_SEPARATOR: &str = include_str!(
    "../../../artifacts/examples/math/finite-separation-v0/smt2/bad-separator-farkas-conflict.smt2"
);
const FINITE_KKT_BAD_STATIONARITY: &str = include_str!(
    "../../../artifacts/examples/math/finite-kkt-v0/smt2/bad-stationarity-farkas-conflict.smt2"
);
const FINITE_SDP_BAD_OBJECTIVE: &str = include_str!(
    "../../../artifacts/examples/math/finite-sdp-v0/smt2/bad-objective-farkas-conflict.smt2"
);
const FINITE_GRADIENT_DESCENT_BAD_DECREASE: &str = include_str!(
    "../../../artifacts/examples/math/finite-gradient-descent-v0/smt2/bad-decrease-farkas-conflict.smt2"
);
const FINITE_LINE_SEARCH_BAD_ARMIJO: &str = include_str!(
    "../../../artifacts/examples/math/finite-line-search-v0/smt2/bad-armijo-farkas-conflict.smt2"
);
const FINITE_WOLFE_LINE_SEARCH_BAD_CURVATURE: &str = include_str!(
    "../../../artifacts/examples/math/finite-wolfe-line-search-v0/smt2/bad-wolfe-curvature-farkas-conflict.smt2"
);
const FINITE_PROJECTED_GRADIENT_BAD_PROJECTION: &str = include_str!(
    "../../../artifacts/examples/math/finite-projected-gradient-v0/smt2/bad-projection-farkas-conflict.smt2"
);
const FINITE_PROXIMAL_GRADIENT_BAD_PROXIMAL_POINT: &str = include_str!(
    "../../../artifacts/examples/math/finite-proximal-gradient-v0/smt2/bad-proximal-point-farkas-conflict.smt2"
);
const MULTIVARIABLE_CALCULUS_BAD_GRADIENT: &str = include_str!(
    "../../../artifacts/examples/math/multivariable-calculus-rational-v0/smt2/bad-gradient-farkas-conflict.smt2"
);
const FINITE_MEASURE_BAD_COMPLEMENT: &str = include_str!(
    "../../../artifacts/examples/math/finite-measure-v0/smt2/bad-complement-measure-farkas-conflict.smt2"
);
const FINITE_MEASURE_MONOTONICITY_BAD_SUBSET_MEASURE: &str = include_str!(
    "../../../artifacts/examples/math/finite-measure-monotonicity-v0/smt2/bad-subset-measure-farkas-conflict.smt2"
);
const COORDINATE_GEOMETRY_BAD_DISTANCE_SQUARED: &str = include_str!(
    "../../../artifacts/examples/math/coordinate-geometry-v0/smt2/bad-distance-squared-farkas-conflict.smt2"
);
const INCIDENCE_GEOMETRY_BAD_POINT_ON_LINE: &str = include_str!(
    "../../../artifacts/examples/math/incidence-geometry-v0/smt2/bad-incidence-farkas-conflict.smt2"
);
const RIGID_CONFIGURATION_BAD_DISTANCE_TABLE: &str = include_str!(
    "../../../artifacts/examples/math/rigid-configuration-geometry-v0/smt2/bad-rigid-distance-table-farkas-conflict.smt2"
);
const FINITE_OPERATOR_BAD_OPERATOR_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/finite-operator-v0/smt2/bad-operator-bound-farkas-conflict.smt2"
);
const BOUNDED_DYNAMICS_BAD_INVARIANT_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/bounded-dynamics-v0/smt2/bad-invariant-bound-farkas-conflict.smt2"
);
const RATIONALS_TRICHOTOMY_NONLESS: &str = include_str!(
    "../../../artifacts/examples/math/rationals-lra-v0/smt2/trichotomy-nonless-farkas-conflict.smt2"
);
const RATIONALS_TRICHOTOMY_EQUALITY: &str = include_str!(
    "../../../artifacts/examples/math/rationals-lra-v0/smt2/trichotomy-equality-farkas-conflict.smt2"
);
const RATIONALS_TRICHOTOMY_GREATER: &str = include_str!(
    "../../../artifacts/examples/math/rationals-lra-v0/smt2/trichotomy-greater-farkas-conflict.smt2"
);
const RATIONALS_ORDER_TRANSITIVITY: &str = include_str!(
    "../../../artifacts/examples/math/rationals-lra-v0/smt2/order-transitivity-farkas-conflict.smt2"
);

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

fn assert_resource_farkas(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: resource SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: resource obligation must be unsat"
    );
    assert_farkas_checked(label, &script.arena, &assertions);
}

fn assert_resource_farkas_rejects_tampered_certificate(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: resource SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: resource obligation must be unsat before tampering"
    );

    let report = produce_lra_evidence(&script.arena, &assertions).unwrap();
    let Evidence::UnsatFarkas(mut certificate) = report.evidence else {
        panic!("{label}: expected Farkas-certified unsat");
    };
    assert!(
        certificate.verify(),
        "{label}: genuine certificate must verify before tampering"
    );
    assert!(
        Evidence::UnsatFarkas(certificate.clone())
            .check(&script.arena, &assertions)
            .unwrap(),
        "{label}: genuine evidence must independently check before tampering"
    );

    certificate.multipliers[0] = Rational::zero();
    let bogus = Evidence::UnsatFarkas(certificate);
    assert!(
        !bogus.check(&script.arena, &assertions).unwrap(),
        "{label}: tampering a Farkas multiplier must make evidence reject"
    );
}

#[test]
fn qf_lra_resource_route_rejects_tampered_farkas_certificate() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let x_ge_one = arena.real_ge(x, one).unwrap();
    let x_le_zero = arena.real_le(x, zero).unwrap();
    let assertions = [x_ge_one, x_le_zero];

    let report = produce_lra_evidence(&arena, &assertions).unwrap();
    let Evidence::UnsatFarkas(mut certificate) = report.evidence else {
        panic!("expected Farkas-certified unsat");
    };
    assert!(certificate.verify());

    certificate.multipliers[0] = Rational::zero();
    let bogus = Evidence::UnsatFarkas(certificate);
    assert!(
        !bogus.check(&arena, &assertions).unwrap(),
        "tampering a Farkas multiplier must make evidence reject"
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
fn rationals_trichotomy_source_artifacts_emit_checked_farkas() {
    for (label, smt2) in [
        (
            "rationals-lra-v0 trichotomy non-less SMT-LIB artifact",
            RATIONALS_TRICHOTOMY_NONLESS,
        ),
        (
            "rationals-lra-v0 trichotomy equality SMT-LIB artifact",
            RATIONALS_TRICHOTOMY_EQUALITY,
        ),
        (
            "rationals-lra-v0 trichotomy greater SMT-LIB artifact",
            RATIONALS_TRICHOTOMY_GREATER,
        ),
    ] {
        assert_resource_farkas(label, smt2);
    }
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
fn rationals_order_transitivity_source_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "rationals-lra-v0 order-transitivity SMT-LIB artifact",
        RATIONALS_ORDER_TRANSITIVITY,
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
fn linear_algebra_singular_system_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "linear-algebra-rational-v0 singular-system-inconsistent SMT-LIB artifact",
        LINEAR_ALGEBRA_SINGULAR_SYSTEM,
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
fn linear_optimization_objective_threshold_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "linear-optimization-v0 objective-threshold SMT-LIB artifact",
        LINEAR_OPTIMIZATION_OBJECTIVE_THRESHOLD,
    );
}

#[test]
fn linear_optimization_objective_threshold_rejects_tampered_farkas_certificate() {
    assert_resource_farkas_rejects_tampered_certificate(
        "linear-optimization-v0 objective-threshold SMT-LIB artifact",
        LINEAR_OPTIMIZATION_OBJECTIVE_THRESHOLD,
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
fn convexity_bad_midpoint_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "convexity-rational-v0 bad-midpoint SMT-LIB artifact",
        CONVEXITY_BAD_MIDPOINT,
    );
}

#[test]
fn calculus_riemann_sum_false_integral_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "calculus-riemann-sum-v0 false-integral SMT-LIB artifact",
        CALCULUS_RIEMANN_FALSE_INTEGRAL,
    );
}

#[test]
fn calculus_algebraic_false_derivative_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "calculus-algebraic-shadow-v0 false-derivative SMT-LIB artifact",
        CALCULUS_ALGEBRAIC_FALSE_DERIVATIVE,
    );
}

#[test]
fn polynomial_factorization_irreducible_quadratic_discriminant_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "polynomial-factorization-rational-v0 irreducible quadratic discriminant SMT-LIB artifact",
        POLYNOMIAL_FACTORIZATION_IRREDUCIBLE_QUADRATIC_DISCRIMINANT,
    );
}

#[test]
fn reals_rcf_shadow_negative_discriminant_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "reals-rcf-shadow-v0 negative-discriminant SMT-LIB artifact",
        REALS_RCF_NEGATIVE_DISCRIMINANT,
    );
}

#[test]
fn complex_plane_bad_unit_square_real_part_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "complex-plane-transforms-v0 bad-unit-square-real-part SMT-LIB artifact",
        COMPLEX_PLANE_BAD_UNIT_SQUARE_REAL_PART,
    );
}

#[test]
fn complex_algebraic_bad_norm_squared_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "complex-algebraic-v0 bad-norm-squared SMT-LIB artifact",
        COMPLEX_ALGEBRAIC_BAD_NORM_SQUARED,
    );
}

#[test]
fn sequence_limit_bounded_cauchy_tail_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "sequence-limit-shadow-v0 bounded-Cauchy-tail SMT-LIB artifact",
        SEQUENCE_LIMIT_BOUNDED_CAUCHY,
    );
}

#[test]
fn bounded_monotone_sequence_bad_upper_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "bounded-monotone-sequence-v0 bad-upper-bound SMT-LIB artifact",
        BOUNDED_MONOTONE_SEQUENCE_BAD_UPPER_BOUND,
    );
}

#[test]
fn finite_recurrence_prefix_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-recurrence-prefix-v0 bad-Fibonacci-value SMT-LIB artifact",
        FINITE_RECURRENCE_PREFIX_BAD_VALUE,
    );
}

#[test]
fn finite_root_finding_bad_newton_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-root-finding-v0 bad-Newton-step SMT-LIB artifact",
        FINITE_ROOT_FINDING_BAD_NEWTON_STEP,
    );
}

#[test]
fn finite_separation_bad_separator_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-separation-v0 bad-separator SMT-LIB artifact",
        FINITE_SEPARATION_BAD_SEPARATOR,
    );
}

#[test]
fn finite_kkt_bad_stationarity_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-kkt-v0 bad-stationarity SMT-LIB artifact",
        FINITE_KKT_BAD_STATIONARITY,
    );
}

#[test]
fn finite_sdp_bad_objective_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-sdp-v0 bad-objective SMT-LIB artifact",
        FINITE_SDP_BAD_OBJECTIVE,
    );
}

#[test]
fn finite_gradient_descent_bad_decrease_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-gradient-descent-v0 bad-decrease SMT-LIB artifact",
        FINITE_GRADIENT_DESCENT_BAD_DECREASE,
    );
}

#[test]
fn finite_line_search_bad_armijo_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-line-search-v0 bad-Armijo SMT-LIB artifact",
        FINITE_LINE_SEARCH_BAD_ARMIJO,
    );
}

#[test]
fn finite_wolfe_line_search_bad_curvature_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-wolfe-line-search-v0 bad-Wolfe-curvature SMT-LIB artifact",
        FINITE_WOLFE_LINE_SEARCH_BAD_CURVATURE,
    );
}

#[test]
fn finite_projected_gradient_bad_projection_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-projected-gradient-v0 bad-projection SMT-LIB artifact",
        FINITE_PROJECTED_GRADIENT_BAD_PROJECTION,
    );
}

#[test]
fn finite_proximal_gradient_bad_proximal_point_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-proximal-gradient-v0 bad-proximal-point SMT-LIB artifact",
        FINITE_PROXIMAL_GRADIENT_BAD_PROXIMAL_POINT,
    );
}

#[test]
fn multivariable_calculus_bad_gradient_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "multivariable-calculus-rational-v0 bad-gradient SMT-LIB artifact",
        MULTIVARIABLE_CALCULUS_BAD_GRADIENT,
    );
}

#[test]
fn coordinate_geometry_bad_distance_squared_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "coordinate-geometry-v0 bad-distance-squared SMT-LIB artifact",
        COORDINATE_GEOMETRY_BAD_DISTANCE_SQUARED,
    );
}

#[test]
fn incidence_geometry_bad_point_on_line_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "incidence-geometry-v0 bad-incidence SMT-LIB artifact",
        INCIDENCE_GEOMETRY_BAD_POINT_ON_LINE,
    );
}

#[test]
fn rigid_configuration_bad_distance_table_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "rigid-configuration-geometry-v0 bad-distance-table SMT-LIB artifact",
        RIGID_CONFIGURATION_BAD_DISTANCE_TABLE,
    );
}

#[test]
fn finite_operator_bad_operator_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-operator-v0 bad-operator-bound SMT-LIB artifact",
        FINITE_OPERATOR_BAD_OPERATOR_BOUND,
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
fn finite_chebyshev_duplicate_node_grid_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let determinant = real(&mut arena, "determinant");
    let determinant_is_zero = eq_ratio(&mut arena, determinant, 0, 1);
    let false_nonzero_determinant = eq_ratio(&mut arena, determinant, 1, 1);

    assert_farkas_checked(
        "finite-chebyshev-systems-v0 bad-duplicate-node-grid-rejected",
        &arena,
        &[determinant_is_zero, false_nonzero_determinant],
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
fn finite_product_measure_bad_probability_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let product_probability = real(&mut arena, "product_probability");
    let replay_computed_mass = eq_ratio(&mut arena, product_probability, 1, 6);
    let false_claimed_mass = eq_ratio(&mut arena, product_probability, 1, 5);

    assert_farkas_checked(
        "finite-product-measure-v0 bad-product-measure-rejected",
        &arena,
        &[replay_computed_mass, false_claimed_mass],
    );
}

#[test]
fn finite_measure_bad_complement_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-measure-v0 bad-complement SMT-LIB artifact",
        FINITE_MEASURE_BAD_COMPLEMENT,
    );
}

#[test]
fn finite_measure_monotonicity_bad_subset_measure_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-measure-monotonicity-v0 bad-subset-measure SMT-LIB artifact",
        FINITE_MEASURE_MONOTONICITY_BAD_SUBSET_MEASURE,
    );
}

#[test]
fn finite_random_variables_bad_pushforward_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let long_probability = real(&mut arena, "long_probability");
    let replay_computed_mass = eq_ratio(&mut arena, long_probability, 1, 4);
    let false_claimed_mass = eq_ratio(&mut arena, long_probability, 1, 2);

    assert_farkas_checked(
        "finite-random-variables-v0 bad-pushforward-rejected",
        &arena,
        &[replay_computed_mass, false_claimed_mass],
    );
}

#[test]
fn finite_integration_bad_expectation_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let integral_value = real(&mut arena, "integral_value");
    let replay_computed_integral = eq_ratio(&mut arena, integral_value, 5, 2);
    let false_claimed_integral = eq_ratio(&mut arena, integral_value, 3, 1);

    assert_farkas_checked(
        "finite-integration-v0 bad-expectation-rejected",
        &arena,
        &[replay_computed_integral, false_claimed_integral],
    );
}

#[test]
fn finite_martingales_bad_conditional_expectation_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let up_block_conditional_expectation = real(&mut arena, "up_block_conditional_expectation");
    let replay_computed_expectation = eq_ratio(&mut arena, up_block_conditional_expectation, 3, 2);
    let false_martingale_equality = eq_ratio(&mut arena, up_block_conditional_expectation, 1, 1);

    assert_farkas_checked(
        "finite-martingales-v0 bad-martingale-rejected",
        &arena,
        &[replay_computed_expectation, false_martingale_equality],
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
fn metric_continuity_bad_delta_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let output_distance = real(&mut arena, "output_distance");
    let output_distance_is_epsilon = eq_ratio(&mut arena, output_distance, 1, 1);
    let epsilon = arena.real_ratio(1, 1);
    let false_output_bound = arena.real_lt(output_distance, epsilon).unwrap();

    assert_farkas_checked(
        "metric-continuity-v0 bad-delta-rejected",
        &arena,
        &[output_distance_is_epsilon, false_output_bound],
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
fn finite_stochastic_kernel_bad_row_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let rainy_walk = real(&mut arena, "rainy_walk");
    let rainy_bus = real(&mut arena, "rainy_bus");
    let rainy_row_sum = real(&mut arena, "rainy_row_sum");
    let rainy_walk_is_three_fifths = eq_ratio(&mut arena, rainy_walk, 3, 5);
    let rainy_bus_is_three_fifths = eq_ratio(&mut arena, rainy_bus, 3, 5);
    let row_entries_sum = arena.real_add(rainy_walk, rainy_bus).unwrap();
    let row_sum_matches_entries = arena.eq(rainy_row_sum, row_entries_sum).unwrap();
    let row_sum_is_one = eq_ratio(&mut arena, rainy_row_sum, 1, 1);

    assert_farkas_checked(
        "finite-stochastic-kernels-v0 bad-kernel-row-rejected",
        &arena,
        &[
            rainy_walk_is_three_fifths,
            rainy_bus_is_three_fifths,
            row_sum_matches_entries,
            row_sum_is_one,
        ],
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
fn bounded_dynamics_bad_invariant_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "bounded-dynamics-v0 bad-invariant-bound SMT-LIB artifact",
        BOUNDED_DYNAMICS_BAD_INVARIANT_BOUND,
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
