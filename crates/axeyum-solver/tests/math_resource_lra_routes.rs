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
