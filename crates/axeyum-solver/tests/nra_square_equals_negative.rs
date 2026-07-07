//! Front-door regression for P2.5 slice 2: an integer numeral in a real
//! equality (`a² = −k`, parsed as `(= (* a a) (to_real (- k)))`) reaches the
//! exact NRA decider via the `to_real(<const>)` fold + even-power-equality arm,
//! and is decided **unsat** — while the satisfiable `a² = k` (k > 0) stays sat.

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto, check_with_nra};

fn verdict(text: &str) -> CheckResult {
    let mut script = parse_script(text).expect("parse");
    check_auto(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .expect("check_auto")
}

fn is_unsat(text: &str) -> bool {
    matches!(verdict(text), CheckResult::Unsat)
}

fn is_sat(text: &str) -> bool {
    matches!(verdict(text), CheckResult::Sat(_))
}

const HDR: &str = "(set-logic QF_NRA)\n(declare-fun a () Real)\n(declare-fun b () Real)\n";

#[test]
fn square_equals_negative_int_numeral_is_unsat() {
    // The exact `very-simple-unsat` shape.
    assert!(is_unsat(&format!(
        "{HDR}(assert (= (* a a) (- 2)))\n(check-sat)"
    )));
}

#[test]
fn square_equals_negative_real_numeral_is_unsat() {
    assert!(is_unsat(&format!(
        "{HDR}(assert (= (* a a) (- 2.0)))\n(check-sat)"
    )));
}

#[test]
fn fourth_power_equals_negative_is_unsat() {
    assert!(is_unsat(&format!(
        "{HDR}(assert (= (* (* a a) (* a a)) (- 1)))\n(check-sat)"
    )));
}

#[test]
fn even_power_sum_equals_negative_is_unsat() {
    assert!(is_unsat(&format!(
        "{HDR}(assert (= (+ (* a a) (* b b)) (- 3)))\n(check-sat)"
    )));
}

#[test]
fn mirrored_negative_equals_square_is_unsat() {
    assert!(is_unsat(&format!(
        "{HDR}(assert (= (- 5) (* a a)))\n(check-sat)"
    )));
}

// ---- NEGATIVE tests: the coercion + even-power arm must NOT over-fire. ----

#[test]
fn square_equals_positive_stays_sat() {
    // a² = 2 IS satisfiable (a = ±√2) — must never be reported unsat.
    assert!(is_sat(&format!("{HDR}(assert (= (* a a) 2))\n(check-sat)")));
}

#[test]
fn square_equals_positive_int_coercion_not_unsat() {
    // `a² = (+ 0 2)` (with an int-coerced RHS) is satisfiable (a = ±√2). It is
    // outside this narrow slice (the RHS is positive, so the even-power arm
    // declines and it falls to the coercion relaxation), so it may be `unknown`
    // — the soundness bar is only that it must NEVER be reported unsat.
    assert!(!is_unsat(&format!(
        "{HDR}(assert (= (* a a) (+ 0 2)))\n(check-sat)"
    )));
}

#[test]
fn square_equals_zero_stays_sat() {
    // a² = 0 (a = 0) is sat; RHS is not negative, arm must not fire.
    assert!(is_sat(&format!("{HDR}(assert (= (* a a) 0))\n(check-sat)")));
}

#[test]
fn odd_power_equals_negative_not_unsat() {
    // a³ = −2 (a = −∛2) IS satisfiable — an odd power is not sign-definite, so
    // the even-power arm must decline. It may be `unknown` (outside the slice),
    // but must NEVER be reported unsat.
    assert!(!is_unsat(&format!(
        "{HDR}(assert (= (* (* a a) a) (- 2)))\n(check-sat)"
    )));
}

/// The NRA collector must see through a `to_real(<int const>)` right side (the
/// coercion routing): calling `check_with_nra` directly — which bypasses the
/// `check_auto` coercion relaxation — on `a² = to_real(3)` reaches the exact
/// real decider and returns a decision (sat, a = ±√3), not `unknown`.
#[test]
fn collect_through_to_real_reaches_exact_decider() {
    let mut script = parse_script(&format!(
        "{HDR}(assert (= (* a a) (to_real 3)))\n(check-sat)"
    ))
    .expect("parse");
    let res = check_with_nra(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .expect("check_with_nra");
    assert!(
        matches!(res, CheckResult::Sat(_)),
        "a² = to_real(3) should be sat via the exact decider, got {res:?}"
    );
}

/// The direct-`check_with_nra` unsat path for the coerced negative constant.
#[test]
fn collect_through_to_real_negative_is_unsat_direct() {
    let mut script = parse_script(&format!(
        "{HDR}(assert (= (* a a) (to_real (- 2))))\n(check-sat)"
    ))
    .expect("parse");
    let res = check_with_nra(
        &mut script.arena,
        &script.assertions,
        &SolverConfig::default(),
    )
    .expect("check_with_nra");
    assert!(matches!(res, CheckResult::Unsat), "got {res:?}");
}

/// Property: for every k in a small range, `a² = k` is unsat iff k < 0, and
/// never the reverse (the soundness bar — never refute a satisfiable formula).
#[test]
fn property_square_equals_k_both_directions() {
    for k in -6_i64..=6 {
        let rhs = if k < 0 {
            format!("(- {})", -k)
        } else {
            k.to_string()
        };
        let text = format!("{HDR}(assert (= (* a a) {rhs}))\n(check-sat)");
        let v = verdict(&text);
        if k < 0 {
            assert!(
                matches!(v, CheckResult::Unsat),
                "a² = {k} should be unsat, got {v:?}"
            );
        } else {
            // k ≥ 0 has a real root ±√k — must be sat, NEVER unsat.
            assert!(
                !matches!(v, CheckResult::Unsat),
                "a² = {k} must not be unsat (a = ±√{k}), got {v:?}"
            );
        }
    }
}
