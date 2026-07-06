//! Regression: SMT-LIB string-literal `\u{…}` / `\uXXXX` escape decoding.
//!
//! The bounded byte-model encoder and the code-point word/skeleton route both
//! decoded a string literal by only collapsing the `""` quote escape — they did
//! **not** expand the two SMT-LIB Unicode escapes, so `"\u{62}"` was six raw bytes
//! `\ u { 6 2 }` rather than the single character `b`. Every regex-side decoder
//! *does* expand those escapes, so a script mixing a `str.in_re` literal (or a
//! `re.range` bound) with a string-literal equality got two different denotations
//! for the same text — a **wrong verdict** against Z3/cvc5.
//!
//! This surfaced as the membership fuzz's seed-215 wrong-`sat`:
//! `s0 = "\u{62}" ∧ s0 ∈ (re.comp (re.range "a" "b"))` — `\u{62}` is `b`, which is
//! in `[a-b]`, so it is **not** in the complement ⇒ unsat; the byte-model encoder
//! read `\u{62}` as a six-byte string, which *is* in the complement ⇒ a fabricated
//! `sat`. The fix expands the escapes on every literal route.
//!
//! These checks are deterministic (no external oracle): they assert the direction
//! that matters (a genuinely-unsat shape is never reported `sat`, and vice-versa).

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};
use std::time::Duration;

fn decide(script: &str) -> CheckResult {
    solve_smtlib(
        script,
        &SolverConfig::new().with_timeout(Duration::from_secs(10)),
    )
    .unwrap_or_else(|e| panic!("solve_smtlib errored: {e:?}"))
    .result
}

fn assert_not_sat(script: &str) {
    match decide(script) {
        CheckResult::Sat(m) => panic!("expected non-sat (unsat/unknown), got SAT: {m:?}\n{script}"),
        CheckResult::Unsat | CheckResult::Unknown(_) => {}
    }
}

fn assert_not_unsat(script: &str) {
    if let CheckResult::Unsat = decide(script) {
        panic!("expected non-unsat (sat/unknown), got UNSAT\n{script}");
    }
}

/// The exact seed-215 shape: `\u{62}` is `b`, in `[a-b]`, hence NOT in the
/// complement — unsat. The pre-fix byte model fabricated a `sat` here.
#[test]
fn seed215_escaped_b_in_complement_is_not_sat() {
    assert_not_sat(
        "(set-logic QF_S)\n\
         (declare-const s0 String)\n\
         (assert (and (= s0 \"\\u{62}\") (str.in_re s0 (re.comp (re.range \"a\" \"b\")))))\n\
         (check-sat)",
    );
}

/// The escaped literal `"\u{62}"` and the plain literal `"b"` denote the same
/// string, so their conjunction with a membership behaves identically: `b` IS in
/// `[a-b]`, so `b ∈ comp([a-b])` is false ⇒ unsat.
#[test]
fn escaped_b_membership_matches_plain_b() {
    // `"\u{62}"` in the complement of `[a-b]` — unsat (b is in the range).
    assert_not_sat(
        "(set-logic QF_S)\n(assert (str.in_re \"\\u{62}\" (re.comp (re.range \"a\" \"b\"))))\n(check-sat)",
    );
    // `"\u{62}"` in `[a-b]` — sat (b is in the range).
    assert_not_unsat(
        "(set-logic QF_S)\n(assert (str.in_re \"\\u{62}\" (re.range \"a\" \"b\")))\n(check-sat)",
    );
}

/// `\u{62}` (`b`) equals the plain literal `b`; equating both to one variable is
/// satisfiable, and equating the variable additionally to `a` is not.
#[test]
fn escaped_and_plain_letter_equalities() {
    // s0 = \u{62} ∧ s0 = b — the two literals are equal ⇒ sat.
    assert_not_unsat(
        "(set-logic QF_S)\n(declare-const s0 String)\n(assert (= s0 \"\\u{62}\"))\n(assert (= s0 \"b\"))\n(check-sat)",
    );
    // s0 = \u{62} ∧ s0 = a — b ≠ a ⇒ unsat.
    assert_not_sat(
        "(set-logic QF_S)\n(declare-const s0 String)\n(assert (= s0 \"\\u{62}\"))\n(assert (= s0 \"a\"))\n(check-sat)",
    );
}

/// The 4-digit `\uXXXX` form decodes to the same character as the braced form.
#[test]
fn four_digit_escape_form() {
    // b = b, in comp([a-b]) ⇒ unsat.
    assert_not_sat(
        "(set-logic QF_S)\n(assert (str.in_re \"\\u0062\" (re.comp (re.range \"a\" \"b\"))))\n(check-sat)",
    );
    // c = c, NOT in [a-b], so c ∈ comp([a-b]) ⇒ sat.
    assert_not_unsat(
        "(set-logic QF_S)\n(assert (str.in_re \"\\u0063\" (re.comp (re.range \"a\" \"b\"))))\n(check-sat)",
    );
}
