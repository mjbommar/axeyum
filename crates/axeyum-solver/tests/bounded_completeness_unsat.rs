//! End-to-end bounded-completeness UNSAT route (task #75). A bounded-complete
//! string query whose bounded encoding is unsat is upgraded from the
//! "no model within the bounded integer width" `unknown` to a real `unsat`
//! (see docs/research/01-foundations/bounded-string-completeness-unsat.md).
//! Every upgraded verdict was cross-checked against cvc5 (`DISAGREE=0` on the
//! whole `QF_S`/`QF_SLIA` corpus) before landing.

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn verdict(text: &str) -> CheckResult {
    solve_smtlib(text, &config()).expect("decides").result
}

/// The two cvc5 `update-ex2` corpus shapes: `str.update`'s unsat targets that
/// the encoding alone left `unknown` (int-blast cannot prove unsat from a
/// no-bounded-model result), now decided `unsat` because `s` is length-capped
/// `< 3` so the query is bounded-complete. cvc5 agrees (`:status unsat`).
#[test]
fn update_ex2_qf_slia_decides_unsat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                (assert (not (= (str.substr (str.update \"AAAAAA\" 1 s) 5 1) \"A\")))\n\
                (assert (< (str.len s) 3))\n(check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// A ground string unsat (no free vars → bounded-complete vacuously) is now
/// decided `unsat` rather than left `unknown`.
#[test]
fn ground_string_unsat_decides_unsat() {
    let text = "(set-logic QF_S)\n\
                (assert (not (= (str.update \"AAAAAA\" 1 \"B\") \"ABAAAA\")))\n(check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// SOUNDNESS: a free unbounded Int (C1) must NOT let the route upgrade — the
/// width-32 no-model is genuinely inconclusive. This query is sat; the route
/// must never turn it into unsat.
#[test]
fn free_int_is_not_wrongly_unsat() {
    let text = "(set-logic QF_SLIA)\n(declare-fun x () Int)\n(declare-fun s () String)\n\
                (assert (< (str.len s) 3))\n(assert (> x 5))\n\
                (assert (not (= (str.substr s 0 1) \"A\")))\n(check-sat)\n";
    assert!(
        matches!(verdict(text), CheckResult::Sat(_) | CheckResult::Unknown(_)),
        "a free Int must block the bounded-completeness upgrade"
    );
    // The analyzer itself must reject it.
    assert!(!axeyum_smtlib::is_bounded_complete(text));
}

/// SOUNDNESS: an unbounded String var (C2) must be rejected by the analyzer —
/// a real model may need `s` longer than the cap. (The end-to-end verdict on
/// `(str.at s 100)` is a SEPARATE pre-existing base-solver wrong-unsat, tracked
/// as task #76; here we lock that the #75 analyzer does not sanction it.)
#[test]
fn unbounded_string_analyzer_rejects() {
    for text in [
        "(set-logic QF_S)\n(declare-fun s () String)\n(assert (= (str.at s 100) \"x\"))\n(check-sat)\n",
        "(set-logic QF_S)\n(declare-fun s () String)\n(assert (> (str.len s) 100))\n(check-sat)\n",
        "(set-logic QF_S)\n(declare-fun s () String)\n(assert (not (= (str.substr s 0 1) \"A\")))\n(check-sat)\n",
    ] {
        assert!(
            !axeyum_smtlib::is_bounded_complete(text),
            "an unbounded String var must block the upgrade: {text}"
        );
    }
}

/// Regression for the pre-existing wrong-unsat (#76): `str.at` at a CONSTANT
/// index beyond the packed cap on a SYMBOLIC string used to fold to a hard `""`,
/// making `(= (str.at s 100) "x")` a wrong `unsat` (cvc5: sat, `s` = 101 chars
/// with 'x' at 100). It must now be sound — never `unsat` (the fix routes it
/// through the Int mux → `unknown`).
#[test]
fn str_at_past_cap_symbolic_is_not_wrongly_unsat() {
    let text = "(set-logic QF_S)\n(declare-fun s () String)\n\
                (assert (= (str.at s 100) \"x\"))\n(check-sat)\n";
    assert_ne!(
        verdict(text),
        CheckResult::Unsat,
        "str.at past cap on a symbolic string must not fold to a wrong unsat (#76)"
    );
}

/// The bounded-complete counterpart: with `s` length-capped `≤ 8 < 100`,
/// `str.at s 100` is genuinely `""`, so the query IS unsat — decided via the
/// bounded-completeness route (#75).
#[test]
fn str_at_past_cap_length_capped_is_unsat() {
    let text = "(set-logic QF_S)\n(declare-fun s () String)\n\
                (assert (<= (str.len s) 8))\n(assert (= (str.at s 100) \"x\"))\n(check-sat)\n";
    assert_eq!(verdict(text), CheckResult::Unsat);
}

/// In-cap constant `str.at` folds are unchanged (regression guard).
#[test]
fn str_at_in_cap_still_folds() {
    assert!(matches!(
        verdict("(set-logic QF_S)\n(assert (= (str.at \"abc\" 1) \"b\"))\n(check-sat)\n"),
        CheckResult::Sat(_)
    ));
    assert_eq!(
        verdict("(set-logic QF_S)\n(assert (= (str.at \"abc\" 1) \"x\"))\n(check-sat)\n"),
        CheckResult::Unsat
    );
}
