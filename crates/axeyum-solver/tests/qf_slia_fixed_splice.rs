//! Focused coverage for the correlated bound on generated fixed-position splices.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, online_string_verdict, solve_smtlib};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(5))
}

/// `PyExZ3` spells a one-character overwrite as two substrings around a literal.
/// Naively summing their independent bounds yields `8 + 1 + 8 = 17`, although the
/// exact result never exceeds the base's eight-character bound. Exercise every
/// short-string branch as well as the full-bound case; each SAT model is replayed
/// by the front door against the original formula.
#[test]
fn fixed_splice_uses_correlated_bound_and_preserves_short_strings() {
    for (source, expected) in [
        ("", "X"),
        ("a", "aX"),
        ("ab", "aX"),
        ("abc", "aXc"),
        ("abcdefgh", "aXcdefgh"),
    ] {
        let script = format!(
            r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= s "{source}"))
(assert (= (str.++ (str.++ (str.substr s 0 (- 1 0)) "X")
                    (str.substr s 2 (- (str.len s) 2)))
           "{expected}"))
(check-sat)
"#
        );
        let result = solve_smtlib(&script, &config())
            .unwrap_or_else(|error| panic!("fixed splice must parse and solve: {error:?}"));
        assert!(
            matches!(result.result, CheckResult::Sat(_)),
            "fixed splice over {source:?} must equal {expected:?}; got {:?}",
            result.result
        );
    }
}

/// The UNSAT-only word relaxation may treat a repeated fixed splice as one opaque
/// Seq term: every real model induces the same abstract value, so an equality plus
/// disequality is a valid original-theory contradiction. The generated ground and
/// empty-length guards must survive into the Boolean skeleton as well.
#[test]
fn opaque_fixed_splice_equality_conflict_is_unsat() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun end () String)
(assert
  (and
    (not (not (= (ite (= (str.++ (str.++ (str.substr s 0 (- 0 0)) "X")
                                      (str.substr s 1 (- (str.len s) 1))) end)
                         1 0) 0)))
    (not (= (ite (= end (str.++ (str.++ (str.substr s 0 (- 0 0)) "X")
                                  (str.substr s 1 (- (str.len s) 1))))
                 1 0) 0))
    (not (not (= (ite (<= (str.len s) 0) 1 0) 0)))
    (>= (- 0 0) 0)
    (>= (- (str.len s) 1) 0)))
(check-sat)
"#;
    let mut script = parse_script(input).expect("parse fixed-splice conflict");
    assert!(script.word_skeleton_opaque_terms > 0);
    assert_eq!(
        online_string_verdict(&mut script, &config()),
        Some(CheckResult::Unsat)
    );
    assert_eq!(
        solve_smtlib(input, &config())
            .expect("solve fixed-splice conflict")
            .result,
        CheckResult::Unsat
    );
}

/// A model of the opaque relaxation does not prove the original splice formula
/// satisfiable. The public online entry point must therefore discard SAT whenever
/// the skeleton contains an opaque fixed-splice term.
#[test]
fn opaque_fixed_splice_relaxation_never_reports_sat() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun end () String)
(assert (= end (str.++ (str.++ (str.substr s 0 (- 0 0)) "X")
                         (str.substr s 1 (- (str.len s) 1)))))
(assert (not (<= (str.len s) 0)))
(assert (>= (- 0 0) 0))
(assert (>= (- (str.len s) 1) 0))
(check-sat)
"#;
    let mut script = parse_script(input).expect("parse satisfiable fixed-splice relaxation");
    assert!(script.word_skeleton_opaque_terms > 0);
    assert_eq!(online_string_verdict(&mut script, &config()), None);
}
