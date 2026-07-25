//! Focused coverage for the correlated bound on generated fixed-position splices.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

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
