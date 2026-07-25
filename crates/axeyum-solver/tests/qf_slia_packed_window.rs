//! Focused front-door coverage for the 12-byte packed SMT-LIB string window.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

#[test]
fn lengths_nine_through_eleven_replay_sat_with_content_constraints() {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(2));

    for length in [9, 10, 11] {
        let last = length - 1;
        let input = format!(
            "(set-logic QF_SLIA)\n\
             (declare-fun s () String)\n\
             (assert (= (str.len s) {length}))\n\
             (assert (= (str.at s {last}) \"X\"))\n\
             (assert (= (str.len (str.substr s {last} 1)) 1))\n\
             (check-sat)\n"
        );
        let outcome = solve_smtlib(&input, &config).expect("supported packed string query");
        assert!(
            matches!(outcome.result, CheckResult::Sat(_)),
            "length {length} must have a replay-checked packed witness; got {:?}",
            outcome.result
        );
    }
}
