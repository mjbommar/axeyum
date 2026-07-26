//! Focused front-door coverage for the default 12-byte and selective 13-byte
//! packed SMT-LIB string windows.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::Sort;
use axeyum_smtlib::parse_script;
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

#[test]
fn direct_thirteen_byte_protocol_token_gets_a_replay_checked_witness() {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(2));
    let sat = r#"(set-logic QF_SLIA)
(declare-fun key () String)
(declare-fun unrelated () String)
(assert (= "cache-control" key))
(assert (= unrelated "ok"))
(check-sat)"#;
    let mut parsed = parse_script(sat).expect("parse adaptive 13-byte string query");
    let key = parsed.arena.find_symbol("key").expect("key symbol");
    let unrelated = parsed
        .arena
        .find_symbol("unrelated")
        .expect("unrelated symbol");
    let key_term = parsed.arena.var(key);
    let unrelated_term = parsed.arena.var(unrelated);
    assert_eq!(parsed.arena.sort_of(key_term), Sort::BitVec(108));
    assert_eq!(
        parsed.arena.sort_of(unrelated_term),
        Sort::BitVec(100),
        "an unrelated string must retain the cheaper 12-byte encoding"
    );
    assert!(matches!(
        solve_smtlib(sat, &config)
            .expect("adaptive 13-byte string query")
            .result,
        CheckResult::Sat(_)
    ));

    let contradiction = sat.replace(
        "(check-sat)",
        "(assert (not (= key \"cache-control\")))(check-sat)",
    );
    assert_eq!(
        solve_smtlib(&contradiction, &config)
            .expect("adaptive 13-byte contradiction")
            .result,
        CheckResult::Unsat
    );
}
