//! Wide decimal intake preserves verdict honesty and resource classification.
#![cfg(feature = "full")]
use axeyum_solver::{CheckResult, SolverConfig, UnknownKind, check_model, solve_smtlib_with_model};
use std::time::Duration;

#[test]
fn promoted_real_queries_never_panic_or_flip_verdicts() {
    let big = "340282366920938463463374607431768211454.0";
    let next = "340282366920938463463374607431768211455.0";
    for (constraints, feasible) in [
        (format!("(assert (= x {big}))"), true),
        (format!("(assert (= x {big}))(assert (= x {next}))"), false),
    ] {
        let source = format!("(set-logic QF_LRA)(declare-const x Real){constraints}(check-sat)");
        let solved = solve_smtlib_with_model(
            &source,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .unwrap();
        match solved.outcome.result {
            CheckResult::Sat(_) => {
                assert!(feasible);
                assert!(
                    check_model(
                        &solved.script.arena,
                        &solved.assertions,
                        solved.model.as_ref().unwrap()
                    )
                    .unwrap()
                );
            }
            CheckResult::Unsat => assert!(!feasible),
            CheckResult::Unknown(_) => (),
        }
    }
}

#[test]
fn excessive_decimal_intake_is_resource_unknown() {
    let source = format!(
        "(set-logic QF_LRA)(assert (= {}.0 0.0))(check-sat)",
        "9".repeat(4096)
    );
    let solved = solve_smtlib_with_model(&source, &SolverConfig::new()).unwrap();
    assert!(
        matches!(solved.outcome.result, CheckResult::Unknown(reason) if reason.kind == UnknownKind::ResourceLimit)
    );
    assert!(solved.model.is_none());
}
