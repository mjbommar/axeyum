//! Controls for shared optimization intake and replay deadlines.
#![cfg(feature = "full")]
use axeyum_solver::smtlib::optimization::{OptimizationMode, optimize_with_models};
use axeyum_solver::smtlib::{optimize_smtlib, optimize_smtlib_lexicographic};
use axeyum_solver::{OptOutcome, SolverConfig, UnknownKind};
use std::time::Duration;

const QUERY: &str = "(set-logic QF_LIA)(declare-const x Int)(assert (and (>= x 0) (<= x 10)))(maximize x)(check-sat)";

#[test]
fn typed_intake_exhaustion_has_no_fabricated_objectives_or_gold() {
    let config = SolverConfig::new().with_timeout(Duration::ZERO);
    for mode in [OptimizationMode::Box, OptimizationMode::Lexicographic] {
        let report = optimize_with_models(QUERY, mode, &config).unwrap();
        assert!(report.objectives.is_empty());
        assert_eq!(
            report.intake_unknown.unwrap().kind,
            UnknownKind::ResourceLimit
        );
    }
}

#[test]
fn legacy_intake_exhaustion_is_unknown_not_unbounded_or_parse_error() {
    let config = SolverConfig::new().with_timeout(Duration::ZERO);
    for outcomes in [
        optimize_smtlib(QUERY, &config).unwrap(),
        optimize_smtlib_lexicographic(QUERY, &config).unwrap(),
    ] {
        assert_eq!(outcomes.len(), 1);
        assert!(
            matches!(&outcomes[0], OptOutcome::Unknown(reason) if reason.kind == UnknownKind::ResourceLimit)
        );
    }
}

#[test]
fn finite_optimization_remains_available_with_an_intake_budget() {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
    let report = optimize_with_models(QUERY, OptimizationMode::Lexicographic, &config).unwrap();
    assert!(report.intake_unknown.is_none());
    assert_eq!(report.objectives.len(), 1);
    assert!(matches!(
        report.objectives[0].outcome,
        OptOutcome::Optimal(10)
    ));
    assert_eq!(report.replay(0).unwrap(), Some(true));
    assert!(report.gold_eligible(0).unwrap());
}

#[test]
fn portable_replay_distinguishes_budget_exhaustion_from_rejection() {
    let report =
        optimize_with_models(QUERY, OptimizationMode::Lexicographic, &SolverConfig::new()).unwrap();
    let certificate = report.certificate(0).unwrap();
    let limited = certificate
        .check_within(QUERY, Some(std::time::Instant::now()))
        .unwrap();
    assert!(!limited.accepted && limited.resource_limited);
    assert_eq!((limited.examined, limited.discharged), (0, 0));
    let checked = certificate
        .check_within(
            QUERY,
            std::time::Instant::now().checked_add(Duration::from_secs(10)),
        )
        .unwrap();
    assert!(checked.accepted && !checked.resource_limited);
    assert_eq!((checked.examined, checked.discharged), (2, 2));
    let rejected = certificate.check("changed source").unwrap();
    assert!(!rejected.accepted && !rejected.resource_limited);
}
