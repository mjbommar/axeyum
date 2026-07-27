//! Floating-point preprocessing regressions at the SMT-LIB front door.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

#[test]
fn float_no_simp3_decides_with_default_preprocessing() {
    let input = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../corpus/public-curated/non-incremental/QF_BVFP/bitwuzla-regress-clean/solver__fp__Float-no-simp3-main.smt2"
    ));
    let outcome = solve_smtlib(
        input,
        &SolverConfig::new().with_timeout(Duration::from_secs(2)),
    )
    .expect("public FP row solves");
    assert_eq!(outcome.expected_status.as_deref(), Some("unsat"));
    assert_eq!(outcome.result, CheckResult::Unsat);
}
