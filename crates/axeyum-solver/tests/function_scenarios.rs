//! Differential test of the `QF_UFBV` path against the function scenario
//! catalog.
//!
//! Every function scenario is satisfiable by construction (each application
//! equals its concrete table value). Running the catalog through
//! [`check_with_function_elimination`] checks the whole EUF pipeline — Ackermann
//! elimination, BV solving, model projection, and original-query replay —
//! against oracle-free ground truth.

use std::time::Duration;

use axeyum_scenarios::function_catalog;
use axeyum_solver::{CheckResult, SatBvBackend, SolverConfig, check_with_function_elimination};

#[test]
fn function_scenarios_decide_through_function_elimination() {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(30));
    let mut decided = 0usize;
    for mut scenario in function_catalog() {
        scenario.self_check().unwrap_or_else(|error| {
            panic!(
                "function scenario {} failed self-check: {error}",
                scenario.name
            )
        });

        let assertions = scenario.query.solver_terms().collect::<Vec<_>>();
        let mut backend = SatBvBackend::new();
        let result = check_with_function_elimination(
            &mut backend,
            &mut scenario.arena,
            &assertions,
            &config,
        )
        .unwrap_or_else(|error| panic!("function scenario {} errored: {error}", scenario.name));
        match result {
            // Satisfiable by construction; the entry point already replays the
            // projected function model against the original query.
            CheckResult::Sat(_) => decided += 1,
            CheckResult::Unsat => {
                panic!(
                    "SOUNDNESS: function scenario {} is satisfiable but got unsat",
                    scenario.name
                )
            }
            CheckResult::Unknown(reason) => {
                panic!(
                    "function scenario {} returned unknown: {reason:?}",
                    scenario.name
                )
            }
        }
    }
    assert!(decided > 0, "function catalog must not be empty");
}
