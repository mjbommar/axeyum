//! Differential test of the `QF_ABV` path against the memory scenario catalog.
//!
//! Every memory scenario is satisfiable by construction (its load equals a
//! concretely-computed value). Running the catalog through
//! [`check_with_array_elimination`] checks the whole array pipeline — eager
//! elimination, BV solving, model projection, and original-query replay —
//! against oracle-free ground truth.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_scenarios::memory_catalog;
use axeyum_solver::{CheckResult, SatBvBackend, SolverConfig, check_with_array_elimination};

#[test]
fn memory_scenarios_decide_through_array_elimination() {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(30));
    let mut decided = 0usize;
    for mut scenario in memory_catalog() {
        scenario.self_check().unwrap_or_else(|error| {
            panic!(
                "memory scenario {} failed self-check: {error}",
                scenario.name
            )
        });

        let assertions = scenario.query.solver_terms().collect::<Vec<_>>();
        let mut backend = SatBvBackend::new();
        let result =
            check_with_array_elimination(&mut backend, &mut scenario.arena, &assertions, &config)
                .unwrap_or_else(|error| {
                    panic!("memory scenario {} errored: {error}", scenario.name)
                });
        match result {
            // Satisfiable by construction; the entry point already replays the
            // projected array model against the original query.
            CheckResult::Sat(_) => decided += 1,
            CheckResult::Unsat => {
                panic!(
                    "SOUNDNESS: memory scenario {} is satisfiable but got unsat",
                    scenario.name
                )
            }
            CheckResult::Unknown(reason) => {
                panic!(
                    "memory scenario {} returned unknown: {reason:?}",
                    scenario.name
                )
            }
        }
    }
    assert!(decided > 0, "memory catalog must not be empty");
}
