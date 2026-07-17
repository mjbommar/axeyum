//! Differential tests of the pure Rust backend against oracle-free scenarios.
//!
//! Every scenario from [`axeyum_scenarios`] carries its own ground truth,
//! established by the evaluator (SAT witnesses) or by bounded-verified
//! identities (UNSAT) — never by a native oracle. Running the catalog through
//! [`SatBvBackend`] checks the whole lower-to-AIG-to-CNF-to-SAT path against a
//! trust signal that is independent in kind of the search path (ADR-0008).
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_scenarios::{Expectation, catalog};
use axeyum_solver::{CheckResult, SatBvBackend, SolverBackend, SolverConfig};

/// A generous per-scenario budget; the catalog is sized to decide well within
/// this, but the cap keeps a regression from hanging CI.
const TIMEOUT: Duration = Duration::from_secs(30);

#[test]
fn scenarios_self_check_and_agree_with_pure_rust_backend() {
    let config = SolverConfig {
        timeout: Some(TIMEOUT),
        ..SolverConfig::default()
    };

    let mut decided = 0usize;
    let mut unknown = 0usize;
    for scenario in catalog() {
        // The scenario must be internally consistent before we trust it as an
        // oracle for the backend.
        scenario.self_check().unwrap_or_else(|error| {
            panic!("scenario {} failed self-check: {error}", scenario.name)
        });

        let mut backend = SatBvBackend::new();
        let result = backend
            .check_query(&scenario.arena, &scenario.query, &config)
            .unwrap_or_else(|error| panic!("scenario {} errored: {error}", scenario.name));

        match (&scenario.expectation, &result) {
            (Expectation::Sat { .. }, CheckResult::Sat(model)) => {
                // The backend already replays, but cross-check the returned
                // model independently against the scenario's own query.
                let assignment = model.to_assignment();
                for term in scenario.query.solver_terms() {
                    assert_eq!(
                        axeyum_ir::eval(&scenario.arena, term, &assignment).unwrap(),
                        axeyum_ir::Value::Bool(true),
                        "backend model must satisfy {} term #{}",
                        scenario.name,
                        term.index()
                    );
                }
                decided += 1;
            }
            (Expectation::Unsat { .. }, CheckResult::Unsat) => decided += 1,
            (_, CheckResult::Unknown(reason)) => {
                // Unknown is a sound non-answer; record it but never let it pass
                // as a decision.
                unknown += 1;
                eprintln!("scenario {} returned unknown: {:?}", scenario.name, reason);
            }
            (Expectation::Sat { .. }, CheckResult::Unsat) => {
                panic!(
                    "SOUNDNESS: backend reported unsat for satisfiable {}",
                    scenario.name
                )
            }
            (Expectation::Unsat { .. }, CheckResult::Sat(_)) => {
                panic!(
                    "SOUNDNESS: backend reported sat for unsatisfiable {}",
                    scenario.name
                )
            }
        }
    }

    // The catalog is deliberately sized inside the supported subset, so the
    // pure-Rust backend should decide all of it without budget exhaustion.
    assert_eq!(unknown, 0, "every catalog scenario should be decided");
    assert!(decided > 0, "catalog must not be empty");
}
