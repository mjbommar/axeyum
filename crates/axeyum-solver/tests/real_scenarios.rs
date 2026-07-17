//! Differential test of the `QF_LRA` path against the real scenario catalog.
//!
//! Every real scenario is satisfiable by construction (its rational witness
//! satisfies every constraint). Running the catalog through [`check_with_lra`]
//! checks the whole LRA pipeline — linear-atom extraction, Fourier–Motzkin
//! elimination, rational model reconstruction, and exact replay — against
//! oracle-free ground truth.
#![cfg(feature = "full")]

use axeyum_scenarios::real_catalog;
use axeyum_solver::{CheckResult, check_with_lra};

#[test]
fn real_scenarios_decide_through_fourier_motzkin() {
    let mut decided = 0usize;
    for scenario in real_catalog() {
        scenario.self_check().unwrap_or_else(|error| {
            panic!("real scenario {} failed self-check: {error}", scenario.name)
        });

        let assertions = scenario.query.solver_terms().collect::<Vec<_>>();
        let result = check_with_lra(&scenario.arena, &assertions)
            .unwrap_or_else(|error| panic!("real scenario {} errored: {error}", scenario.name));
        match result {
            // Satisfiable by construction; `check_with_lra` already replays the
            // rational model against the original query.
            CheckResult::Sat(_) => decided += 1,
            CheckResult::Unsat => {
                panic!(
                    "SOUNDNESS: real scenario {} is satisfiable but got unsat",
                    scenario.name
                )
            }
            CheckResult::Unknown(reason) => {
                panic!(
                    "real scenario {} returned unknown: {reason:?}",
                    scenario.name
                )
            }
        }
    }
    assert!(decided > 0, "real catalog must not be empty");
}
