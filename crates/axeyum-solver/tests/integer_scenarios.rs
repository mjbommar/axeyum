//! Differential test of the bounded `QF_LIA` path against the integer scenario
//! catalog.
//!
//! Every integer scenario is satisfiable by construction (its witness satisfies
//! every constraint, with small values inside the default bounded width).
//! Running the catalog through [`check_with_int_blasting`] checks the whole LIA
//! pipeline — bit-blasting, BV solving, integer model read-back, and
//! exact-integer replay — against oracle-free ground truth.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_scenarios::integer_catalog;
use axeyum_solver::{
    CheckResult, DEFAULT_INT_WIDTH, SatBvBackend, SolverConfig, check_with_int_blasting,
};

#[test]
fn integer_scenarios_decide_through_bit_blasting() {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(30));
    let mut decided = 0usize;
    for mut scenario in integer_catalog() {
        scenario.self_check().unwrap_or_else(|error| {
            panic!(
                "integer scenario {} failed self-check: {error}",
                scenario.name
            )
        });

        let assertions = scenario.query.solver_terms().collect::<Vec<_>>();
        let mut backend = SatBvBackend::new();
        let result = check_with_int_blasting(
            &mut backend,
            &mut scenario.arena,
            &assertions,
            DEFAULT_INT_WIDTH,
            &config,
        )
        .unwrap_or_else(|error| panic!("integer scenario {} errored: {error}", scenario.name));
        match result {
            // Satisfiable by construction; the entry point already replays the
            // integer model against the original query.
            CheckResult::Sat(_) => decided += 1,
            CheckResult::Unsat => {
                panic!(
                    "SOUNDNESS: integer scenario {} is satisfiable but got unsat",
                    scenario.name
                )
            }
            CheckResult::Unknown(reason) => {
                panic!(
                    "integer scenario {} returned unknown: {reason:?}",
                    scenario.name
                )
            }
        }
    }
    assert!(decided > 0, "integer catalog must not be empty");
}
