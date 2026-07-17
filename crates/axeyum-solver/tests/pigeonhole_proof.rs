//! The `proofs` curriculum node, made concrete: the **pigeonhole principle** is a
//! proof-complexity landmark (Haken 1985: no polynomial-size resolution proof),
//! and here axeyum decides `PHP(5,4)` UNSAT and emits an independently
//! **re-checked** certificate — "trusted small checking" on a famous theorem.
//! The satisfiable counterpart (`permutation_exists`) is decided `sat` with a
//! replay-checked model, exhibiting the SAT/UNSAT boundary.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::TermId;
use axeyum_scenarios::{permutation_exists, pigeonhole};
use axeyum_solver::{Evidence, SolverConfig, produce_evidence};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

#[test]
fn pigeonhole_5_into_4_has_a_rechecked_unsat_proof() {
    // PHP(5,4): 5 pigeons cannot occupy 4 holes without a collision.
    let mut scenario = pigeonhole(4);
    let assertions: Vec<TermId> = scenario.query.solver_terms().collect();
    let report = produce_evidence(&mut scenario.arena, &assertions, &config()).unwrap();
    assert!(
        !matches!(report.evidence, Evidence::Sat(_) | Evidence::Unknown(_)),
        "PHP(5,4) must be decided UNSAT"
    );
    // The certificate (DRAT/LRAT/Alethe/term-level) re-checks independently.
    assert!(
        report.evidence.check(&scenario.arena, &assertions).unwrap(),
        "the UNSAT proof must re-check"
    );
}

#[test]
fn permutation_of_4_is_sat_with_a_checked_model() {
    // 4 items into 4 holes, all distinct: a permutation exists.
    let mut scenario = permutation_exists(4);
    let assertions: Vec<TermId> = scenario.query.solver_terms().collect();
    let report = produce_evidence(&mut scenario.arena, &assertions, &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::Sat(_)),
        "a permutation of 4 should be SAT"
    );
    assert!(
        report.evidence.check(&scenario.arena, &assertions).unwrap(),
        "the SAT model must replay-check"
    );
}
