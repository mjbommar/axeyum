//! Resource-backed `QF_LIA` proof-route regressions for math curriculum packs.
//!
//! These tests keep integer-obstruction educational resources tied to Axeyum's
//! small checked evidence: the solver may search over the integer system, but
//! the accepted evidence must re-check the Diophantine certificate against the
//! original equalities.

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, check_auto, produce_diophantine_evidence,
};

const MODULAR_NONUNIT_DIOPHANTINE: &str = include_str!(
    "../../../artifacts/examples/math/modular-arithmetic-v0/smt2/nonunit-inverse-diophantine-conflict.smt2"
);

#[test]
fn modular_nonunit_inverse_emits_checked_diophantine_evidence() {
    assert_resource_diophantine(
        "modular-arithmetic-v0 nonunit inverse Diophantine obstruction",
        MODULAR_NONUNIT_DIOPHANTINE,
    );
}

fn assert_resource_diophantine(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: resource SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: resource obligation must be unsat"
    );

    let report = produce_diophantine_evidence(&script.arena, &assertions)
        .unwrap_or_else(|error| panic!("{label}: Diophantine evidence production failed: {error}"))
        .unwrap_or_else(|| panic!("{label}: resource obligation emits Diophantine evidence"));
    assert!(
        matches!(report.evidence, Evidence::UnsatDiophantine { .. }),
        "{label}: expected UnsatDiophantine evidence, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert!(
        report.evidence.check(&script.arena, &assertions).unwrap(),
        "{label}: Diophantine certificate must independently re-check"
    );
}
