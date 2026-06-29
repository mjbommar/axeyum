//! Resource-backed `QF_UF` proof-route regressions for math curriculum packs.
//!
//! These tests keep equality-heavy educational resources tied to Axeyum's
//! zero-trust Alethe route: the solver may search with EUF, but the accepted
//! evidence must re-derive the congruence conflict without a trusted reduction
//! step.

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, Evidence, SolverConfig, check_auto, prove_qf_uf_unsat_alethe};

const EQUIVALENCE_CLASSES_QUOTIENT_CONGRUENCE: &str = include_str!(
    "../../../artifacts/examples/math/equivalence-classes-v0/smt2/quotient-map-congruence-conflict.smt2"
);

#[test]
fn equivalence_classes_quotient_map_congruence_emits_checked_alethe() {
    let mut script = parse_script(EQUIVALENCE_CLASSES_QUOTIENT_CONGRUENCE)
        .expect("resource SMT-LIB artifact parses");
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "resource obligation must be unsat"
    );

    let proof = prove_qf_uf_unsat_alethe(&script.arena, &assertions)
        .expect("resource obligation emits a pure EUF Alethe proof");
    let evidence = Evidence::UnsatAletheProof(proof);
    assert!(evidence.is_certified());
    assert!(
        evidence.check(&script.arena, &assertions).unwrap(),
        "Alethe certificate must independently re-check"
    );
}
