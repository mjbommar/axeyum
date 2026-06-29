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
const RELATIONS_FUNCTIONS_SINGLE_VALUED_CONFLICT: &str = include_str!(
    "../../../artifacts/examples/math/relations-functions-v0/smt2/function-single-valued-conflict.smt2"
);
const FINITE_GROUPS_OPERATION_CONGRUENCE: &str = include_str!(
    "../../../artifacts/examples/math/finite-groups-v0/smt2/group-operation-congruence-conflict.smt2"
);

#[test]
fn equivalence_classes_quotient_map_congruence_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "equivalence-classes-v0 quotient-map congruence",
        EQUIVALENCE_CLASSES_QUOTIENT_CONGRUENCE,
    );
}

#[test]
fn relations_functions_single_valued_conflict_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "relations-functions-v0 function single-valued conflict",
        RELATIONS_FUNCTIONS_SINGLE_VALUED_CONFLICT,
    );
}

#[test]
fn finite_groups_operation_congruence_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-groups-v0 group operation congruence",
        FINITE_GROUPS_OPERATION_CONGRUENCE,
    );
}

fn assert_resource_euf_alethe(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: resource SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: resource obligation must be unsat"
    );

    let proof = prove_qf_uf_unsat_alethe(&script.arena, &assertions)
        .unwrap_or_else(|| panic!("{label}: resource obligation emits a pure EUF Alethe proof"));
    let evidence = Evidence::UnsatAletheProof(proof);
    assert!(evidence.is_certified());
    assert!(
        evidence.check(&script.arena, &assertions).unwrap(),
        "{label}: Alethe certificate must independently re-check"
    );
}
