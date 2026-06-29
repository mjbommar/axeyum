//! Resource-backed `QF_BV` proof-route regressions for math curriculum packs.
//!
//! These tests keep fixed-width finite algebra resources tied to Axeyum's
//! clausal proof route: the pack-level finite replay explains the source
//! mathematical counterexample, and the upgraded `unsat` row must emit a
//! DIMACS/DRAT certificate that rechecks independently of solver search.

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, UnsatProofOutcome, check_auto, export_qf_bv_unsat_proof,
};

const FINITE_RINGS_BAD_DISTRIBUTIVITY: &str = include_str!(
    "../../../artifacts/examples/math/finite-rings-v0/smt2/non-distributive-table-bitblast-conflict.smt2"
);
const FINITE_FIELDS_COMPOSITE_NONFIELD: &str = include_str!(
    "../../../artifacts/examples/math/finite-fields-v0/smt2/composite-modulus-nonfield-bitblast-conflict.smt2"
);

#[test]
fn finite_rings_bad_distributivity_emits_checked_drat() {
    assert_resource_qf_bv_drat(
        "finite-rings-v0 bad distributivity bit-blast conflict",
        FINITE_RINGS_BAD_DISTRIBUTIVITY,
    );
}

#[test]
fn finite_fields_composite_nonfield_emits_checked_drat() {
    assert_resource_qf_bv_drat(
        "finite-fields-v0 composite modulus nonfield bit-blast conflict",
        FINITE_FIELDS_COMPOSITE_NONFIELD,
    );
}

fn assert_resource_qf_bv_drat(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: resource SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();
    assert!(
        !assertions.is_empty(),
        "{label}: artifact must contain assertions"
    );

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: resource obligation must be unsat"
    );

    let proof = match export_qf_bv_unsat_proof(&script.arena, &assertions) {
        Ok(UnsatProofOutcome::Proved(proof)) => proof,
        other => panic!("{label}: expected checked DRAT proof, got {other:?}"),
    };
    assert!(
        proof.dimacs.lines().any(|line| line.starts_with("p cnf ")),
        "{label}: proof must expose DIMACS CNF"
    );
    assert!(
        !proof.drat.trim().is_empty(),
        "{label}: proof must expose a non-empty DRAT refutation"
    );
    assert_eq!(
        proof.recheck(),
        Ok(true),
        "{label}: UnsatProof::recheck must accept the DIMACS/DRAT pair"
    );

    let evidence = Evidence::Unsat(Some(proof));
    assert!(evidence.is_certified(), "{label}: evidence is certified");
    assert!(
        evidence.check(&script.arena, &assertions).unwrap(),
        "{label}: Evidence::check must independently re-run the DRAT checker"
    );
}
