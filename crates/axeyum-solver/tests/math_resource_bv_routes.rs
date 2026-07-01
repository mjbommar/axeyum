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
const FINITE_RINGS_BAD_MULTIPLICATIVE_IDENTITY: &str = include_str!(
    "../../../artifacts/examples/math/finite-rings-v0/smt2/bad-multiplicative-identity-bitblast-conflict.smt2"
);
const FINITE_FIELDS_COMPOSITE_NONFIELD: &str = include_str!(
    "../../../artifacts/examples/math/finite-fields-v0/smt2/composite-modulus-nonfield-bitblast-conflict.smt2"
);
const FINITE_FIELDS_BAD_INVERSE_CANDIDATE: &str = include_str!(
    "../../../artifacts/examples/math/finite-fields-v0/smt2/bad-inverse-candidate-bitblast-conflict.smt2"
);
const GRAPH_COLORING_TRIANGLE_NOT_2_COLORABLE: &str = include_str!(
    "../../../artifacts/examples/math/graph-coloring-v0/smt2/triangle-not-2-colorable-bitblast-conflict.smt2"
);
const NUMBER_THEORY_QUADRATIC_NONRESIDUE: &str = include_str!(
    "../../../artifacts/examples/math/number-theory-v0/smt2/quadratic-nonresidue-mod7-bitblast-conflict.smt2"
);
const NUMBER_THEORY_BAD_SQUARE_WITNESS: &str = include_str!(
    "../../../artifacts/examples/math/number-theory-v0/smt2/bad-square-witness-mod7-bitblast-conflict.smt2"
);
const FINITE_SIMPLICIAL_CUP_PRODUCT_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-simplicial-cup-products-v0/smt2/bad-cup-product-bitblast-conflict.smt2"
);

#[test]
fn finite_rings_bad_distributivity_emits_checked_drat() {
    assert_resource_qf_bv_drat(
        "finite-rings-v0 bad distributivity bit-blast conflict",
        FINITE_RINGS_BAD_DISTRIBUTIVITY,
    );
}

#[test]
fn finite_rings_bad_multiplicative_identity_emits_checked_drat() {
    assert_resource_qf_bv_drat(
        "finite-rings-v0 bad multiplicative identity bit-blast conflict",
        FINITE_RINGS_BAD_MULTIPLICATIVE_IDENTITY,
    );
}

#[test]
fn finite_fields_composite_nonfield_emits_checked_drat() {
    assert_resource_qf_bv_drat(
        "finite-fields-v0 composite modulus nonfield bit-blast conflict",
        FINITE_FIELDS_COMPOSITE_NONFIELD,
    );
}

#[test]
fn finite_fields_bad_inverse_candidate_emits_checked_drat() {
    assert_resource_qf_bv_drat(
        "finite-fields-v0 bad inverse candidate bit-blast conflict",
        FINITE_FIELDS_BAD_INVERSE_CANDIDATE,
    );
}

#[test]
fn graph_coloring_triangle_not_2_colorable_emits_checked_bv_drat() {
    assert_resource_qf_bv_drat(
        "graph-coloring-v0 triangle not 2-colorable bit-blast conflict",
        GRAPH_COLORING_TRIANGLE_NOT_2_COLORABLE,
    );
}

#[test]
fn number_theory_quadratic_nonresidue_emits_checked_bv_drat() {
    assert_resource_qf_bv_drat(
        "number-theory-v0 quadratic nonresidue mod 7 bit-blast conflict",
        NUMBER_THEORY_QUADRATIC_NONRESIDUE,
    );
}

#[test]
fn number_theory_bad_square_witness_emits_checked_bv_drat() {
    assert_resource_qf_bv_drat(
        "number-theory-v0 bad square witness mod 7 bit-blast conflict",
        NUMBER_THEORY_BAD_SQUARE_WITNESS,
    );
}

#[test]
fn finite_simplicial_cup_product_bad_value_emits_checked_bv_drat() {
    assert_resource_qf_bv_drat(
        "finite-simplicial-cup-products-v0 bad cup-product value",
        FINITE_SIMPLICIAL_CUP_PRODUCT_BAD_VALUE,
    );
}

#[test]
fn qf_bv_resource_route_rejects_tampered_drat_certificate() {
    let script = parse_script(FINITE_FIELDS_COMPOSITE_NONFIELD)
        .expect("finite-fields-v0 composite-modulus artifact parses");
    let assertions = script.assertions.clone();
    let proof = match export_qf_bv_unsat_proof(&script.arena, &assertions) {
        Ok(UnsatProofOutcome::Proved(proof)) => proof,
        other => panic!("expected checked DRAT proof, got {other:?}"),
    };
    assert_eq!(proof.recheck(), Ok(true));

    let mut tampered = proof.clone();
    tampered.drat = remove_last_nonempty_line(&tampered.drat);
    let evidence = Evidence::Unsat(Some(tampered));
    assert!(
        !matches!(evidence.check(&script.arena, &assertions), Ok(true)),
        "removing the final DRAT step must make QF_BV evidence reject"
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

fn remove_last_nonempty_line(text: &str) -> String {
    let mut lines: Vec<&str> = text.lines().collect();
    while matches!(lines.last(), Some(line) if line.trim().is_empty()) {
        lines.pop();
    }
    lines.pop();
    let mut out = lines.join("\n");
    if !out.is_empty() {
        out.push('\n');
    }
    out
}
