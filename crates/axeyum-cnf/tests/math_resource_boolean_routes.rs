//! Resource-backed Boolean proof-route regressions for foundational math packs.
//!
//! These tests keep example-pack CNF artifacts connected to the in-tree proof
//! checkers: search may emit the proof, but DRAT/LRAT checking is the trusted
//! acceptance path.

use axeyum_cnf::{
    ProofSolveOutcome, check_drat, check_lrat, elaborate_drat_to_lrat, parse_dimacs, parse_lrat,
    solve_with_drat_proof, write_lrat,
};

const TRIANGLE_NOT_2_COLORABLE_CNF: &str = include_str!(
    "../../../artifacts/examples/math/graph-coloring-v0/cnf/triangle-not-2-colorable.cnf"
);
const CONTRADICTION_REFUTATION_CNF: &str = include_str!(
    "../../../artifacts/examples/math/proof-methods-patterns-v0/cnf/contradiction-refutation.cnf"
);
const FINITE_SETS_DISTRIBUTIVE_COUNTEREXAMPLE_CNF: &str = include_str!(
    "../../../artifacts/examples/math/finite-sets-v0/cnf/distributive-law-counterexample.cnf"
);
const LOGIC_BASICS_TINY_CNF_REFUTATION: &str =
    include_str!("../../../artifacts/examples/math/logic-basics-v0/cnf/tiny-cnf-refutation.cnf");
const FINITE_CARDINALITY_NO_INJECTION_FOUR_TO_THREE: &str = include_str!(
    "../../../artifacts/examples/math/finite-cardinality-v0/cnf/no-injection-four-to-three.cnf"
);
const GRAPH_CUT_ONE_EDGE_REJECTED: &str =
    include_str!("../../../artifacts/examples/math/graph-cut-v0/cnf/one-edge-cut-rejected.cnf");
const GRAPH_MATCHING_TRIANGLE_NO_PERFECT_MATCHING: &str = include_str!(
    "../../../artifacts/examples/math/graph-matching-v0/cnf/triangle-no-perfect-matching.cnf"
);
const GRAPH_REACHABILITY_DISCONNECTED_NO_PATH: &str = include_str!(
    "../../../artifacts/examples/math/graph-reachability-v0/cnf/disconnected-no-path.cnf"
);

fn assert_unsat_resource_cnf_checks(
    label: &str,
    dimacs: &str,
    expected_variables: usize,
    expected_clauses: usize,
) {
    let formula = parse_dimacs(dimacs).unwrap_or_else(|error| panic!("{label} parses: {error}"));
    assert_eq!(formula.variable_count(), expected_variables);
    assert_eq!(formula.clauses().len(), expected_clauses);

    let ProofSolveOutcome::Unsat(drat) = solve_with_drat_proof(&formula) else {
        panic!("{label} must be unsat");
    };
    assert_eq!(
        check_drat(&formula, &drat),
        Ok(true),
        "{label}: generated DRAT proof must independently check"
    );

    let lrat = elaborate_drat_to_lrat(&formula, &drat)
        .unwrap_or_else(|error| panic!("{label}: DRAT elaborates to LRAT: {error}"));
    assert_eq!(
        check_lrat(&formula, &lrat),
        Ok(true),
        "{label}: elaborated LRAT proof must independently check"
    );

    let reparsed = parse_lrat(&write_lrat(&lrat)).expect("LRAT text round-trips");
    assert_eq!(check_lrat(&formula, &reparsed), Ok(true));
}

#[test]
fn graph_coloring_triangle_not_2_colorable_emits_checked_drat_and_lrat() {
    assert_unsat_resource_cnf_checks(
        "graph-coloring-v0 triangle-not-2-colorable",
        TRIANGLE_NOT_2_COLORABLE_CNF,
        3,
        6,
    );
}

#[test]
fn proof_methods_contradiction_refutation_emits_checked_drat_and_lrat() {
    assert_unsat_resource_cnf_checks(
        "proof-methods-patterns-v0 contradiction-refutation",
        CONTRADICTION_REFUTATION_CNF,
        2,
        3,
    );
}

#[test]
fn finite_sets_distributive_counterexample_emits_checked_drat_and_lrat() {
    assert_unsat_resource_cnf_checks(
        "finite-sets-v0 distributive-law-counterexample",
        FINITE_SETS_DISTRIBUTIVE_COUNTEREXAMPLE_CNF,
        5,
        13,
    );
}

#[test]
fn logic_basics_tiny_cnf_refutation_emits_checked_drat_and_lrat() {
    assert_unsat_resource_cnf_checks(
        "logic-basics-v0 tiny-cnf-refutation",
        LOGIC_BASICS_TINY_CNF_REFUTATION,
        2,
        3,
    );
}

#[test]
fn finite_cardinality_no_injection_four_to_three_emits_checked_drat_and_lrat() {
    assert_unsat_resource_cnf_checks(
        "finite-cardinality-v0 no-injection-four-to-three",
        FINITE_CARDINALITY_NO_INJECTION_FOUR_TO_THREE,
        12,
        34,
    );
}

#[test]
fn graph_cut_one_edge_rejected_emits_checked_drat_and_lrat() {
    assert_unsat_resource_cnf_checks(
        "graph-cut-v0 one-edge-cut-rejected",
        GRAPH_CUT_ONE_EDGE_REJECTED,
        16,
        47,
    );
}

#[test]
fn graph_matching_triangle_no_perfect_matching_emits_checked_drat_and_lrat() {
    assert_unsat_resource_cnf_checks(
        "graph-matching-v0 triangle-no-perfect-matching",
        GRAPH_MATCHING_TRIANGLE_NO_PERFECT_MATCHING,
        3,
        6,
    );
}

#[test]
fn graph_reachability_disconnected_no_path_emits_checked_drat_and_lrat() {
    assert_unsat_resource_cnf_checks(
        "graph-reachability-v0 disconnected-no-path",
        GRAPH_REACHABILITY_DISCONNECTED_NO_PATH,
        16,
        41,
    );
}
