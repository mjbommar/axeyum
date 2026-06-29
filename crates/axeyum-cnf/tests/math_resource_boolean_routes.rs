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
