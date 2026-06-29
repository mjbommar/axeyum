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

#[test]
fn graph_coloring_triangle_not_2_colorable_emits_checked_drat_and_lrat() {
    let formula = parse_dimacs(TRIANGLE_NOT_2_COLORABLE_CNF)
        .expect("graph-coloring-v0 triangle CNF artifact parses");
    assert_eq!(formula.variable_count(), 3);
    assert_eq!(formula.clauses().len(), 6);

    let ProofSolveOutcome::Unsat(drat) = solve_with_drat_proof(&formula) else {
        panic!("triangle-not-2-colorable CNF must be unsat");
    };
    assert_eq!(
        check_drat(&formula, &drat),
        Ok(true),
        "generated DRAT proof must independently check"
    );

    let lrat = elaborate_drat_to_lrat(&formula, &drat)
        .expect("resource DRAT proof elaborates to search-free LRAT");
    assert_eq!(
        check_lrat(&formula, &lrat),
        Ok(true),
        "elaborated LRAT proof must independently check"
    );

    let reparsed = parse_lrat(&write_lrat(&lrat)).expect("LRAT text round-trips");
    assert_eq!(check_lrat(&formula, &reparsed), Ok(true));
}
