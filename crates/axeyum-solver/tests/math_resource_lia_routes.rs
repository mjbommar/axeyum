//! Resource-backed `QF_LIA` proof-route regressions for math curriculum packs.
//!
//! These tests keep integer-obstruction educational resources tied to Axeyum's
//! small checked evidence: the solver may search over the integer system, but
//! accepted evidence must independently re-check against the original terms.

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, check_auto, produce_diophantine_evidence, produce_evidence,
};

const MODULAR_NONUNIT_DIOPHANTINE: &str = include_str!(
    "../../../artifacts/examples/math/modular-arithmetic-v0/smt2/nonunit-inverse-diophantine-conflict.smt2"
);
const EXACT_STATS_BAD_BINOMIAL_TAIL_COUNT: &str = include_str!(
    "../../../artifacts/examples/math/exact-statistical-tests-v0/smt2/bad-binomial-tail-count-diophantine-conflict.smt2"
);
const FINITE_SIMPLICIAL_BAD_BOUNDARY_COEFFICIENT: &str = include_str!(
    "../../../artifacts/examples/math/finite-simplicial-homology-v0/smt2/bad-boundary-coefficient-diophantine-conflict.smt2"
);
const INDUCTION_EVEN_PRODUCT_ODD: &str = include_str!(
    "../../../artifacts/examples/math/induction-patterns-v0/smt2/even-product-odd-diophantine-conflict.smt2"
);
const DESCRIPTIVE_STATS_BAD_CONTINGENCY_TOTAL: &str = include_str!(
    "../../../artifacts/examples/math/descriptive-statistics-v0/smt2/bad-contingency-total-diophantine-conflict.smt2"
);
const GRAPH_SEARCH_BAD_DFS_COST_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/graph-search-runtime-v0/smt2/bad-dfs-cost-bound-lia-conflict.smt2"
);

#[test]
fn modular_nonunit_inverse_emits_checked_diophantine_evidence() {
    assert_resource_diophantine(
        "modular-arithmetic-v0 nonunit inverse Diophantine obstruction",
        MODULAR_NONUNIT_DIOPHANTINE,
    );
}

#[test]
fn exact_stats_bad_binomial_tail_count_emits_checked_diophantine_evidence() {
    assert_resource_diophantine(
        "exact-statistical-tests-v0 bad binomial tail-count obstruction",
        EXACT_STATS_BAD_BINOMIAL_TAIL_COUNT,
    );
}

#[test]
fn finite_simplicial_bad_boundary_coefficient_emits_checked_diophantine_evidence() {
    assert_resource_diophantine(
        "finite-simplicial-homology-v0 bad boundary coefficient obstruction",
        FINITE_SIMPLICIAL_BAD_BOUNDARY_COEFFICIENT,
    );
}

#[test]
fn induction_even_product_odd_emits_checked_diophantine_evidence() {
    assert_resource_diophantine(
        "induction-patterns-v0 even product odd obstruction",
        INDUCTION_EVEN_PRODUCT_ODD,
    );
}

#[test]
fn descriptive_stats_bad_contingency_total_emits_checked_diophantine_evidence() {
    assert_resource_diophantine(
        "descriptive-statistics-v0 bad contingency total obstruction",
        DESCRIPTIVE_STATS_BAD_CONTINGENCY_TOTAL,
    );
}

#[test]
fn graph_search_bad_dfs_cost_bound_emits_checked_lia_dpll_evidence() {
    assert_resource_lia_dpll(
        "graph-search-runtime-v0 bad DFS cost-bound obstruction",
        GRAPH_SEARCH_BAD_DFS_COST_BOUND,
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

fn assert_resource_lia_dpll(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: resource SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: resource obligation must be unsat"
    );

    let report = produce_evidence(&mut script.arena, &assertions, &SolverConfig::default())
        .unwrap_or_else(|error| panic!("{label}: evidence production failed: {error}"));
    assert!(
        matches!(report.evidence, Evidence::UnsatArithDpll(_)),
        "{label}: expected certified arithmetic-DPLL evidence, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert!(
        report.evidence.check(&script.arena, &assertions).unwrap(),
        "{label}: arithmetic-DPLL refutation must independently re-check"
    );
}
