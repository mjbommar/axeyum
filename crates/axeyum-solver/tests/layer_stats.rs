//! Tests for the typed pipeline-stage view [`BvLayerStats`].

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{
    BvLayerStats, CheckResult, SatBvBackend, SolveStats, SolverBackend, SolverConfig,
};

#[test]
fn sat_bv_run_exposes_typed_layer_stats() {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let sum = arena.bv_add(x, y).unwrap();
    let target = arena.bv_const(8, 100).unwrap();
    let goal = arena.eq(sum, target).unwrap();

    let mut backend = SatBvBackend::new();
    let result = backend
        .check(&arena, &[goal], &SolverConfig::default())
        .unwrap();
    assert!(matches!(result, CheckResult::Sat(_)));

    let stats = backend.last_stats().expect("sat-bv records stats");
    let layers = BvLayerStats::from_solve_stats(stats).expect("sat-bv stats are typed-extractable");

    // The pipeline actually produced an AIG and a CNF.
    assert!(layers.aig_nodes > 0, "expected a non-empty AIG");
    assert!(
        layers.aig_inputs >= 16,
        "two 8-bit symbols give >= 16 inputs"
    );
    assert!(layers.cnf_variables > 0, "expected CNF variables");
    assert!(layers.cnf_clauses > 0, "expected CNF clauses");
    assert!(layers.aig_and_requests > 0, "AIG requests are counted");
    assert_eq!(
        layers.aig_and_requests,
        layers.aig_and_trivial_simplifications
            + layers.aig_and_absorption_simplifications
            + layers.aig_and_structural_hash_hits
            + layers.aig_and_nodes_created,
        "each primitive AND request has one outcome"
    );
    assert_eq!(
        layers.cnf_clause_attempts,
        layers.cnf_clauses
            + layers.cnf_tautological_clauses_skipped
            + layers.cnf_duplicate_clauses_skipped,
        "each clause attempt is emitted or skipped"
    );
    assert!(layers.cnf_reachable_nodes > 0);
    assert_eq!(layers.cnf_inprocess, std::time::Duration::ZERO);
    assert!(layers.clause_density() > 0.0, "density is positive");
    // total() is the sum of all stage durations and is well-defined.
    let _ = layers.total();
}

#[test]
fn empty_stats_are_not_misread_as_sat_bv() {
    // A SolveStats with no backend counters is not a sat-bv run.
    assert!(BvLayerStats::from_solve_stats(&SolveStats::default()).is_none());
}

#[test]
fn typed_layers_include_optional_cnf_inprocessing() {
    let mut stats = SolveStats::default();
    stats.solve = std::time::Duration::from_millis(5);
    stats.model_lift = std::time::Duration::from_millis(7);
    stats.backend = vec![
        ("aig_nodes".to_owned(), 10.0),
        ("cnf_variables".to_owned(), 12.0),
        ("bit_blast_ms".to_owned(), 1.0),
        ("cnf_encode_ms".to_owned(), 2.0),
        ("inprocess_ms".to_owned(), 3.0),
    ];
    let layers = BvLayerStats::from_solve_stats(&stats).unwrap();
    assert_eq!(layers.cnf_inprocess, std::time::Duration::from_millis(3));
    assert_eq!(layers.total(), std::time::Duration::from_millis(18));
}
