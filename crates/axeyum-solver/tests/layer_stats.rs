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
    assert!(layers.clause_density() > 0.0, "density is positive");
    // total() is the sum of all stage durations and is well-defined.
    let _ = layers.total();
}

#[test]
fn empty_stats_are_not_misread_as_sat_bv() {
    // A SolveStats with no backend counters is not a sat-bv run.
    assert!(BvLayerStats::from_solve_stats(&SolveStats::default()).is_none());
}
