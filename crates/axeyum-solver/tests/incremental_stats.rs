//! Public incremental phase-attribution contract.

use axeyum_ir::TermArena;
use axeyum_solver::{CheckResult, IncrementalBvSolver, SolverConfig};

#[test]
fn incremental_stats_snapshot_and_delta_cover_the_client_pipeline() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 64).unwrap();
    let low = arena.extract(7, 0, x).unwrap();
    let expected = arena.bv_const(8, 0x5a).unwrap();
    let assertion = arena.eq(low, expected).unwrap();
    let mut solver = IncrementalBvSolver::with_config_and_profiling(
        SolverConfig::default().with_preprocess(false),
    );

    let empty = solver.stats();
    assert_eq!(empty.root_encodings, 0);
    assert_eq!(empty.checks, 0);
    assert_eq!(
        empty.aig_nodes,
        u64::try_from(solver.lowered_aig_node_count()).unwrap()
    );
    assert_eq!(empty.cnf_variables, 0);
    assert_eq!(empty.cnf_clauses, 0);

    solver.assert(&arena, assertion).unwrap();
    let asserted = solver.stats();
    let assertion_delta = asserted.delta_since(empty);
    assert_eq!(assertion_delta.root_encodings, 1);
    assert_eq!(assertion_delta.checks, 0);
    assert!(assertion_delta.aig_nodes > 0);
    assert!(assertion_delta.cnf_variables > 0);
    assert!(assertion_delta.cnf_clauses > 0);
    assert_eq!(assertion_delta.word_rewrite, std::time::Duration::ZERO);

    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
    let checked = solver.stats();
    let check_delta = checked.delta_since(asserted);
    assert_eq!(check_delta.root_encodings, 0);
    assert_eq!(check_delta.checks, 1);
    assert_eq!(check_delta.aig_nodes, 0);
    assert_eq!(check_delta.cnf_variables, 0);
    assert_eq!(check_delta.cnf_clauses, 0);
    assert_eq!(
        checked.aig_nodes,
        u64::try_from(solver.lowered_aig_node_count()).unwrap()
    );
    assert_eq!(
        checked.cnf_variables,
        u64::try_from(solver.encoded_variable_count()).unwrap()
    );
    assert_eq!(
        checked.cnf_clauses,
        u64::try_from(solver.encoded_clause_count()).unwrap()
    );

    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
    let repeated = solver.stats().delta_since(checked);
    assert_eq!(repeated.checks, 1);
    assert_eq!(repeated.root_encodings, 0);
    assert_eq!(repeated.aig_nodes, 0);
    assert_eq!(repeated.cnf_variables, 0);
    assert_eq!(repeated.cnf_clauses, 0);
}

#[test]
fn configured_batch_attributes_word_rewrite_once_and_preserves_replay() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 64).unwrap();
    let one = arena.bv_const(64, 1).unwrap();
    let five = arena.bv_const(64, 5).unwrap();
    let seven = arena.bv_const(64, 7).unwrap();
    let sum = arena.bv_add(x, one).unwrap();
    let assertions = [arena.eq(sum, five).unwrap(), arena.eq(sum, seven).unwrap()];
    let mut solver = IncrementalBvSolver::with_config_and_profiling(SolverConfig::default());

    let before = solver.stats();
    solver
        .assert_configured_batch(&mut arena, &assertions)
        .unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
    let delta = solver.stats().delta_since(before);

    assert_eq!(
        delta.root_encodings,
        u64::try_from(assertions.len()).unwrap()
    );
    assert_eq!(delta.checks, 1);
    assert!(delta.aig_nodes > 0);
    assert!(delta.cnf_variables > 0);
    assert!(delta.cnf_clauses > 0);
}

#[test]
fn ordinary_constructor_keeps_phase_profiling_disabled() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let value = arena.bv_const(8, 7).unwrap();
    let assertion = arena.eq(x, value).unwrap();
    let mut solver = IncrementalBvSolver::new();

    solver.assert(&arena, assertion).unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
    let stats = solver.stats();

    assert_eq!(stats.root_encodings, 0);
    assert_eq!(stats.checks, 0);
    assert_eq!(stats.total_time(), std::time::Duration::ZERO);
    assert!(stats.aig_nodes > 0);
    assert!(stats.cnf_variables > 0);
    assert!(stats.cnf_clauses > 0);
}
