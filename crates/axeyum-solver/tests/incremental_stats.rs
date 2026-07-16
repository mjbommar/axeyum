//! Public incremental phase-attribution contract.

use axeyum_ir::TermArena;
use axeyum_solver::{
    AigConstructionStats, CheckResult, IncrementalBvSolver, IncrementalCnfStats,
    IncrementalLoweringStats, IncrementalModelLiftStats, SolverConfig,
};

fn assert_model_lift_attribution(
    work: IncrementalModelLiftStats,
    total: std::time::Duration,
    expected_aig_nodes: u64,
) {
    assert!(work.aig_recompute > std::time::Duration::ZERO);
    assert!(work.assignment_reconstruct > std::time::Duration::ZERO);
    assert!(work.model_completion > std::time::Duration::ZERO);
    assert_eq!(work.aig_nodes_recomputed, expected_aig_nodes);
    assert_eq!(work.symbol_bit_inputs_scanned, 64);
    assert_eq!(work.assignment_symbols_produced, 1);
    assert_eq!(work.arena_symbols_scanned, 1);
    assert_eq!(work.completed_model_values, 1);
    assert!(work.aig_recompute + work.assignment_reconstruct + work.model_completion <= total);
}

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
    assert_eq!(
        assertion_delta.aig_construction.and_requests,
        assertion_delta
            .aig_construction
            .and_trivial_simplifications
            .saturating_add(
                assertion_delta
                    .aig_construction
                    .and_absorption_simplifications
            )
            .saturating_add(assertion_delta.aig_construction.and_structural_hash_hits)
            .saturating_add(assertion_delta.aig_construction.and_nodes_created)
    );
    assert!(assertion_delta.aig_construction.and_nodes_created > 0);
    assert_eq!(
        assertion_delta.lowering_work.memoized_terms,
        assertion_delta.lowering_work.terms_lowered
    );
    assert_eq!(
        assertion_delta.lowering_work.term_bit_bindings,
        assertion_delta.lowering_work.term_bit_bindings_written
    );
    assert!(assertion_delta.lowering_work.operand_bits_copied > 0);
    assert!(assertion_delta.cnf_variables > 0);
    assert!(assertion_delta.cnf_clauses > 0);
    assert!(assertion_delta.cnf_gate_mix.and_nodes_synced > 0);
    assert_eq!(assertion_delta.cnf_gate_mix.definition_clauses, 0);
    assert_eq!(assertion_delta.cnf_gate_mix.root_clauses, 8);
    assert_eq!(assertion_delta.cnf_gate_mix.fused_positive_and_roots, 1);
    assert!(assertion_delta.cnf_gate_mix.fused_positive_and_nodes > 0);
    assert_eq!(
        assertion_delta.cnf_gate_mix.constant_clauses
            + assertion_delta.cnf_gate_mix.definition_clauses
            + assertion_delta.cnf_gate_mix.root_clauses,
        assertion_delta.cnf_clauses
    );
    assert_eq!(assertion_delta.word_rewrite, std::time::Duration::ZERO);

    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
    let checked = solver.stats();
    let check_delta = checked.delta_since(asserted);
    assert_eq!(check_delta.root_encodings, 0);
    assert_eq!(check_delta.checks, 1);
    assert_eq!(check_delta.aig_nodes, 0);
    assert_eq!(check_delta.cnf_variables, 0);
    assert_eq!(check_delta.cnf_clauses, 0);
    assert_model_lift_attribution(
        check_delta.model_lift_work,
        check_delta.model_lift,
        checked.aig_nodes,
    );
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
    assert_eq!(repeated.aig_construction, AigConstructionStats::default());
    assert_eq!(repeated.lowering_work, IncrementalLoweringStats::default());
    assert_eq!(repeated.cnf_gate_mix, IncrementalCnfStats::default());
    assert_eq!(
        repeated.model_lift_work.aig_nodes_recomputed,
        checked.aig_nodes
    );
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
fn solver_config_routes_internal_positive_and_flattening() {
    let mut arena = TermArena::new();
    let input_a = arena.bool_var("a").unwrap();
    let input_b = arena.bool_var("b").unwrap();
    let input_c = arena.bool_var("c").unwrap();
    let input_d = arena.bool_var("d").unwrap();
    let input_e = arena.bool_var("e").unwrap();
    let pair_ab = arena.and(input_a, input_b).unwrap();
    let pair_cd = arena.and(input_c, input_d).unwrap();
    let tree = arena.and(pair_ab, pair_cd).unwrap();
    let not_e = arena.not(input_e).unwrap();
    let assertion = arena.or(tree, not_e).unwrap();
    let config = SolverConfig::default()
        .with_preprocess(false)
        .with_incremental_positive_and_flattening(true);
    let mut solver = IncrementalBvSolver::with_config_and_profiling(config);

    solver.assert(&arena, assertion).unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
    let gate_mix = solver.stats().cnf_gate_mix;

    assert!(gate_mix.internal_positive_and_opportunities > 0);
    assert!(gate_mix.internal_positive_and_flattened > 0);
    assert!(gate_mix.internal_positive_and_immediate_clauses_avoided > 0);
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
    assert_eq!(stats.cnf_gate_mix, IncrementalCnfStats::default());
    assert_eq!(stats.lowering_work, IncrementalLoweringStats::default());
    assert_eq!(stats.model_lift_work, IncrementalModelLiftStats::default());
    assert!(stats.aig_construction.and_requests > 0);
    assert!(stats.aig_nodes > 0);
    assert!(stats.cnf_variables > 0);
    assert!(stats.cnf_clauses > 0);
}
