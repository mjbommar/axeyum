//! Warm word-level preprocessing for lifter-shaped `QF_BV` formulas.

use axeyum_ir::TermArena;
use axeyum_rewrite::canonicalize_terms;
use axeyum_solver::{CheckResult, IncrementalBvSolver, SolverConfig, SolverError};

fn sliced_wide_bitwise_assertion(arena: &mut TermArena) -> axeyum_ir::TermId {
    let x = arena.bv_var("x", 64).unwrap();
    let y = arena.bv_var("y", 64).unwrap();
    let wide = arena.bv_and(x, y).unwrap();
    let byte = arena.extract(7, 0, wide).unwrap();
    let expected = arena.bv_const(8, 0x5a).unwrap();
    arena.eq(byte, expected).unwrap()
}

#[test]
fn warm_preprocessing_avoids_discarded_wide_bitwise_gates() {
    let mut raw_arena = TermArena::new();
    let raw_assertion = sliced_wide_bitwise_assertion(&mut raw_arena);
    let mut raw = IncrementalBvSolver::with_config(SolverConfig::default().with_preprocess(false));
    let lowered = raw
        .assert_configured(&mut raw_arena, raw_assertion)
        .unwrap();
    assert_eq!(lowered, raw_assertion);
    let raw_aig_nodes = raw.lowered_aig_node_count();
    assert!(matches!(
        raw.check(&raw_arena).unwrap(),
        CheckResult::Sat(_)
    ));

    let mut optimized_arena = TermArena::new();
    let optimized_assertion = sliced_wide_bitwise_assertion(&mut optimized_arena);
    let mut optimized = IncrementalBvSolver::new();
    let lowered = optimized
        .assert_configured(&mut optimized_arena, optimized_assertion)
        .unwrap();
    assert_ne!(lowered, optimized_assertion);
    let optimized_aig_nodes = optimized.lowered_aig_node_count();
    assert!(matches!(
        optimized.check(&optimized_arena).unwrap(),
        CheckResult::Sat(_)
    ));

    assert!(
        optimized_aig_nodes + 40 < raw_aig_nodes,
        "narrowing before bit-blast should remove most discarded gates: raw={raw_aig_nodes}, optimized={optimized_aig_nodes}",
    );
}

#[test]
fn cold_batch_preprocessing_matches_shared_multi_root_canonicalization() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 64).unwrap();
    let one = arena.bv_const(64, 1).unwrap();
    let five = arena.bv_const(64, 5).unwrap();
    let seven = arena.bv_const(64, 7).unwrap();
    let x_plus_one = arena.bv_add(x, one).unwrap();
    let assertions = [
        arena.eq(x_plus_one, five).unwrap(),
        arena.eq(x_plus_one, seven).unwrap(),
    ];
    let expected = canonicalize_terms(&mut arena, &assertions).unwrap().terms;

    let mut solver = IncrementalBvSolver::new();
    let lowered = solver
        .assert_preprocessed_batch(&mut arena, &assertions)
        .unwrap();

    assert_eq!(lowered, expected);
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
}

#[test]
fn configured_batch_can_preserve_raw_roots() {
    let mut arena = TermArena::new();
    let assertion = sliced_wide_bitwise_assertion(&mut arena);
    let mut solver =
        IncrementalBvSolver::with_config(SolverConfig::default().with_preprocess(false));

    let lowered = solver
        .assert_configured_batch(&mut arena, &[assertion])
        .unwrap();

    assert_eq!(lowered, vec![assertion]);
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));
}

#[test]
fn batch_rejects_non_boolean_input_before_asserting_any_root() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let true_term = arena.bool_const(true);
    let mut solver = IncrementalBvSolver::new();

    assert!(
        solver
            .assert_preprocessed_batch(&mut arena, &[])
            .unwrap()
            .is_empty()
    );
    assert!(matches!(
        solver.assert_preprocessed_batch(&mut arena, &[true_term, x]),
        Err(SolverError::NonBooleanAssertion(term)) if term == x
    ));
    assert_eq!(solver.encoded_clause_count(), 0);
}
