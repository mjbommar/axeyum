//! Warm word-level preprocessing for lifter-shaped `QF_BV` formulas.

use axeyum_ir::TermArena;
use axeyum_solver::{CheckResult, IncrementalBvSolver, SolverConfig};

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
