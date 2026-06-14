//! Quantifies the incrementality win on the product-critical symbolic-execution
//! path: a warm [`IncrementalBvSolver`] that explores related path queries by
//! `push`/`check`/`pop` over a shared base constraint encodes far fewer total
//! CNF clauses than re-encoding each query from a cold solver, because shared
//! subterms bit-blast and Tseitin-encode exactly once.
//!
//! The measurement is on *encoded clause count* (deterministic), not wall-clock
//! (flaky in CI). Both engines must also agree on every per-branch verdict.

use std::time::Duration;

use axeyum_ir::TermArena;
use axeyum_solver::{CheckResult, IncrementalBvSolver, SolverConfig};

const TIMEOUT: Duration = Duration::from_secs(30);

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(TIMEOUT)
}

fn is_sat(result: &CheckResult) -> bool {
    matches!(result, CheckResult::Sat(_))
}

#[test]
fn warm_incremental_reuse_beats_cold_reencoding() {
    let width = 12u32;
    let branch_count = 6u128;

    // Shared base: x * y == 0 — a large bit-blasted multiplier circuit that a
    // symbolic-execution frontend would carry across every path query.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", width).unwrap();
    let y = arena.bv_var("y", width).unwrap();
    let zero = arena.bv_const(width, 0).unwrap();
    let xy = arena.bv_mul(x, y).unwrap();
    let base = arena.eq(xy, zero).unwrap();

    // Distinct, cheap branch constraints: x == i. Each is satisfiable under the
    // base (pick y = 0 when x != 0).
    let branches = (0..branch_count)
        .map(|i| {
            let vi = arena.bv_const(width, i).unwrap();
            arena.eq(x, vi).unwrap()
        })
        .collect::<Vec<_>>();

    // Cold: a fresh solver per branch re-encodes the whole base each time.
    let mut cold_clauses = 0usize;
    let mut cold_results = Vec::new();
    for &branch in &branches {
        let mut solver = IncrementalBvSolver::with_config(config());
        solver.assert(&arena, base).unwrap();
        solver.assert(&arena, branch).unwrap();
        cold_results.push(solver.check(&arena).unwrap());
        cold_clauses += solver.encoded_clause_count();
    }

    // Warm: assert the base once, explore each branch in its own push/pop scope.
    let mut warm = IncrementalBvSolver::with_config(config());
    warm.assert(&arena, base).unwrap();
    let mut warm_results = Vec::new();
    for &branch in &branches {
        warm.push().unwrap();
        warm.assert(&arena, branch).unwrap();
        warm_results.push(warm.check(&arena).unwrap());
        warm.pop();
    }
    let warm_clauses = warm.encoded_clause_count();

    // Agreement: warm and cold must reach the same verdict on every branch
    // (all satisfiable here), or the incremental reuse changed semantics.
    for (i, (warm_r, cold_r)) in warm_results.iter().zip(&cold_results).enumerate() {
        assert!(is_sat(cold_r), "branch {i} should be sat (cold)");
        assert_eq!(
            is_sat(warm_r),
            is_sat(cold_r),
            "branch {i}: warm/cold verdict disagreement"
        );
    }

    println!(
        "warm_vs_cold: branches={branch_count} warm_clauses={warm_clauses} \
         cold_clauses={cold_clauses} (cold/warm = {}x scaled by 100)",
        cold_clauses * 100 / warm_clauses
    );

    // The shared multiplier circuit is encoded once warm versus once per branch
    // cold, so warm must encode dramatically fewer total clauses.
    assert!(
        warm_clauses * 2 < cold_clauses,
        "warm reuse should at least halve total encoded clauses: \
         warm={warm_clauses} cold={cold_clauses}"
    );
}
