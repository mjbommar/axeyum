//! Quantifies the incrementality win on the product-critical symbolic-execution
//! path: a warm [`IncrementalBvSolver`] that explores related path queries by
//! `push`/`check`/`pop` over a shared base constraint encodes far fewer total
//! CNF clauses than re-encoding each query from a cold solver, because shared
//! subterms bit-blast and Tseitin-encode exactly once.
//!
//! The measurement is on *encoded clause count* (deterministic), not wall-clock
//! (flaky in CI). Both engines must also agree on every per-branch verdict.
#![cfg(feature = "full")]
// Array tests name arrays/indices/elements with the conventional single letters
// (`a`, `b`, `c`, `d`, `i`, `j`, `k`, `m`, `v`); mirror the lint configuration
// the other `abv` suites use for the same reason.
#![allow(clippy::many_single_char_names, clippy::similar_names)]

use std::time::Duration;

use axeyum_ir::{TermArena, TermId};
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

// ---------------------------------------------------------------------------
// The array CEGAR (roadmap item 1.1).
// ---------------------------------------------------------------------------
//
// `check_qf_abv_lazy_row` refines by APPENDING read-over-write and
// select-congruence lemmas to one `working` set and re-solving. Warm means
// round n+1 reuses round n's lowering and CNF instead of re-blasting the whole
// abstraction; `RowCegarWarmth` is how the loop says which it did.
//
// The assertion that carries the weight here is NOT clause monotonicity. A
// fresh engine at round n+1 encodes the whole (larger) working set, so its
// clause count is also >= round n's -- monotonicity is true whether or not the
// loop is warm, and a check that cannot fail is worse than none. What fails on
// a rebuild is `encodes_each_assertion_once`: the warm engine is handed each
// working assertion exactly one time, so the running total equals the final
// working-set size, and a rebuild re-hands everything before it.

use axeyum_solver::{
    RowCegarWarmthGuard, SatBvBackend, check_qf_abv_lazy_row_warm, check_with_array_elimination,
    last_row_cegar_warmth,
};

/// A wide-index `QF_ABV` query the eager elimination refuses (array equality
/// over a 32-bit index) and the lazy-ROW CEGAR decides over several rounds: a
/// three-deep store chain read back at every write index and at two further
/// indices, with the read-back values pinned so the abstraction's first
/// candidates violate ROW.
fn wide_index_store_chain(arena: &mut TermArena) -> Vec<TermId> {
    let a = arena.array_var("a", 32, 8).unwrap();
    let b = arena.array_var("b", 32, 8).unwrap();
    let c = arena.array_var("c", 32, 8).unwrap();
    let d = arena.array_var("d", 32, 8).unwrap();
    let i = arena.bv_var("i", 32).unwrap();
    let j = arena.bv_var("j", 32).unwrap();
    let k = arena.bv_var("k", 32).unwrap();
    let m = arena.bv_var("m", 32).unwrap();
    let v1 = arena.bv_const(8, 0x11).unwrap();
    let v2 = arena.bv_const(8, 0x22).unwrap();
    let v3 = arena.bv_const(8, 0x33).unwrap();

    let sb = arena.store(a, i, v1).unwrap();
    let sc = arena.store(b, j, v2).unwrap();
    let sd = arena.store(c, k, v3).unwrap();
    let mut out = vec![
        arena.eq(b, sb).unwrap(),
        arena.eq(c, sc).unwrap(),
        arena.eq(d, sd).unwrap(),
    ];

    // Read the chain back at each write index and at a fourth, free index.
    for (name, index) in [("r1", i), ("r2", j), ("r3", k), ("r4", m)] {
        let read = arena.select(d, index).unwrap();
        let var = arena.bv_var(name, 8).unwrap();
        out.push(arena.eq(read, var).unwrap());
    }
    // Also read the base array, so read-over-read congruence has work to do.
    for (name, index) in [("s1", i), ("s2", j)] {
        let read = arena.select(a, index).unwrap();
        let var = arena.bv_var(name, 8).unwrap();
        out.push(arena.eq(read, var).unwrap());
    }
    // Force the write indices apart, so every ROW axiom must resolve through
    // the chain rather than collapsing to one hit.
    for (x, y) in [(i, j), (j, k), (i, k)] {
        let e = arena.eq(x, y).unwrap();
        out.push(arena.not(e).unwrap());
    }
    out
}

#[test]
fn array_cegar_reuses_the_previous_round_encoding() {
    let mut arena = TermArena::new();
    let originals = wide_index_store_chain(&mut arena);

    // Positive control on the PREMISE: this query really is one the eager
    // elimination refuses, so the lazy-ROW CEGAR is what decides it. Without
    // this, a query the eager path swallowed would make every assertion below
    // vacuous.
    {
        let mut probe = arena.clone();
        let mut backend = SatBvBackend::new();
        let eager = check_with_array_elimination(&mut backend, &mut probe, &originals, &config());
        assert!(
            eager.is_err(),
            "premise: the eager path must refuse this wide-index store-chain query, got {eager:?}"
        );
    }

    let mut backend = SatBvBackend::new();
    let guard = RowCegarWarmthGuard::enable();
    let result =
        check_qf_abv_lazy_row_warm(&mut backend, &mut arena, &originals, &config()).unwrap();
    let warmth = last_row_cegar_warmth();
    drop(guard);
    println!("{}", warmth.trace_line());

    assert!(
        is_sat(&result),
        "the store chain is satisfiable; got {result:?}"
    );
    // Replay the model against every original assertion: a warm engine that
    // leaked an encoding between rounds would show up here first.
    let CheckResult::Sat(model) = &result else {
        unreachable!("checked above")
    };
    let assignment = model.to_assignment();
    for &t in &originals {
        assert_eq!(
            axeyum_ir::eval(&arena, t, &assignment).unwrap(),
            axeyum_ir::Value::Bool(true),
            "the lazy-ROW sat model must replay on every original assertion"
        );
    }

    // The loop must actually have refined -- a one-round query would make the
    // reuse claim untestable.
    assert!(
        warmth.rounds >= 2,
        "need a multi-round refinement to test reuse at all, got {warmth:?}"
    );
    // One engine for the whole query, no round pushed back to the one-shot
    // backend.
    assert!(
        warmth.stayed_warm(),
        "the CEGAR loop must hold ONE warm engine across its rounds: {warmth:?}"
    );
    // THE falsifiable one: every working assertion encoded exactly once.
    assert!(
        warmth.encodes_each_assertion_once(),
        "round n+1 must reuse round n's encoding: the warm engine was handed \
         {} assertions for a final working set of {} -- {warmth:?}",
        warmth.warm_asserted_terms,
        warmth.working_terms_final
    );
    // The roadmap's stated criterion, kept as a necessary condition.
    assert!(
        warmth.clauses_monotone(),
        "retained clause count must be monotone across rounds: {:?}",
        warmth.clause_counts
    );
    assert!(
        warmth.lowering_monotone(),
        "retained lowering must be monotone across rounds: {:?}",
        warmth.aig_node_counts
    );
    assert_eq!(
        warmth.clause_counts.len(),
        warmth.rounds as usize,
        "one clause reading per round, or the record is not describing this loop"
    );
}

#[test]
fn array_cegar_warm_and_cold_agree() {
    // The warm route is a ROUTING change: it must not move a verdict. Same
    // query, both engines, same answer.
    let mut warm_arena = TermArena::new();
    let warm_originals = wide_index_store_chain(&mut warm_arena);
    let mut warm_backend = SatBvBackend::new();
    let warm = check_qf_abv_lazy_row_warm(
        &mut warm_backend,
        &mut warm_arena,
        &warm_originals,
        &config(),
    )
    .unwrap();

    let mut cold_arena = TermArena::new();
    let cold_originals = wide_index_store_chain(&mut cold_arena);
    let mut cold_backend = SatBvBackend::new();
    let cold = axeyum_solver::check_qf_abv_lazy_row(
        &mut cold_backend,
        &mut cold_arena,
        &cold_originals,
        &config(),
    )
    .unwrap();

    assert_eq!(
        is_sat(&warm),
        is_sat(&cold),
        "warm/cold verdict disagreement on the array CEGAR: warm={warm:?} cold={cold:?}"
    );
}

#[test]
fn array_cegar_unsat_still_transfers_warm() {
    // b = store(a, i, v) with select(b, i) != v: ROW refutes it. The warm route
    // must still carry the refutation -- an `unsat` here comes from the
    // relaxation, which the warm engine holds in full.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 32, 8).unwrap();
    let b = arena.array_var("b", 32, 8).unwrap();
    let i = arena.bv_var("i", 32).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let read = arena.select(b, i).unwrap();
    let eq = arena.eq(read, v).unwrap();
    let originals = [arena.eq(b, stored).unwrap(), arena.not(eq).unwrap()];

    let mut backend = SatBvBackend::new();
    let result =
        check_qf_abv_lazy_row_warm(&mut backend, &mut arena, &originals, &config()).unwrap();
    assert_eq!(
        result,
        CheckResult::Unsat,
        "the warm route must still refute a ROW-violating query"
    );
}
