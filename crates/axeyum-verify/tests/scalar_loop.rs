//! C4.1 — the generic `ScalarLoopSystem` over N scalar variables. It (a) subsumes
//! the hand-written `CounterLoopSystem` (same verdict on the same loop), and (b)
//! handles a genuine multi-variable accumulator loop — all via the warm
//! `bounded_model_check` route (not unrolling into one-shot queries).

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{SolverConfig, SolverError};
use axeyum_verify::Ty;
use axeyum_verify::bmc::{CounterLoopSystem, LoopSafety, ScalarLoopSystem, check_loop, run_loop};

const W: u32 = 8;

fn names(xs: &[&str]) -> Vec<String> {
    xs.iter().map(|s| (*s).to_string()).collect()
}

/// A generic system replicating `while i < limit { i += 1 }` with bad state
/// `i == bad`, over state vars `[i, limit]`.
fn counter_like(bad: u128) -> ScalarLoopSystem {
    ScalarLoopSystem::new(
        W,
        names(&["i", "limit"]),
        // init: i == 0 (limit is a free symbolic input).
        Box::new(
            |arena: &mut TermArena, v: &[TermId]| -> Result<TermId, SolverError> {
                let zero = arena.bv_const(W, 0)?;
                Ok(arena.eq(v[0], zero)?)
            },
        ),
        // guard: i < limit.
        Box::new(|arena, v| Ok(arena.bv_ult(v[0], v[1])?)),
        // update: i' = i + 1, limit' = limit.
        Box::new(|arena, v| {
            let one = arena.bv_const(W, 1)?;
            Ok(vec![arena.bv_add(v[0], one)?, v[1]])
        }),
        // bad: i == bad.
        Box::new(move |arena, v| {
            let b = arena.bv_const(W, bad)?;
            Ok(arena.eq(v[0], b)?)
        }),
    )
}

#[test]
fn generic_subsumes_counter_loop() {
    let cfg = SolverConfig::default();
    let bad = 3;
    let specific = CounterLoopSystem::new(
        Ty::Int {
            width: 8,
            signed: false,
        },
        bad,
    )
    .expect("u8 counter loop");
    let generic = counter_like(bad);

    let s = check_loop(&specific, 10, &cfg).expect("specific");
    let g = run_loop(&generic, 10, &cfg).expect("generic");

    match (s, g) {
        (
            LoopSafety::BugReachable { steps: s1, .. },
            LoopSafety::BugReachable { steps: s2, .. },
        ) => {
            assert_eq!(
                s1, s2,
                "generic and hand-written counter loop must agree on depth"
            );
        }
        other => panic!("expected both BugReachable, got {other:?}"),
    }
}

#[test]
fn multi_variable_accumulator_loop_finds_bug() {
    // while i < limit { sum += i; i += 1 }  with bad state i == 5 — three state
    // variables [i, sum, limit]; the bad counter value is reachable.
    let cfg = SolverConfig::default();
    let system = ScalarLoopSystem::new(
        W,
        names(&["i", "sum", "limit"]),
        Box::new(
            |arena: &mut TermArena, v: &[TermId]| -> Result<TermId, SolverError> {
                let zero = arena.bv_const(W, 0)?;
                let i0 = arena.eq(v[0], zero)?;
                let sum0 = arena.eq(v[1], zero)?;
                Ok(arena.and(i0, sum0)?)
            },
        ),
        Box::new(|arena, v| Ok(arena.bv_ult(v[0], v[2])?)),
        Box::new(|arena, v| {
            let one = arena.bv_const(W, 1)?;
            // sum' = sum + i, i' = i + 1, limit' = limit
            Ok(vec![
                arena.bv_add(v[0], one)?,
                arena.bv_add(v[1], v[0])?,
                v[2],
            ])
        }),
        Box::new(|arena, v| {
            let five = arena.bv_const(W, 5)?;
            Ok(arena.eq(v[0], five)?)
        }),
    );
    match run_loop(&system, 10, &cfg).expect("multi-var") {
        LoopSafety::BugReachable { steps, .. } => assert_eq!(steps, 5, "i reaches 5 in 5 steps"),
        other => panic!("expected BugReachable, got {other:?}"),
    }
}

#[test]
fn accumulator_safe_within_bound() {
    // Same loop but bad state i == 200: unreachable within a 10-iteration bound.
    let cfg = SolverConfig::default();
    let system = ScalarLoopSystem::new(
        W,
        names(&["i", "sum", "limit"]),
        Box::new(
            |arena: &mut TermArena, v: &[TermId]| -> Result<TermId, SolverError> {
                let zero = arena.bv_const(W, 0)?;
                let i0 = arena.eq(v[0], zero)?;
                let sum0 = arena.eq(v[1], zero)?;
                Ok(arena.and(i0, sum0)?)
            },
        ),
        Box::new(|arena, v| Ok(arena.bv_ult(v[0], v[2])?)),
        Box::new(|arena, v| {
            let one = arena.bv_const(W, 1)?;
            Ok(vec![
                arena.bv_add(v[0], one)?,
                arena.bv_add(v[1], v[0])?,
                v[2],
            ])
        }),
        Box::new(|arena, v| {
            let big = arena.bv_const(W, 200)?;
            Ok(arena.eq(v[0], big)?)
        }),
    );
    match run_loop(&system, 10, &cfg).expect("safe") {
        LoopSafety::SafeWithinBound { bound } => assert_eq!(bound, 10),
        other => panic!("expected SafeWithinBound, got {other:?}"),
    }
}

#[test]
fn conditional_update_in_loop_body_folds_to_ite() {
    // while i < limit { if (i & 1 == 0) { evens += 1 } i += 1 }  with bad i == 4.
    // The in-loop `if` folds into evens' = ite(i even, evens+1, evens) — C4.2: the
    // ScalarLoopSystem update closure expresses guarded body assignments directly.
    let cfg = SolverConfig::default();
    let system = ScalarLoopSystem::new(
        W,
        names(&["i", "evens", "limit"]),
        Box::new(
            |arena: &mut TermArena, v: &[TermId]| -> Result<TermId, SolverError> {
                let zero = arena.bv_const(W, 0)?;
                let i0 = arena.eq(v[0], zero)?;
                let e0 = arena.eq(v[1], zero)?;
                Ok(arena.and(i0, e0)?)
            },
        ),
        Box::new(|arena, v| Ok(arena.bv_ult(v[0], v[2])?)),
        Box::new(|arena, v| {
            let one = arena.bv_const(W, 1)?;
            // i even  <=>  (i & 1) == 0
            let lsb = arena.bv_and(v[0], one)?;
            let zero = arena.bv_const(W, 0)?;
            let is_even = arena.eq(lsb, zero)?;
            let evens_inc = arena.bv_add(v[1], one)?;
            let evens_next = arena.ite(is_even, evens_inc, v[1])?;
            Ok(vec![arena.bv_add(v[0], one)?, evens_next, v[2]])
        }),
        Box::new(|arena, v| {
            let four = arena.bv_const(W, 4)?;
            Ok(arena.eq(v[0], four)?)
        }),
    );
    match run_loop(&system, 10, &cfg).expect("conditional-update") {
        LoopSafety::BugReachable { steps, .. } => assert_eq!(steps, 4, "i reaches 4 in 4 steps"),
        other => panic!("expected BugReachable, got {other:?}"),
    }
}
