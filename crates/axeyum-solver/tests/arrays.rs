//! End-to-end `QF_ABV`: eager array elimination + pure-Rust BV solving
//! (ADR-0010).
//!
//! These tests close the array loop: a query over `select`/`store` is reduced
//! to `QF_BV` by [`axeyum_rewrite::eliminate_arrays`], solved by
//! [`SatBvBackend`],
//! and its model is projected back to array values and **replayed against the
//! original array query** with the ground evaluator — soundness checked without
//! a native oracle.

use axeyum_ir::TermArena;
use axeyum_solver::{CheckResult, SatBvBackend, SolverConfig, check_with_array_elimination};

/// Solves a `QF_ABV` conjunction through the first-class entry point, which
/// internally eliminates arrays, solves with the pure-Rust backend, and replays
/// the projected array model against the original query.
fn solve_qf_abv(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    let mut backend = SatBvBackend::new();
    check_with_array_elimination(&mut backend, arena, assertions, &SolverConfig::default())
        .expect("supported `QF_ABV` query decides without error")
}

#[test]
fn distinct_address_loads_are_satisfiable_and_replay() {
    // mem[i] == 0xa1 && mem[j] == 0xb2 && i != j.
    let mut arena = TermArena::new();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let load_i = arena.select(mem, i).unwrap();
    let load_j = arena.select(mem, j).unwrap();
    let a1 = arena.bv_const(8, 0xa1).unwrap();
    let b2 = arena.bv_const(8, 0xb2).unwrap();
    let c1 = arena.eq(load_i, a1).unwrap();
    let c2 = arena.eq(load_j, b2).unwrap();
    let distinct = arena.bv_ult(i, j).unwrap(); // forces i != j

    assert!(matches!(
        solve_qf_abv(&mut arena, &[c1, c2, distinct]),
        CheckResult::Sat(_)
    ));
}

#[test]
fn read_after_write_same_address_must_return_written_value() {
    // NOT( select(store(mem, i, v), i) == v ) is unsatisfiable.
    let mut arena = TermArena::new();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(mem, i, v).unwrap();
    let loaded = arena.select(stored, i).unwrap();
    let same = arena.eq(loaded, v).unwrap();
    let violated = arena.not(same).unwrap();

    assert_eq!(solve_qf_abv(&mut arena, &[violated]), CheckResult::Unsat);
}

#[test]
fn aliasing_write_then_distinct_load_is_satisfiable() {
    // After storing v at address i, a load at j may read either v (if i == j)
    // or the original memory (if i != j); requiring the load to equal a fixed
    // constant is satisfiable.
    let mut arena = TermArena::new();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(mem, i, v).unwrap();
    let loaded = arena.select(stored, j).unwrap();
    let target = arena.bv_const(8, 0x7e).unwrap();
    let goal = arena.eq(loaded, target).unwrap();

    let CheckResult::Sat(_) = solve_qf_abv(&mut arena, &[goal]) else {
        panic!("expected a satisfiable aliasing load");
    };
}
