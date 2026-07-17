//! End-to-end `QF_UFBV`: eager Ackermann elimination + pure-Rust BV solving
//! (ADR-0013).
//!
//! These tests close the EUF loop: a query over uninterpreted-function
//! applications is reduced to `QF_BV` by
//! [`axeyum_rewrite::eliminate_functions`], solved by [`SatBvBackend`], and its
//! model is projected back to function interpretations and **replayed against
//! the original query** with the ground evaluator — soundness checked without a
//! native oracle.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{CheckResult, SatBvBackend, SolverConfig, check_with_function_elimination};

/// Solves a `QF_UFBV` conjunction through the first-class entry point, which
/// internally eliminates functions, solves with the pure-Rust backend, and
/// replays the projected function model against the original query.
fn solve_qf_ufbv(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    let mut backend = SatBvBackend::new();
    check_with_function_elimination(&mut backend, arena, assertions, &SolverConfig::default())
        .expect("supported `QF_UFBV` query decides without error")
}

#[test]
fn congruence_makes_distinct_outputs_with_equal_inputs_unsat() {
    // x == y && f(x) != f(y) is unsatisfiable by congruence.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let same_in = arena.eq(x, y).unwrap();
    let same_out = arena.eq(fx, fy).unwrap();
    let diff_out = arena.not(same_out).unwrap();

    assert_eq!(
        solve_qf_ufbv(&mut arena, &[same_in, diff_out]),
        CheckResult::Unsat
    );
}

#[test]
fn distinct_outputs_force_distinct_inputs_sat_and_replays() {
    // f(x) != f(y) is satisfiable (it forces x != y); the projected model must
    // replay against the original query with the reconstructed f.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(4))
        .unwrap();
    let x = arena.bv_var("x", 4).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let same_out = arena.eq(fx, fy).unwrap();
    let diff_out = arena.not(same_out).unwrap();

    let CheckResult::Sat(model) = solve_qf_ufbv(&mut arena, &[diff_out]) else {
        panic!("expected a satisfiable disequality");
    };
    // The returned model carries the reconstructed interpretation of f, and the
    // original (application-using) query replays to true under it.
    assert!(model.function(f).is_some());
    let assignment = model.to_assignment();
    assert_eq!(
        eval(&arena, diff_out, &assignment).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn pinned_outputs_with_pinned_inputs_are_satisfiable() {
    // x == 3 && y == 5 && f(x) == 0xaa && f(y) == 0xbb is satisfiable
    // (3 != 5, so congruence imposes nothing).
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(8))
        .unwrap();
    let x = arena.bv_var("x", 4).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    let three = arena.bv_const(4, 3).unwrap();
    let five = arena.bv_const(4, 5).unwrap();
    let aa = arena.bv_const(8, 0xaa).unwrap();
    let bb = arena.bv_const(8, 0xbb).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let cx = arena.eq(x, three).unwrap();
    let cy = arena.eq(y, five).unwrap();
    let cfx = arena.eq(fx, aa).unwrap();
    let cfy = arena.eq(fy, bb).unwrap();

    let CheckResult::Sat(_) = solve_qf_ufbv(&mut arena, &[cx, cy, cfx, cfy]) else {
        panic!("expected satisfiable pinned function outputs");
    };
}

#[test]
fn pinned_distinct_outputs_with_equal_inputs_are_unsat() {
    // x == y && f(x) == 0xaa && f(y) == 0xbb is unsatisfiable: congruence forces
    // f(x) == f(y), contradicting 0xaa != 0xbb.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(8))
        .unwrap();
    let x = arena.bv_var("x", 4).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    let aa = arena.bv_const(8, 0xaa).unwrap();
    let bb = arena.bv_const(8, 0xbb).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let same_in = arena.eq(x, y).unwrap();
    let cfx = arena.eq(fx, aa).unwrap();
    let cfy = arena.eq(fy, bb).unwrap();

    assert_eq!(
        solve_qf_ufbv(&mut arena, &[same_in, cfx, cfy]),
        CheckResult::Unsat
    );
}

#[test]
fn binary_function_congruence_holds_end_to_end() {
    // f(a0, b0) != f(a1, b1) && a0 == a1 && b0 == b1 is unsatisfiable.
    let mut arena = TermArena::new();
    let func = arena
        .declare_fun("f", &[Sort::BitVec(4), Sort::BitVec(4)], Sort::BitVec(8))
        .unwrap();
    let a0 = arena.bv_var("a0", 4).unwrap();
    let b0 = arena.bv_var("b0", 4).unwrap();
    let a1 = arena.bv_var("a1", 4).unwrap();
    let b1 = arena.bv_var("b1", 4).unwrap();
    let lhs = arena.apply(func, &[a0, b0]).unwrap();
    let rhs = arena.apply(func, &[a1, b1]).unwrap();
    let diff = {
        let equal = arena.eq(lhs, rhs).unwrap();
        arena.not(equal).unwrap()
    };
    let same_a = arena.eq(a0, a1).unwrap();
    let same_b = arena.eq(b0, b1).unwrap();

    assert_eq!(
        solve_qf_ufbv(&mut arena, &[diff, same_a, same_b]),
        CheckResult::Unsat
    );
}
