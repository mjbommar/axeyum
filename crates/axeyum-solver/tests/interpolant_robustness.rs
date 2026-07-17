//! Cross-theory robustness gate for the interpolation engine (review-driven).
//!
//! `Solver::interpolant` feeds the *same* partition to every theory interpolator
//! in turn (LRA → EUF → UFLRA → BV), so each must **decline gracefully** on a
//! foreign-theory partition — never panic (the "graceful unknown, never crash"
//! hard rule). A latent panic here (one was found + fixed in `qf_bv_interpolant`,
//! which `unreachable!`d on real-sorted input) is a robustness bug. Every check
//! below simply *completes without panicking* and returns a `Result`/`Option`.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{
    InterpolantOutcome, SatBvBackend, Solver, lra_interpolant, qf_bv_interpolant,
    qf_uf_interpolant, uflra_interpolant,
};

fn bv_atoms(arena: &mut TermArena, name: &str) -> Vec<TermId> {
    let s = arena.declare(name, Sort::BitVec(8)).unwrap();
    let x = arena.var(s);
    let zero = arena.bv_const(8, 0).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let lo = arena.bv_ult(x, five).unwrap();
    let hi = arena.bv_ult(zero, x).unwrap();
    vec![lo, hi]
}

fn real_atoms(arena: &mut TermArena, name: &str) -> Vec<TermId> {
    let s = arena.declare(name, Sort::Real).unwrap();
    let x = arena.var(s);
    let zero = arena.real_ratio(0, 1);
    let le = arena.real_le(x, zero).unwrap();
    vec![le]
}

fn int_atoms(arena: &mut TermArena, name: &str) -> Vec<TermId> {
    let s = arena.declare(name, Sort::Int).unwrap();
    let x = arena.var(s);
    let zero = arena.int_const(0);
    let le = arena.int_le(x, zero).unwrap();
    vec![le]
}

fn uf_atoms(arena: &mut TermArena, name: &str) -> Vec<TermId> {
    let s = arena.declare(name, Sort::Int).unwrap();
    let x = arena.var(s);
    let f = arena
        .declare_fun(&format!("{name}_f"), &[Sort::Int], Sort::Int)
        .unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let e = arena.eq(fx, x).unwrap();
    vec![e]
}

/// Every free interpolant function, and the Solver dispatch, must return (not
/// panic) on each partition `(a, b)`.
fn assert_no_panic(arena: &mut TermArena, a: &[TermId], b: &[TermId]) {
    // Free functions — any Ok/Err/Some/None is fine; the point is no panic.
    let _ = lra_interpolant(arena, a, b);
    let _ = qf_uf_interpolant(arena, a, b);
    let _ = uflra_interpolant(arena, a, b);
    let _ = qf_bv_interpolant(arena, a, b);

    // The Solver dispatch over the same partition.
    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert_all(a);
    solver.assert_all(b);
    let a_indices: Vec<usize> = (0..a.len()).collect();
    let outcome = solver.interpolant_explained(arena, &a_indices);
    assert!(
        outcome.is_ok(),
        "interpolant_explained must return Ok (graceful), got {outcome:?}"
    );
    // Whatever it is, it is one of the three outcomes — never a panic.
    if let Ok(o) = outcome {
        assert!(matches!(
            o,
            InterpolantOutcome::Interpolant(_)
                | InterpolantOutcome::NotInterpolable
                | InterpolantOutcome::Declined
        ));
    }
}

#[test]
fn bv_vs_real_partitions_do_not_panic() {
    let mut arena = TermArena::new();
    let a = bv_atoms(&mut arena, "bx");
    let b = real_atoms(&mut arena, "ry");
    assert_no_panic(&mut arena, &a, &b);
    // And the reverse orientation.
    assert_no_panic(&mut arena, &b, &a);
}

#[test]
fn real_vs_int_partitions_do_not_panic() {
    let mut arena = TermArena::new();
    let a = real_atoms(&mut arena, "rx");
    let b = int_atoms(&mut arena, "iy");
    assert_no_panic(&mut arena, &a, &b);
    assert_no_panic(&mut arena, &b, &a);
}

#[test]
fn uf_vs_bv_partitions_do_not_panic() {
    let mut arena = TermArena::new();
    let a = uf_atoms(&mut arena, "ux");
    let b = bv_atoms(&mut arena, "by");
    assert_no_panic(&mut arena, &a, &b);
    assert_no_panic(&mut arena, &b, &a);
}

#[test]
fn mixed_theory_assertion_list_does_not_panic() {
    // A single partition whose assertions span BV + real + int + UF atoms — the
    // worst case for the dispatch (every theory sees foreign atoms).
    let mut arena = TermArena::new();
    let mut a = bv_atoms(&mut arena, "mbx");
    a.extend(real_atoms(&mut arena, "mrx"));
    let mut b = int_atoms(&mut arena, "miy");
    b.extend(uf_atoms(&mut arena, "muy"));
    assert_no_panic(&mut arena, &a, &b);
}

#[test]
fn empty_and_singleton_partitions_do_not_panic() {
    let mut arena = TermArena::new();
    let a = bv_atoms(&mut arena, "ebx");
    assert_no_panic(&mut arena, &a, &[]);
    assert_no_panic(&mut arena, &[], &a);
    assert_no_panic(&mut arena, &[], &[]);
}
