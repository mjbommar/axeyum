//! End-to-end self-check of the `QF_ABV` array-elimination certificate emitter
//! [`prove_qf_abv_unsat_alethe_via_elimination`] (Track 3, P3.5 — ADR-0010
//! task #20).
//!
//! Each test builds a genuinely-`unsat` `QF_ABV` instance whose refutation goes
//! through the array-elimination reduction (read-over-write + Ackermann-over-
//! select), emits the composed Alethe proof, and confirms the in-tree
//! [`axeyum_cnf::check_alethe`] re-accepts it and that it closes to the empty
//! clause `(cl)`. The certificate's distinguishing property is that each
//! **read-consistency** (Ackermann-over-select) constraint is **derived** by
//! `eq_congruent` over the per-array unary select function — there is no trusted
//! reduction step. Carcara cross-validation of the same proofs lives in
//! `carcara_crosscheck.rs`; reconstruction to a kernel-checked `False` lives in
//! the `reconstruct` unit tests.
#![cfg(feature = "full")]
#![allow(clippy::many_single_char_names)] // a, i, j, c, e: array, indices, const, expr

use axeyum_cnf::{AletheCommand, check_alethe};
use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::prove_qf_abv_unsat_alethe_via_elimination;

/// Declares a fresh `BitVec(width)` variable.
fn bv(arena: &mut TermArena, name: &str, width: u32) -> TermId {
    let s = arena.declare(name, Sort::BitVec(width)).expect("declare");
    arena.var(s)
}

/// Emits the certificate, asserts it self-checks and closes to `(cl)`.
fn self_checks(arena: &mut TermArena, assertions: &[TermId]) -> Vec<AletheCommand> {
    let proof = prove_qf_abv_unsat_alethe_via_elimination(arena, assertions)
        .expect("emitter produces the array-elimination certificate");
    assert_eq!(
        check_alethe(&proof),
        Ok(true),
        "emitted QF_ABV certificate must independently re-check"
    );
    match proof.last().expect("non-empty proof") {
        AletheCommand::Step { clause, .. } => {
            assert!(clause.is_empty(), "final step must derive the empty clause");
        }
        AletheCommand::Assume { .. } => panic!("final command must be a step"),
    }
    proof
}

#[test]
fn select_consistency_distinct_indices() {
    // select(a, i) = #b0…0 ∧ i = j ∧ ¬(select(a, j) = #b0…0).
    // unsat by read-consistency: i = j ⇒ select(a, i) = select(a, j).
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = bv(&mut arena, "i", 4);
    let j = bv(&mut arena, "j", 4);
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(sa, c).unwrap();
    let e2 = arena.eq(i, j).unwrap();
    let e3 = {
        let e = arena.eq(sb, c).unwrap();
        arena.not(e).unwrap()
    };
    self_checks(&mut arena, &[e1, e2, e3]);
}

#[test]
fn select_consistency_transitive_indices() {
    // select(a, i) = #b0…0 ∧ i = k ∧ k = j ∧ ¬(select(a, j) = #b0…0).
    // unsat by read-consistency where the index equality i = j holds only by
    // transitive closure i = k = j — exercises the eq_transitive index chain.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = bv(&mut arena, "i", 4);
    let k = bv(&mut arena, "k", 4);
    let j = bv(&mut arena, "j", 4);
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(sa, c).unwrap();
    let e2 = arena.eq(i, k).unwrap();
    let e3 = arena.eq(k, j).unwrap();
    let e4 = {
        let e = arena.eq(sb, c).unwrap();
        arena.not(e).unwrap()
    };
    self_checks(&mut arena, &[e1, e2, e3, e4]);
}

#[test]
fn select_consistency_symmetric_diseq() {
    // Same, but the disequality is written `¬(#b0…0 = select(a, j))`.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = bv(&mut arena, "i", 4);
    let j = bv(&mut arena, "j", 4);
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(c, sa).unwrap();
    let e2 = arena.eq(i, j).unwrap();
    let e3 = {
        let e = arena.eq(c, sb).unwrap();
        arena.not(e).unwrap()
    };
    self_checks(&mut arena, &[e1, e2, e3]);
}

#[test]
fn no_arrays_returns_none() {
    // Pure QF_BV (no arrays): the dedicated QF_BV emitter handles it; the
    // array-elimination certificate emitter declines.
    let mut arena = TermArena::new();
    let x = bv(&mut arena, "x", 4);
    let c = arena.bv_const(4, 0).unwrap();
    let e = arena.eq(x, c).unwrap();
    assert!(prove_qf_abv_unsat_alethe_via_elimination(&mut arena, &[e]).is_none());
}

#[test]
fn unconnected_indices_returns_none() {
    // select(a, i) = c ∧ ¬(select(a, j) = c) with NO i = j: the read-consistency
    // constraint's antecedent is not entailed, so its consequent is not derivable
    // — decline (the problem is in fact SAT).
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = bv(&mut arena, "i", 4);
    let j = bv(&mut arena, "j", 4);
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(sa, c).unwrap();
    let e2 = {
        let e = arena.eq(sb, c).unwrap();
        arena.not(e).unwrap()
    };
    assert!(prove_qf_abv_unsat_alethe_via_elimination(&mut arena, &[e1, e2]).is_none());
}

#[test]
fn single_select_returns_none() {
    // One select only: no select pair, hence no read-consistency constraint to
    // certify — decline.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = bv(&mut arena, "i", 4);
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let e = {
        let eq = arena.eq(sa, c).unwrap();
        arena.not(eq).unwrap()
    };
    assert!(prove_qf_abv_unsat_alethe_via_elimination(&mut arena, &[e]).is_none());
}
