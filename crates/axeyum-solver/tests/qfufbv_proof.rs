//! End-to-end self-check of the `QF_UFBV` Ackermann certificate emitter
//! [`prove_qf_ufbv_unsat_alethe`] (Track 3, P3.5 — ADR-0013 task #19).
//!
//! Each test builds a genuinely-`unsat` `QF_UFBV` instance whose refutation goes
//! through the Ackermann reduction, emits the composed Alethe proof, and confirms
//! the in-tree [`axeyum_cnf::check_alethe`] re-accepts it and that it closes to the
//! empty clause `(cl)`. The certificate's distinguishing property is that each
//! functional-consistency constraint is **derived** by `eq_congruent` (over the
//! abstraction's defining equations) rather than assumed — there is no trusted
//! reduction step. Carcara cross-validation of the same proofs lives in
//! `carcara_crosscheck.rs`.

use axeyum_cnf::{AletheCommand, check_alethe};
use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::prove_qf_ufbv_unsat_alethe;

/// Declares a fresh `BitVec(width)` variable.
fn bv(arena: &mut TermArena, name: &str, width: u32) -> TermId {
    let s = arena.declare(name, Sort::BitVec(width)).expect("declare");
    arena.var(s)
}

/// Emits the certificate, asserts it self-checks and closes to `(cl)`.
fn self_checks(arena: &mut TermArena, assertions: &[TermId]) -> Vec<AletheCommand> {
    let proof = prove_qf_ufbv_unsat_alethe(arena, assertions)
        .expect("emitter produces the Ackermann certificate");
    assert_eq!(
        check_alethe(&proof),
        Ok(true),
        "emitted QF_UFBV certificate must independently re-check"
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
fn unary_congruence_with_bv_constant() {
    // f(a) = #b00 ∧ a = b ∧ ¬(f(b) = #b00).
    // unsat: a = b ⇒ f(a) = f(b) ⇒ f(b) = #b00, contradicting the disequality.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fb, c00).unwrap();
        arena.not(e).unwrap()
    };
    self_checks(&mut arena, &[e1, e2, e3]);
}

#[test]
#[allow(clippy::many_single_char_names)]
fn binary_congruence_two_argument_equalities() {
    // g(a, b) = #b00 ∧ a = c ∧ b = d ∧ ¬(g(c, d) = #b00).
    // unsat by two-argument congruence: a = c ∧ b = d ⇒ g(a, b) = g(c, d).
    let mut arena = TermArena::new();
    let g = arena
        .declare_fun("g", &[Sort::BitVec(2), Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let c = bv(&mut arena, "c", 2);
    let d = bv(&mut arena, "d", 2);
    let gab = arena.apply(g, &[a, b]).unwrap();
    let gcd = arena.apply(g, &[c, d]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(gab, c00).unwrap();
    let e2 = arena.eq(a, c).unwrap();
    let e3 = arena.eq(b, d).unwrap();
    let e4 = {
        let e = arena.eq(gcd, c00).unwrap();
        arena.not(e).unwrap()
    };
    self_checks(&mut arena, &[e1, e2, e3, e4]);
}

#[test]
#[allow(clippy::many_single_char_names)]
fn transitive_argument_equality_unary() {
    // f(a) = #b00 ∧ a = b ∧ b = c ∧ ¬(f(c) = #b00).
    // unsat: a = b = c (by transitivity) ⇒ f(a) = f(c) ⇒ f(c) = #b00, contradiction.
    // The argument equality a = c is NOT directly asserted — only derivable through
    // the chain a = b = c — so this exercises the eq_transitive arg-chain.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let c = bv(&mut arena, "c", 2);
    let fa = arena.apply(f, &[a]).unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = arena.eq(b, c).unwrap();
    let e4 = {
        let e = arena.eq(fc, c00).unwrap();
        arena.not(e).unwrap()
    };
    self_checks(&mut arena, &[e1, e2, e3, e4]);
}

#[test]
#[allow(clippy::many_single_char_names)]
fn transitive_argument_equality_binary_one_chained() {
    // g(a, b) = #b00 ∧ a = c ∧ b = d ∧ d = e ∧ ¬(g(c, e) = #b00).
    // unsat: a = c (direct) and b = d = e (chained) ⇒ g(a, b) = g(c, e). Mixes a
    // direct argument equality with a transitively-derived one in one congruence.
    let mut arena = TermArena::new();
    let g = arena
        .declare_fun("g", &[Sort::BitVec(2), Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let c = bv(&mut arena, "c", 2);
    let d = bv(&mut arena, "d", 2);
    let e = bv(&mut arena, "e", 2);
    let gab = arena.apply(g, &[a, b]).unwrap();
    let gce = arena.apply(g, &[c, e]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let a1 = arena.eq(gab, c00).unwrap();
    let a2 = arena.eq(a, c).unwrap();
    let a3 = arena.eq(b, d).unwrap();
    let a4 = arena.eq(d, e).unwrap();
    let a5 = {
        let eq = arena.eq(gce, c00).unwrap();
        arena.not(eq).unwrap()
    };
    self_checks(&mut arena, &[a1, a2, a3, a4, a5]);
}

#[test]
#[allow(clippy::many_single_char_names)]
fn congruence_derived_argument_equality() {
    // f(g(a)) = #b00 ∧ a = b ∧ ¬(f(g(b)) = #b00).
    // unsat: a = b ⇒ g(a) = g(b) (congruence over g) ⇒ f(g(a)) = f(g(b)) ⇒
    // f(g(b)) = #b00, contradiction. The two f-applications' arguments g(a) and
    // g(b) are equal NOT by a chain of asserted edges but by CONGRUENCE over g, so
    // the asserted-edge BFS declines and the e-graph congruence fallback derives
    // (= g(a) g(b)) via eq_congruent on a = b.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let g = arena
        .declare_fun("g", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let ga = arena.apply(g, &[a]).unwrap();
    let gb = arena.apply(g, &[b]).unwrap();
    let fga = arena.apply(f, &[ga]).unwrap();
    let fgb = arena.apply(f, &[gb]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fga, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fgb, c00).unwrap();
        arena.not(e).unwrap()
    };
    self_checks(&mut arena, &[e1, e2, e3]);
}

#[test]
fn no_functions_returns_none() {
    // Pure QF_BV (no applications): the dedicated QF_BV emitter handles it; the
    // QF_UFBV certificate emitter declines.
    let mut arena = TermArena::new();
    let x = bv(&mut arena, "x", 2);
    let c = arena.bv_const(2, 0).unwrap();
    let e = arena.eq(x, c).unwrap();
    assert!(prove_qf_ufbv_unsat_alethe(&mut arena, &[e]).is_none());
}

#[test]
fn unconnected_arguments_returns_none() {
    // f(a) = #b00 ∧ ¬(f(b) = #b00) with NO a = b: the consistency constraint's
    // antecedent is not entailed, so its consequent is not derivable — decline.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = {
        let e = arena.eq(fb, c00).unwrap();
        arena.not(e).unwrap()
    };
    assert!(prove_qf_ufbv_unsat_alethe(&mut arena, &[e1, e2]).is_none());
}
