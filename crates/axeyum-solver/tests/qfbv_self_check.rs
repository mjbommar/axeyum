//! Internal self-check of axeyum's own full `QF_BV` Alethe proofs.
//!
//! The driver [`prove_qf_bv_unsat_alethe`] emits a complete refutation closing to
//! the empty clause `(cl)`. With the `bitblast_<op>` reconstruction rules and the
//! `and` clausification rule ported into the in-tree checker
//! [`axeyum_cnf::check_alethe`], that checker now accepts the **full** driver
//! output with no external Carcara needed: axeyum self-checks its own `QF_BV`
//! proofs. Each test below builds a genuinely-`unsat` instance (the same shapes the
//! Carcara cross-check exercises), emits the proof, and asserts our own checker
//! returns `Ok(true)` — UNSAT established by a verified empty-clause derivation.
#![cfg(feature = "full")]

use axeyum_cnf::check_alethe;
use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::prove_qf_bv_unsat_alethe;

fn bv(arena: &mut TermArena, name: &str, width: u32) -> TermId {
    let s = arena.declare(name, Sort::BitVec(width)).expect("declare");
    arena.var(s)
}

/// Emits the driver proof for `assertions` and asserts our in-tree checker accepts
/// the FULL proof (derives the empty clause → `Ok(true)`).
fn self_checks(arena: &TermArena, assertions: &[TermId]) {
    let proof = prove_qf_bv_unsat_alethe(arena, assertions).expect("driver emits an unsat proof");
    assert_eq!(
        check_alethe(&proof),
        Ok(true),
        "check_alethe must accept the driver's FULL proof and derive (cl)"
    );
}

#[test]
fn self_checks_eq_and_ult_conflict() {
    // (= a b) ∧ (bvult a b) over 1-bit — the committed template.
    let mut arena = TermArena::new();
    let a = bv(&mut arena, "a", 1);
    let b = bv(&mut arena, "b", 1);
    let eq = arena.eq(a, b).unwrap();
    let ult = arena.bv_ult(a, b).unwrap();
    self_checks(&arena, &[eq, ult]);
}

#[test]
fn self_checks_eq_and_neq_conflict() {
    // (= a b) ∧ (not (= a b)) over width 2.
    let mut arena = TermArena::new();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let eq = arena.eq(a, b).unwrap();
    let neq = arena.not(eq).unwrap();
    self_checks(&arena, &[eq, neq]);
}

#[test]
fn self_checks_ult_cycle_conflict() {
    // (bvult a b) ∧ (bvult b a) over width 2 — antisymmetry of <.
    let mut arena = TermArena::new();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let ab = arena.bv_ult(a, b).unwrap();
    let ba = arena.bv_ult(b, a).unwrap();
    self_checks(&arena, &[ab, ba]);
}

#[test]
fn self_checks_slt_and_eq_conflict() {
    // (bvslt a b) ∧ (= a b) over width 3 — exercises bitblast_slt + bitblast_equal.
    let mut arena = TermArena::new();
    let a = bv(&mut arena, "a", 3);
    let b = bv(&mut arena, "b", 3);
    let slt = arena.bv_slt(a, b).unwrap();
    let eq = arena.eq(a, b).unwrap();
    self_checks(&arena, &[slt, eq]);
}

#[test]
fn self_checks_bitwise_compound() {
    // (= (bvand a b) c) ∧ (= a b) ∧ (not (= b c)) over width 2 — a compound operand
    // reduced bottom-up via cong + bitblast_and + trans.
    let mut arena = TermArena::new();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let c = bv(&mut arena, "c", 2);
    let and = arena.bv_and(a, b).unwrap();
    let eq_and_c = arena.eq(and, c).unwrap();
    let eq_ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let neq_bc = arena.not(bc).unwrap();
    self_checks(&arena, &[eq_and_c, eq_ab, neq_bc]);
}

#[test]
fn self_checks_bvand_idempotent_compound() {
    // (not (= (bvand a a) a)) over width 3 — shared operand `a`, DAG-deduped.
    let mut arena = TermArena::new();
    let a = bv(&mut arena, "a", 3);
    let and = arena.bv_and(a, a).unwrap();
    let eq = arena.eq(and, a).unwrap();
    let neq = arena.not(eq).unwrap();
    self_checks(&arena, &[neq]);
}

#[test]
fn self_checks_arithmetic_compound() {
    // (= (bvadd a b) c) ∧ (= (bvadd a b) d) ∧ (not (= c d)) over width 3 — the
    // shared `(bvadd a b)` is reduced once via bitblast_add.
    let mut arena = TermArena::new();
    let a = bv(&mut arena, "a", 3);
    let b = bv(&mut arena, "b", 3);
    let c = bv(&mut arena, "c", 3);
    let d = bv(&mut arena, "d", 3);
    let sum = arena.bv_add(a, b).unwrap();
    let eq_c = arena.eq(sum, c).unwrap();
    let eq_d = arena.eq(sum, d).unwrap();
    let cd = arena.eq(c, d).unwrap();
    let neq_cd = arena.not(cd).unwrap();
    self_checks(&arena, &[eq_c, eq_d, neq_cd]);
}

#[test]
fn self_checks_nested_compound() {
    // (= (bvand (bvor a b) c) d) ∧ (= (bvor a b) c) ∧ (not (= c d)) over width 2 —
    // a genuinely nested compound (inner bvor, outer bvand), bottom-up.
    let mut arena = TermArena::new();
    let a = bv(&mut arena, "a", 2);
    let b = bv(&mut arena, "b", 2);
    let c = bv(&mut arena, "c", 2);
    let d = bv(&mut arena, "d", 2);
    let or = arena.bv_or(a, b).unwrap();
    let and = arena.bv_and(or, c).unwrap();
    let eq_and_d = arena.eq(and, d).unwrap();
    let eq_or_c = arena.eq(or, c).unwrap();
    let cd = arena.eq(c, d).unwrap();
    let neq_cd = arena.not(cd).unwrap();
    self_checks(&arena, &[eq_and_d, eq_or_c, neq_cd]);
}

#[test]
fn self_checks_compound_in_ult_predicate() {
    // (bvult (bvadd a b) c) ∧ (= (bvadd a b) c) over width 3 — a compound operand
    // inside a bvult predicate (not just `=`).
    let mut arena = TermArena::new();
    let a = bv(&mut arena, "a", 3);
    let b = bv(&mut arena, "b", 3);
    let c = bv(&mut arena, "c", 3);
    let sum = arena.bv_add(a, b).unwrap();
    let ult = arena.bv_ult(sum, c).unwrap();
    let eq = arena.eq(sum, c).unwrap();
    self_checks(&arena, &[ult, eq]);
}
