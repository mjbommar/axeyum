//! Integration tests for the `QF_ABV` read-over-write-same Alethe emitter
//! [`axeyum_solver::prove_qf_abv_unsat_alethe`] (P3.5). Each emitted proof is
//! re-checked by the in-tree [`axeyum_cnf::check_alethe`] — the array proof is
//! validated end to end, not merely shaped.

use axeyum_cnf::{AletheCommand, check_alethe};
use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{distinct, prove_qf_abv_unsat_alethe};

/// Builds `(select (store a i v) i)` over `a : (Array (BitVec 4) (BitVec 8))` and
/// returns `(sel, v)`.
fn row_same_select(arena: &mut TermArena) -> (TermId, TermId) {
    let array = arena.array_var("a", 4, 8).unwrap();
    let i_sym = arena.declare("i", Sort::BitVec(4)).unwrap();
    let i = arena.var(i_sym);
    let v_sym = arena.declare("v", Sort::BitVec(8)).unwrap();
    let v = arena.var(v_sym);
    let stored = arena.store(array, i, v).unwrap();
    let sel = arena.select(stored, i).unwrap();
    (sel, v)
}

#[test]
fn row_same_disequality_proof_is_self_checked() {
    let mut arena = TermArena::new();
    let (sel, v) = row_same_select(&mut arena);
    let eq = arena.eq(sel, v).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = prove_qf_abv_unsat_alethe(&arena, &[neq]).expect("ROW-same proof");
    assert_eq!(
        check_alethe(&proof),
        Ok(true),
        "in-tree checker accepts the full array proof"
    );
    // Last command is the empty clause.
    match proof.last() {
        Some(AletheCommand::Step { clause, rule, .. }) => {
            assert!(clause.is_empty(), "closes to (cl)");
            assert_eq!(rule, "resolution");
        }
        other => panic!("expected empty-clause resolution step, got {other:?}"),
    }
}

#[test]
fn symmetric_disequality_proof_is_self_checked() {
    let mut arena = TermArena::new();
    let (sel, v) = row_same_select(&mut arena);
    let eq = arena.eq(v, sel).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = prove_qf_abv_unsat_alethe(&arena, &[neq]).expect("symmetric proof");
    assert_eq!(check_alethe(&proof), Ok(true));
}

#[test]
fn binary_distinct_proof_is_self_checked() {
    let mut arena = TermArena::new();
    let (sel, v) = row_same_select(&mut arena);
    let dis = distinct(&mut arena, &[sel, v]).unwrap();
    let proof = prove_qf_abv_unsat_alethe(&arena, &[dis]).expect("distinct proof");
    assert_eq!(check_alethe(&proof), Ok(true));
}

#[test]
fn conjunction_with_one_matching_assertion_is_proved() {
    // The ROW-same disequality is buried among unrelated assertions; the emitter
    // still finds it and closes the whole problem.
    let mut arena = TermArena::new();
    let (sel, v) = row_same_select(&mut arena);
    let p_sym = arena.declare("p", Sort::BitVec(8)).unwrap();
    let p = arena.var(p_sym);
    let q_sym = arena.declare("q", Sort::BitVec(8)).unwrap();
    let q = arena.var(q_sym);
    let unrelated = arena.eq(p, q).unwrap();
    let eq = arena.eq(sel, v).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = prove_qf_abv_unsat_alethe(&arena, &[unrelated, neq]).expect("proof");
    assert_eq!(check_alethe(&proof), Ok(true));
}

#[test]
fn different_index_is_none() {
    let mut arena = TermArena::new();
    let array = arena.array_var("a", 4, 8).unwrap();
    let i_sym = arena.declare("i", Sort::BitVec(4)).unwrap();
    let i = arena.var(i_sym);
    let j_sym = arena.declare("j", Sort::BitVec(4)).unwrap();
    let j = arena.var(j_sym);
    let v_sym = arena.declare("v", Sort::BitVec(8)).unwrap();
    let v = arena.var(v_sym);
    let stored = arena.store(array, i, v).unwrap();
    let sel = arena.select(stored, j).unwrap();
    let eq = arena.eq(sel, v).unwrap();
    let neq = arena.not(eq).unwrap();
    assert!(prove_qf_abv_unsat_alethe(&arena, &[neq]).is_none());
}

#[test]
fn plain_bv_disequality_is_none() {
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(8)).unwrap();
    let a = arena.var(a_sym);
    let b_sym = arena.declare("b", Sort::BitVec(8)).unwrap();
    let b = arena.var(b_sym);
    let eq = arena.eq(a, b).unwrap();
    let neq = arena.not(eq).unwrap();
    assert!(prove_qf_abv_unsat_alethe(&arena, &[neq]).is_none());
}

/// Array extensionality conflict: `a = b ∧ select(a, k) ≠ select(b, k)` is unsat by
/// congruence over `select` (treated as an uninterpreted function). The array
/// emitter has no read-over-write-same match here, so it routes to the EUF
/// congruence emitter — and the result still re-checks in-tree.
#[test]
fn array_extensionality_conflict_is_proved_via_congruence() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let k_sym = arena.declare("k", Sort::BitVec(4)).unwrap();
    let k = arena.var(k_sym);
    let sa = arena.select(a, k).unwrap();
    let sb = arena.select(b, k).unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let reads_equal = arena.eq(sa, sb).unwrap();
    let reads_differ = arena.not(reads_equal).unwrap();

    let proof = prove_qf_abv_unsat_alethe(&arena, &[a_eq_b, reads_differ])
        .expect("extensionality proof via congruence");
    assert_eq!(
        check_alethe(&proof),
        Ok(true),
        "extensionality proof re-checks"
    );
    assert!(
        matches!(proof.last(), Some(AletheCommand::Step { clause, .. }) if clause.is_empty()),
        "proof ends in the empty clause"
    );
}
