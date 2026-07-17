//! The "fill the proof step" tutor mechanic (Tier-D #19): the in-tree Alethe
//! checker `check_alethe` is a **sound auto-grader** — it accepts a complete,
//! correct proof and rejects one that is missing a step. A student who fills the
//! final derivation correctly is accepted; an incomplete attempt is not. This is
//! "trusted small checking" used pedagogically: the grader is the independent
//! checker, never the search.
#![cfg(feature = "full")]

use axeyum_cnf::check_alethe;
use axeyum_ir::{Sort, TermArena};
use axeyum_solver::prove_qf_bv_unsat_alethe;

/// Builds the unsatisfiable `(bvult a b) ∧ (bvult b a)` over `BitVec(4)` and the
/// full Alethe refutation axeyum emits for it.
fn build_proof() -> Vec<axeyum_cnf::AletheCommand> {
    let mut arena = TermArena::new();
    let a = arena
        .declare("a", Sort::BitVec(4))
        .map(|s| arena.var(s))
        .unwrap();
    let b = arena
        .declare("b", Sort::BitVec(4))
        .map(|s| arena.var(s))
        .unwrap();
    let a_lt_b = arena.bv_ult(a, b).unwrap();
    let b_lt_a = arena.bv_ult(b, a).unwrap();
    prove_qf_bv_unsat_alethe(&arena, &[a_lt_b, b_lt_a])
        .expect("(bvult a b) ∧ (bvult b a) is in the QF_BV Alethe fragment and unsat")
}

#[test]
fn complete_proof_is_accepted() {
    let proof = build_proof();
    assert!(
        matches!(check_alethe(&proof), Ok(true)),
        "the complete, correct proof must be accepted by the grader"
    );
}

#[test]
fn proof_with_a_missing_final_step_is_rejected() {
    let proof = build_proof();
    assert!(proof.len() >= 2, "proof should have several steps");
    // Remove the last command (the step that closes the refutation): the "hole".
    let with_hole = &proof[..proof.len() - 1];
    assert!(
        !matches!(check_alethe(with_hole), Ok(true)),
        "a proof missing its closing step must NOT be accepted — the grader is sound"
    );
}
