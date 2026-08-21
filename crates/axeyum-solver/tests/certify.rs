//! Term-level `unsat`/`sat` certification by exhaustive evaluation — the trust
//! dual of model replay, using only the ground evaluator.
#![cfg(feature = "full")]

use axeyum_ir::{TermArena, Value};
use axeyum_solver::{CertifyOutcome, certify_qf_bv_by_enumeration};

#[test]
fn exhaustive_evaluation_certifies_unsat_at_the_term_level() {
    // x & 1 == 1 AND x & 1 == 0 over BV4: no assignment satisfies both.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let masked = arena.bv_and(x, one).unwrap();
    let is_one = arena.eq(masked, one).unwrap();
    let is_zero = arena.eq(masked, zero).unwrap();

    let outcome = certify_qf_bv_by_enumeration(&arena, &[is_one, is_zero], 20).unwrap();
    let CertifyOutcome::CertifiedUnsat { cases } = outcome else {
        panic!("expected certified unsat, got {outcome:?}");
    };
    assert_eq!(cases, 1 << 4, "all 16 four-bit values were checked");
}

#[test]
fn exhaustive_evaluation_finds_a_model_for_sat() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let sum = arena.bv_add(x, one).unwrap();
    let eq = arena.eq(sum, five).unwrap();

    let CertifyOutcome::Satisfiable(model) =
        certify_qf_bv_by_enumeration(&arena, &[eq], 20).unwrap()
    else {
        panic!("expected a model");
    };
    assert_eq!(
        model.get(arena.find_symbol("x").unwrap()),
        Some(Value::Bv { width: 8, value: 4 })
    );
}

#[test]
fn oversized_domain_is_reported_not_attempted() {
    // Two 32-bit symbols → 64 bits, far above the budget.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 32).unwrap();
    let y = arena.bv_var("y", 32).unwrap();
    let eq = arena.eq(x, y).unwrap();
    assert!(matches!(
        certify_qf_bv_by_enumeration(&arena, &[eq], 20).unwrap(),
        CertifyOutcome::DomainTooLarge { total_bits: 64 }
    ));
}

#[test]
fn agrees_with_a_known_bitvector_identity() {
    // forall-style identity as unsat-of-negation: NOT( (x ^ y) == (y ^ x) ) is
    // unsatisfiable (xor is commutative), certified by enumeration over 3+3 bits.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 3).unwrap();
    let y = arena.bv_var("y", 3).unwrap();
    let xy = arena.bv_xor(x, y).unwrap();
    let yx = arena.bv_xor(y, x).unwrap();
    let eq = arena.eq(xy, yx).unwrap();
    let neq = arena.not(eq).unwrap();
    assert!(matches!(
        certify_qf_bv_by_enumeration(&arena, &[neq], 20).unwrap(),
        CertifyOutcome::CertifiedUnsat { .. }
    ));
}

/// The arena is a shared DAG, so the symbol scan that precedes enumeration must
/// cost one visit per *node*, not one per *path*.
///
/// This shape is a `bvadd(prev, prev)` chain: 61 DAG nodes whose tree unfolding
/// has 2^60 leaves. It is not adversarial — it is what a bit-blasted `fp.div`
/// looks like, and the real instance
/// (`QF_BVFP/bitwuzla-regress-clean/solver__fp__Float-no-simp3-main.smt2`) made
/// this scan run 1.28e10 times in 90 s at flat memory and a flat 136 kB stack
/// before it was memoized.
///
/// The width is deliberately over the bit budget, so the call returns
/// `DomainTooLarge` and the scan is the only thing being measured — no
/// evaluation happens. The work runs on a worker thread so a regression
/// **fails** here instead of hanging the suite.
#[test]
fn symbol_scan_does_not_unfold_a_shared_dag() {
    use std::time::Duration;

    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let mut arena = TermArena::new();
        let x = arena.bv_var("shared_dag_x", 32).unwrap();
        let mut term = x;
        for _ in 0..60 {
            term = arena.bv_add(term, term).unwrap();
        }
        let zero = arena.bv_const(32, 0).unwrap();
        let eq = arena.eq(term, zero).unwrap();
        let _ = tx.send(certify_qf_bv_by_enumeration(&arena, &[eq], 20));
    });
    let outcome = rx
        .recv_timeout(Duration::from_secs(30))
        .expect("the symbol scan did not return (exponential DAG unfolding?)")
        .expect("a pure BV query is enumerable in principle");
    assert!(
        matches!(outcome, CertifyOutcome::DomainTooLarge { total_bits: 32 }),
        "a 32-bit symbol is past the 20-bit budget, got {outcome:?}"
    );
}
