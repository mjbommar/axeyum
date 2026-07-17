//! Arithmetic UNSAT certificates in the evidence layer (gap E follow-through).
//!
//! A pure linear-integer (`QF_LIA`) `unsat` decided via [`produce_evidence`] now
//! carries an independently-checkable `lia_generic` Alethe certificate
//! ([`Evidence::UnsatArithAletheProof`]) instead of a bare `Evidence::Unsat(None)`.
//! `Evidence::check` re-validates it with the arithmetic-aware checker
//! ([`axeyum_solver::check_alethe_lra`]), so the Farkas reduction is re-derived,
//! not trusted. These tests pin: the new certificate is emitted and re-checks,
//! tampering breaks the check, and the existing `QF_BV` / `QF_UFBV` evidence routes
//! are unchanged (no shadowing of the zero-trust cert).
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{Evidence, SolverConfig, TrustId, produce_evidence};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

/// `x > 0 ∧ x < 0` (i.e. `x >= 1 ∧ x <= -1`): the canonical `QF_LIA` conflict.
/// Was a bare `Unsat(None)`; now a certified arithmetic Alethe proof.
#[test]
fn produce_evidence_certifies_simple_lia_unsat() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let zero = arena.int_const(0);
    let gt0 = arena.int_gt(x, zero).unwrap();
    let lt0 = arena.int_lt(x, zero).unwrap();
    let assertions = [gt0, lt0];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(_) = &report.evidence else {
        panic!(
            "expected an arithmetic-Alethe-certified LIA unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    // The certificate re-validates through the arithmetic-aware checker.
    assert!(report.evidence.check(&arena, &assertions).unwrap());

    // The Farkas/lia_generic reduction is CERTIFIED (re-derived), not a trust hole.
    let farkas = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::Farkas)
        .expect("the LIA cert records the Farkas trust step");
    assert!(
        farkas.certified,
        "the lia_generic proof is re-derived by check_alethe_lra, so Farkas is certified"
    );
}

/// A multi-constraint LIA conflict: `x + y >= 3 ∧ x <= 1 ∧ y <= 1`.
#[test]
fn produce_evidence_certifies_multi_constraint_lia_unsat() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let one = arena.int_const(1);
    let three = arena.int_const(3);
    let sum = arena.int_add(x, y).unwrap();
    let sum_ge3 = arena.int_ge(sum, three).unwrap();
    let x_le1 = arena.int_le(x, one).unwrap();
    let y_le1 = arena.int_le(y, one).unwrap();
    let assertions = [sum_ge3, x_le1, y_le1];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(_) = &report.evidence else {
        panic!(
            "expected an arithmetic-Alethe-certified multi-constraint LIA unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    assert!(
        report
            .trusted_steps
            .iter()
            .any(|s| s.id == TrustId::Farkas && s.certified)
    );
}

/// Tampering with the proof must make `Evidence::check` reject it: a real cert
/// re-validates only a genuine refutation. We drop the final resolution step that
/// closes to the empty clause, so the proof no longer derives `(cl)`.
#[test]
fn tampered_lia_arith_evidence_fails_its_own_check() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let zero = arena.int_const(0);
    let gt0 = arena.int_gt(x, zero).unwrap();
    let lt0 = arena.int_lt(x, zero).unwrap();
    let assertions = [gt0, lt0];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(proof) = &report.evidence else {
        panic!(
            "expected an arithmetic-Alethe LIA unsat, got {:?}",
            report.evidence
        );
    };
    // The genuine proof checks.
    assert!(report.evidence.check(&arena, &assertions).unwrap());

    // Drop the last command (the empty-clause resolution step): the mutated proof
    // no longer closes to `(cl)`, so the arithmetic checker must NOT accept it.
    let mut tampered = proof.clone();
    tampered.pop();
    let bogus = Evidence::UnsatArithAletheProof(tampered);
    assert!(
        !matches!(bogus.check(&arena, &assertions), Ok(true)),
        "tampered arithmetic Alethe proof was accepted — check is not real"
    );
}

/// Regression: a pure `QF_BV` unsat still gets its bit-blast Alethe (or term-level)
/// certificate — the LIA addition must not shadow the `QF_BV` route.
#[test]
fn qf_bv_unsat_evidence_unchanged() {
    let mut arena = TermArena::new();
    let av = arena.bv_var("a", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    // a == 0 ∧ a == 1: unsat.
    let eq0 = arena.eq(av, zero).unwrap();
    let eq1 = arena.eq(av, one).unwrap();
    let assertions = [eq0, eq1];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    // A QF_BV unsat is certified by the term-level / bit-blast Alethe route, never
    // the arithmetic-Alethe route.
    assert!(
        !matches!(report.evidence, Evidence::UnsatArithAletheProof(_)),
        "QF_BV unsat must not use the arithmetic-Alethe route"
    );
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
}

/// Regression: a `QF_UFBV` unsat still reaches the zero-trust Alethe certificate
/// (Ackermann) — the LIA emitters return `None` for UF queries, so ordering the
/// arithmetic helper after `zero_trust_alethe_certificate` keeps that cert.
#[test]
fn qf_ufbv_unsat_evidence_unchanged() {
    let mut arena = TermArena::new();
    // f: BitVec(2) -> BitVec(2); f(a) == 0 ∧ a == b ∧ ¬(f(b) == 0): unsat by
    // Ackermann congruence over `f`.
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = arena.bv_var("a", 2).unwrap();
    let b = arena.bv_var("b", 2).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fb, c00).unwrap();
        arena.not(e).unwrap()
    };
    let assertions = [e1, e2, e3];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    // UF unsat is the zero-trust Alethe cert (UnsatAletheProof), NOT the arithmetic
    // route, and is certified.
    let Evidence::UnsatAletheProof(_) = &report.evidence else {
        panic!(
            "expected a zero-trust Alethe-certified QF_UFBV unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    assert!(
        report.trusted_steps.is_empty(),
        "the zero-trust UF cert records no trust holes"
    );
}
