//! Mixed arithmetic-sorted UF + linear-arithmetic UNSAT certificates in the
//! evidence layer (`QF_UFLIA` / `QF_UFLRA`).
//!
//! A mixed `unsat` like `f(x)=1 ∧ f(y)=2 ∧ x=y` (f:Int→Int, and the Real twin)
//! was previously a bare `Evidence::Unsat(None)`. It now carries an
//! independently-checkable, ZERO-TRUST-HOLE Alethe certificate
//! ([`Evidence::UnsatArithAletheProof`]) whose conflict is congruence-then-
//! arithmetic: `x=y ⊢ f(x)=f(y)` by `eq_congruent` (one congruence step), then
//! `f(x)=1 ∧ f(y)=2 ∧ f(x)=f(y) ⊢ 1=2` by `lia_generic`/`la_generic`. Both halves
//! re-check through the arithmetic-aware kernel ([`axeyum_solver::check_alethe_lra`]),
//! so the functional-consistency reduction is re-derived, not trusted.
//!
//! These tests pin: the mixed certificate is emitted and re-checks (Int and Real),
//! tampering breaks the check, a 2-ary UF works, and the existing routes are
//! unregressed (`QF_UFBV` still BV zero-trust, `QF_LIA` still gap-E certified, a
//! `QF_UFLRA` *sat* still solves with no false unsat).
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena};
use axeyum_solver::{Evidence, SolverConfig, TrustId, produce_evidence};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

/// `f(x)=1 ∧ f(y)=2 ∧ x=y` over `f : Int → Int` is UNSAT. It now carries the
/// mixed congruence-then-arithmetic zero-trust certificate.
#[test]
fn produce_evidence_certifies_uflia_congruence_arith() {
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let a1 = arena.eq(fx, one).unwrap();
    let a2 = arena.eq(fy, two).unwrap();
    let a3 = arena.eq(x, y).unwrap();
    let assertions = [a1, a2, a3];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(_) = &report.evidence else {
        panic!(
            "expected a mixed UF+arith Alethe-certified unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    // The mixed (congruence + arithmetic) proof re-validates end-to-end.
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    // ZERO trust holes: the congruence is proven by `eq_congruent`, the arithmetic
    // by `lia_generic`, both re-derived — so the cert records no trust steps.
    assert!(
        report.trusted_steps.is_empty(),
        "the zero-trust UF+arith cert records no trust holes, got {:?}",
        report.trusted_steps
    );
}

/// The Real twin: `f(x)=1 ∧ f(y)=2 ∧ x=y` over `f : Real → Real` is UNSAT.
#[test]
fn produce_evidence_certifies_uflra_congruence_arith() {
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let two = arena.real_const(Rational::integer(2));
    let a1 = arena.eq(fx, one).unwrap();
    let a2 = arena.eq(fy, two).unwrap();
    let a3 = arena.eq(x, y).unwrap();
    let assertions = [a1, a2, a3];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(_) = &report.evidence else {
        panic!(
            "expected a mixed UF+real-arith Alethe-certified unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

/// A 2-ary UF: `f(a,b)=1 ∧ f(c,d)=2 ∧ a=c ∧ b=d` (f:Int×Int→Int) is UNSAT by
/// congruence on both argument positions then arithmetic.
#[test]
fn produce_evidence_certifies_two_arg_uflia() {
    let mut arena = TermArena::new();
    let func = arena
        .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let a1 = arena.int_var("a1").unwrap();
    let b1 = arena.int_var("b1").unwrap();
    let a2 = arena.int_var("a2").unwrap();
    let b2 = arena.int_var("b2").unwrap();
    let fab = arena.apply(func, &[a1, b1]).unwrap();
    let fcd = arena.apply(func, &[a2, b2]).unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let e1 = arena.eq(fab, one).unwrap();
    let e2 = arena.eq(fcd, two).unwrap();
    let e3 = arena.eq(a1, a2).unwrap();
    let e4 = arena.eq(b1, b2).unwrap();
    let assertions = [e1, e2, e3, e4];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(_) = &report.evidence else {
        panic!(
            "expected a 2-ary UF+arith Alethe-certified unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

/// Tampering with the mixed proof must make `Evidence::check` reject it. We drop
/// the final command (the closing empty-clause resolution), so the proof no longer
/// derives `(cl)` — a genuine check rejects the mutilated certificate.
#[test]
fn tampered_uflia_arith_evidence_fails_its_own_check() {
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let a1 = arena.eq(fx, one).unwrap();
    let a2 = arena.eq(fy, two).unwrap();
    let a3 = arena.eq(x, y).unwrap();
    let assertions = [a1, a2, a3];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(proof) = &report.evidence else {
        panic!(
            "expected a mixed UF+arith Alethe unsat, got {:?}",
            report.evidence
        );
    };
    // The genuine proof checks.
    assert!(report.evidence.check(&arena, &assertions).unwrap());

    // Drop the last command (the empty-clause resolution): the mutated proof no
    // longer closes to `(cl)`, so the arithmetic checker must NOT accept it.
    let mut tampered = proof.clone();
    tampered.pop();
    let bogus = Evidence::UnsatArithAletheProof(tampered);
    assert!(
        !matches!(bogus.check(&arena, &assertions), Ok(true)),
        "tampered mixed UF+arith Alethe proof was accepted — check is not real"
    );
}

/// Regression: a pure `QF_UFBV` unsat still reaches the bit-vector zero-trust
/// Alethe certificate (Ackermann), NOT the arithmetic route — the UFLIA emitter
/// declines BV-sorted UF applications.
#[test]
fn qf_ufbv_unsat_still_bv_zero_trust() {
    let mut arena = TermArena::new();
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
    let Evidence::UnsatAletheProof(_) = &report.evidence else {
        panic!(
            "expected the bit-vector zero-trust Alethe cert for QF_UFBV, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

/// Regression: a pure `QF_LIA` unsat (no UF) still gets its gap-E `lia_generic`
/// certificate — the UFLIA emitter declines (no UF applications), so the pure
/// arithmetic path still fires with the Farkas trust step recorded.
#[test]
fn pure_lia_unsat_still_gap_e_certified() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let zero = arena.int_const(0);
    let gt0 = arena.int_gt(x, zero).unwrap();
    let lt0 = arena.int_lt(x, zero).unwrap();
    let assertions = [gt0, lt0];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(_) = &report.evidence else {
        panic!(
            "expected the gap-E LIA arithmetic cert, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    // The pure-LIA path records the Farkas trust step as certified (distinct from
    // the UFLIA route, which records no trust steps).
    assert!(
        report
            .trusted_steps
            .iter()
            .any(|s| s.id == TrustId::Farkas && s.certified),
        "pure LIA unsat must keep its gap-E Farkas-certified route"
    );
}

/// Regression: a satisfiable `QF_UFLRA` query must NOT be reported `unsat` (no
/// false unsat from the new emitter). With `x ≠ y` there is no congruence
/// collapse, so `f(x)=1 ∧ f(y)=2` is satisfiable; the engine returns `Sat` (replay-
/// checked) or a documented `Unknown` (sat-model projection for an arithmetic-sorted
/// UF is unsupported — UNSAT is decided), but never a (false) `unsat` variant.
#[test]
fn qf_uflra_sat_not_false_unsat() {
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let two = arena.real_const(Rational::integer(2));
    let zero = arena.real_const(Rational::integer(0));
    let a1 = arena.eq(fx, one).unwrap();
    let a2 = arena.eq(fy, two).unwrap();
    // x = 0 ∧ y = 1: distinct arguments, so the two f-values can differ → sat.
    let a3 = arena.eq(x, zero).unwrap();
    let a4 = arena.eq(y, one).unwrap();
    let assertions = [a1, a2, a3, a4];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    match &report.evidence {
        // A sat model must replay-check against the original assertions.
        Evidence::Sat(_) => assert!(report.evidence.check(&arena, &assertions).unwrap()),
        // A documented Unknown is acceptable (sat-model projection for an
        // arithmetic-sorted UF is unsupported); it is not a false unsat.
        Evidence::Unknown(_) => {}
        // The soundness property: the new mixed UF+arith emitter must NEVER turn a
        // satisfiable query into any `unsat` variant.
        other => panic!("a satisfiable QF_UFLRA query was reported unsat: {other:?}"),
    }
}
