//! `bv2nat`-bound UNSAT certificates in the evidence layer.
//!
//! A `bv2nat`-bound contradiction such as `bv2nat(x) >= 16` for a 4-bit `x` is
//! UNSAT because `bv2nat` of a `W`-bit value is in `[0, 2^W - 1]`. The exact
//! integer refuters reject a raw `bv2nat(b)` subterm, so such a query was a bare
//! `Evidence::Unsat(None)`. [`produce_evidence`] now abstracts each `bv2nat(b)` to
//! a fresh `Int` symbol plus its **trusted** range axiom `0 <= n <= 2^W - 1`
//! (ledgered as [`TrustId::IntBlast`], the int↔BV-width bridge) and emits a
//! `lia_generic` Alethe certificate over the pure-LIA abstraction
//! ([`Evidence::UnsatArithAletheProof`]). `Evidence::check` re-validates that LIA
//! refutation through [`axeyum_solver::check_alethe_lra`], so the bulk of the
//! refutation (the Farkas/`lia_generic` step) is re-derived, **certified**; only
//! the range axiom is trusted.
//!
//! These tests pin: the new certificate is emitted, re-checks, and carries the
//! documented trust steps (`IntBlast` trusted, `Farkas` certified); a second width;
//! tampering breaks the check; and the existing `QF_LIA` / `QF_BV` evidence routes
//! are unchanged, while a satisfiable `bv2nat` query is never reported `unsat`.

use std::time::Duration;

use axeyum_ir::TermArena;
use axeyum_solver::{Evidence, SolverConfig, TrustId, produce_evidence};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

/// `bv2nat(x) >= 16` for a 4-bit `x`: UNSAT because `bv2nat(x) <= 15`. Was a bare
/// `Unsat(None)`; now a certified arithmetic Alethe proof over the abstraction,
/// with the `bv2nat`-range step trusted (`IntBlast`) and the LIA refutation
/// certified (`Farkas`).
#[test]
fn produce_evidence_certifies_bv2nat_ge_16_unsat() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let n = arena.bv2nat(x).unwrap();
    let sixteen = arena.int_const(16);
    let ge16 = arena.int_ge(n, sixteen).unwrap();
    let assertions = [ge16];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(_) = &report.evidence else {
        panic!(
            "expected an arithmetic-Alethe-certified bv2nat-bound unsat, got {:?}",
            report.evidence
        );
    };
    assert!(report.evidence.is_certified());
    // The certificate re-validates through the arithmetic-aware checker.
    assert!(report.evidence.check(&arena, &assertions).unwrap());

    // Trust accounting: the LIA refutation is CERTIFIED (re-derived); the
    // `bv2nat`-range abstraction is the one trusted step (`IntBlast`, not certified).
    let farkas = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::Farkas)
        .expect("the bv2nat-bound cert records the Farkas trust step");
    assert!(
        farkas.certified,
        "the lia_generic proof over the abstraction is re-derived, so Farkas is certified"
    );
    let intblast = report
        .trusted_steps
        .iter()
        .find(|s| s.id == TrustId::IntBlast)
        .expect("the bv2nat-bound cert records the IntBlast (range-axiom) trust step");
    assert!(
        !intblast.certified,
        "the bv2nat range axiom is asserted, not re-derived — a trust hole"
    );
}

/// A second width: `bv2nat(y) >= 256` for an 8-bit `y` (UNSAT, `bv2nat(y) <= 255`).
#[test]
fn produce_evidence_certifies_bv2nat_8bit_ge_256_unsat() {
    let mut arena = TermArena::new();
    let y = arena.bv_var("y", 8).unwrap();
    let n = arena.bv2nat(y).unwrap();
    let limit = arena.int_const(256);
    let ge = arena.int_ge(n, limit).unwrap();
    let assertions = [ge];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(_) = &report.evidence else {
        panic!(
            "expected an arithmetic-Alethe-certified 8-bit bv2nat-bound unsat, got {:?}",
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
    assert!(
        report
            .trusted_steps
            .iter()
            .any(|s| s.id == TrustId::IntBlast && !s.certified)
    );
}

/// Tampering with the proof must make `Evidence::check` reject it: a real cert
/// re-validates only a genuine refutation. We drop the final resolution step that
/// closes to the empty clause, so the proof no longer derives `(cl)`.
#[test]
fn tampered_bv2nat_bound_evidence_fails_its_own_check() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let n = arena.bv2nat(x).unwrap();
    let sixteen = arena.int_const(16);
    let ge16 = arena.int_ge(n, sixteen).unwrap();
    let assertions = [ge16];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    let Evidence::UnsatArithAletheProof(proof) = &report.evidence else {
        panic!(
            "expected an arithmetic-Alethe bv2nat-bound unsat, got {:?}",
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
        "tampered bv2nat-bound Alethe proof was accepted — check is not real"
    );
}

/// A satisfiable `bv2nat` query (`bv2nat(x) = 7` for a 4-bit `x`) is never reported
/// `unsat`: the abstraction is a relaxation, so the bv2nat cert declines (it is not
/// LIA-unsat), and the engine decides `sat` with a replay-checkable model.
#[test]
fn sat_bv2nat_query_is_not_reported_unsat() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let n = arena.bv2nat(x).unwrap();
    let seven = arena.int_const(7);
    let eq7 = arena.eq(n, seven).unwrap();
    let assertions = [eq7];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    assert!(
        matches!(report.evidence, Evidence::Sat(_) | Evidence::Unknown(_)),
        "a satisfiable bv2nat query must be sat (or unknown), never unsat, got {:?}",
        report.evidence
    );
    // If decided sat, the model replays.
    if let Evidence::Sat(_) = &report.evidence {
        assert!(report.evidence.check(&arena, &assertions).unwrap());
    }
}

/// Regression: a plain `QF_LIA` unsat (`x > 0 ∧ x < 0`, no `bv2nat`) still gets a
/// **checked** arithmetic certificate with no `IntBlast` (bv2nat-range) trust
/// hole. The exact route has since upgraded: the arith-DPLL theory-enumeration
/// cert (`d3b0d2e1`, "close `QF_LIA` dominance") now decides this instance ahead
/// of the older Farkas Alethe path — both are internally re-checkable (Carcara
/// has no `lia_generic`, so neither was externally checkable for integers), so
/// the intent of this regression (checked cert, no `IntBlast` hole) is
/// unchanged.
#[test]
fn plain_qf_lia_unsat_evidence_unchanged() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let zero = arena.int_const(0);
    let gt0 = arena.int_gt(x, zero).unwrap();
    let lt0 = arena.int_lt(x, zero).unwrap();
    let assertions = [gt0, lt0];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    assert!(
        matches!(
            report.evidence,
            Evidence::UnsatArithDpll(_) | Evidence::UnsatArithAletheProof(_)
        ),
        "expected a checked QF_LIA arith cert, got {:?}",
        report.evidence
    );
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    assert!(
        !report
            .trusted_steps
            .iter()
            .any(|s| s.id == TrustId::IntBlast),
        "the plain LIA cert must NOT record a bv2nat-range (IntBlast) trust hole"
    );
}

/// Regression: a pure `QF_BV` unsat still gets its bit-blast / term-level
/// certificate — the bv2nat-bound addition must not shadow the `QF_BV` route.
#[test]
fn qf_bv_unsat_evidence_unchanged() {
    let mut arena = TermArena::new();
    let av = arena.bv_var("a", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let eq0 = arena.eq(av, zero).unwrap();
    let eq1 = arena.eq(av, one).unwrap();
    let assertions = [eq0, eq1];

    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    assert!(
        !matches!(report.evidence, Evidence::UnsatArithAletheProof(_)),
        "QF_BV unsat must not use the arithmetic-Alethe route"
    );
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
}
