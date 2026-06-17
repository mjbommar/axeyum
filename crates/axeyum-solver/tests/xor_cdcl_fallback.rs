//! Integration tests for the opt-in CDCL(XOR) search fallback (ADR-0035).
//!
//! The fallback only fires when the batsat solve returns `unknown` (timeout /
//! budget) on an XOR-structured formula AND `xor_cdcl_fallback` is set. These
//! tests pin the **default-off** guarantee (the flag changes nothing on
//! instances batsat already decides) and the soundness story (a fallback `unsat`
//! surfaces the `XorGaussian` trust step in produced evidence; a fallback `sat`
//! is replay-checked). The unit-level fallback mechanics (verdict upgrade,
//! gating, stats) are covered inline in `sat_bv_backend.rs`.

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{
    CheckResult, Evidence, EvidenceReport, SatBvBackend, SolverBackend, SolverConfig, TrustId,
    produce_qf_bv_evidence,
};

fn xor_query() -> (TermArena, Vec<TermId>) {
    // A small XOR-structured BV query: (x ^ y) = 1 over 1-bit vectors, which the
    // Tseitin encoding exposes as a recognizable XOR gate. Satisfiable.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 1).unwrap();
    let y = arena.bv_var("y", 1).unwrap();
    let xor = arena.bv_xor(x, y).unwrap();
    let one = arena.bv_const(1, 1).unwrap();
    let eq = arena.eq(xor, one).unwrap();
    (arena, vec![eq])
}

#[test]
fn flag_off_is_the_default() {
    // The new flag defaults to false: enabling nothing leaves it off.
    assert!(!SolverConfig::default().xor_cdcl_fallback);
    assert!(!SolverConfig::new().xor_cdcl_fallback);
    assert!(
        SolverConfig::new()
            .with_xor_cdcl_fallback(true)
            .xor_cdcl_fallback
    );
}

#[test]
fn fallback_flag_does_not_change_a_decided_verdict() {
    // On an instance batsat decides outright, turning the fallback on must not
    // change the verdict (the fallback only ever acts on `unknown`). This is the
    // default-off / no-regression guarantee made observable.
    let (arena, assertions) = xor_query();

    let off = SatBvBackend::new()
        .check(&arena, &assertions, &SolverConfig::default())
        .expect("check off");
    let on = SatBvBackend::new()
        .check(
            &arena,
            &assertions,
            &SolverConfig::new().with_xor_cdcl_fallback(true),
        )
        .expect("check on");

    assert!(matches!(off, CheckResult::Sat(_)));
    assert_eq!(off, on, "flag must not change a verdict batsat decides");
}

#[test]
fn decided_unsat_evidence_unaffected_by_flag() {
    // `x != x` over BV is unsat and batsat decides it: the evidence is a real
    // certificate (term-level / DRAT), and the `XorGaussian` step must NOT appear
    // — the fallback never fired.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let eq_self = arena.eq(x, x).unwrap();
    let neq = arena.not(eq_self).unwrap();

    let report: EvidenceReport = produce_qf_bv_evidence(
        &arena,
        &[neq],
        &SolverConfig::new().with_xor_cdcl_fallback(true),
    )
    .expect("evidence");

    assert!(matches!(
        report.evidence,
        Evidence::Unsat(_) | Evidence::UnsatTermLevel { .. }
    ));
    assert!(
        report
            .trusted_steps
            .iter()
            .all(|s| s.id != TrustId::XorGaussian),
        "no XorGaussian step when batsat decided the unsat"
    );
    assert!(report.evidence.check(&arena, &[neq]).expect("re-check"));
}

#[test]
fn sat_model_replays_with_flag_on() {
    // A satisfiable XOR query with the flag on still produces a replay-checkable
    // model (whether or not the fallback contributed it).
    let (arena, assertions) = xor_query();
    let report = produce_qf_bv_evidence(
        &arena,
        &assertions,
        &SolverConfig::new().with_xor_cdcl_fallback(true),
    )
    .expect("evidence");
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.check(&arena, &assertions).expect("replay"));
}
