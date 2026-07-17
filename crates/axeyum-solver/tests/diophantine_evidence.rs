//! Self-checking, Lean-backed integer-infeasibility (Diophantine) `unsat` evidence
//! (ADR-0043).
//!
//! [`produce_diophantine_evidence`] attaches an [`Evidence::UnsatDiophantine`]
//! certificate to a system of integer equalities that is integer-infeasible (e.g.
//! `x + y = 0 ∧ x − y = 1 ⇒ 2x = 1`). The certificate is fully self-contained:
//! [`Evidence::check`] re-validates it via the independent integer-Farkas re-checker
//! and — when the Diophantine→Lean reconstruction covers the query — ALSO re-derives
//! the kernel-checked Lean module.
//!
//! These tests assert (a) the certificate is produced and INDEPENDENTLY re-validates,
//! (b) the carried Lean module is the kernel-checked refutation, and (c) an
//! integer-FEASIBLE system yields no Diophantine evidence (never a wrong `unsat`).
//! All arithmetic is exact — no floating point.
#![cfg(feature = "full")]

use axeyum_ir::TermArena;
use axeyum_solver::{Evidence, SolverConfig, produce_diophantine_evidence, produce_evidence};

/// The DEFAULT evidence path (`produce_evidence`) routes an integer-infeasible system
/// to the Lean-backed Diophantine certificate — not just the standalone producer.
#[test]
fn default_produce_evidence_routes_integer_infeasibility_to_diophantine() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let zero = arena.int_const(0);
    let e1 = arena.eq(xpy, zero).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let one = arena.int_const(1);
    let e2 = arena.eq(xmy, one).unwrap();
    let assertions = [e1, e2];

    let report = produce_evidence(&mut arena, &assertions, &SolverConfig::default())
        .expect("produce_evidence must not error");
    assert!(
        matches!(report.evidence, Evidence::UnsatDiophantine { .. }),
        "the default path must route 2x=1 to UnsatDiophantine, got {:?}",
        report.evidence
    );
    assert!(
        report
            .evidence
            .check(&arena, &assertions)
            .expect("check must not error"),
        "the routed Diophantine evidence must independently re-check"
    );
}

/// `x + y = 0 ∧ x − y = 1` over `Int`: rational-feasible (`x = ½`) yet
/// integer-infeasible (`2x = 1`). The producer must emit `Evidence::UnsatDiophantine`
/// that independently re-checks.
#[test]
fn two_x_eq_one_produces_self_checking_diophantine_evidence() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let zero = arena.int_const(0);
    let e1 = arena.eq(xpy, zero).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let one = arena.int_const(1);
    let e2 = arena.eq(xmy, one).unwrap();
    let assertions = [e1, e2];

    let report = produce_diophantine_evidence(&arena, &assertions)
        .expect("producer must not error")
        .expect("x+y=0 ∧ x−y=1 must produce a Diophantine certificate");
    assert!(
        matches!(report.evidence, Evidence::UnsatDiophantine { .. }),
        "expected a Diophantine certificate, got {:?}",
        report.evidence
    );
    assert!(
        report
            .evidence
            .check(&arena, &assertions)
            .expect("check must not error"),
        "the Diophantine evidence must independently re-validate"
    );
}

/// The same integer-infeasible system carries a kernel-checked Lean module, and
/// `check` re-derives + re-verifies it through the trusted kernel.
#[test]
fn diophantine_evidence_carries_a_kernel_checked_lean_module() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let zero = arena.int_const(0);
    let e1 = arena.eq(xpy, zero).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let one = arena.int_const(1);
    let e2 = arena.eq(xmy, one).unwrap();
    let assertions = [e1, e2];

    let report = produce_diophantine_evidence(&arena, &assertions)
        .expect("producer must not error")
        .expect("integer-infeasible system must produce Diophantine evidence");
    let Evidence::UnsatDiophantine {
        ref lean_module, ..
    } = report.evidence
    else {
        panic!("expected UnsatDiophantine, got {:?}", report.evidence);
    };
    let module = lean_module
        .as_ref()
        .expect("2x=1 is Diophantine-reconstructable, so the evidence must carry a Lean module");
    assert!(
        module.contains("axeyum_refutation"),
        "the carried module must be the kernel-checked refutation"
    );
    // `check` re-derives the module and re-verifies it through the trusted kernel.
    assert!(
        report
            .evidence
            .check(&arena, &assertions)
            .expect("check must not error"),
        "the Lean-backed Diophantine evidence must re-check (certificate + kernel re-derivation)"
    );
}

/// An integer-FEASIBLE system `x + y = 2 ∧ x − y = 0` (sat at `x = y = 1`) has no
/// Diophantine refutation: the producer must decline (no evidence).
#[test]
fn feasible_system_produces_no_diophantine_evidence() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let two = arena.int_const(2);
    let e1 = arena.eq(xpy, two).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let zero = arena.int_const(0);
    let e2 = arena.eq(xmy, zero).unwrap();

    let evidence =
        produce_diophantine_evidence(&arena, &[e1, e2]).expect("producer must not error");
    assert!(
        evidence.is_none(),
        "x+y=2 ∧ x−y=0 is integer-satisfiable; the producer must decline (no certificate)"
    );
}
