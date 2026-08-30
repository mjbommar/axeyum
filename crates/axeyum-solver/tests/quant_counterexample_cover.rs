//! ADR-0108: checked source-bound counterexample covers for quantified UNSAT.
#![cfg(feature = "full")]

use std::process::Command;
use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{
    CheckResult, Evidence, ProofFragment, QUANT_COUNTEREXAMPLE_COVER_CASE_CAP, SolverConfig,
    check_quantified_counterexample_cover, produce_evidence, prove_unsat_to_lean_module,
    quantified_counterexample_cover_refutation,
    reconstruct_quantified_counterexample_cover_to_lean_module, solve,
};

// The golden pin covers the module BODY; the shared banner is pinned once, in
// `axeyum-lean-kernel --test module_banner_pin`. Header text under many pins is
// what made this suite red three times -- see the helper's module note.
#[path = "../../axeyum-lean-kernel/tests/support/lean_golden.rs"]
mod lean_golden;

const CBQI_ITE: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__006-cbqi-ite.smt2"
);

fn assertions(script: &axeyum_smtlib::Script) -> Vec<axeyum_ir::TermId> {
    script
        .commands
        .iter()
        .filter_map(|command| match command {
            ScriptCommand::Assert(term) => Some(*term),
            _ => None,
        })
        .collect()
}

fn config(seconds: u64) -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(seconds))
}

fn small_cover_query() -> (TermArena, Vec<axeyum_ir::TermId>) {
    let mut arena = TermArena::new();
    let p = arena.declare("p", Sort::Bool).unwrap();
    let x = arena.declare("x", Sort::Int).unwrap();
    let b = arena.declare("b", Sort::Bool).unwrap();
    let p_term = arena.var(p);
    let x_term = arena.var(x);
    let b_term = arena.var(b);
    let one = arena.int_const(1);
    let x_plus_one = arena.int_add(x_term, one).unwrap();
    let selected = arena.ite(b_term, x_term, x_plus_one).unwrap();
    let equality = arena.eq(selected, x_term).unwrap();
    let body = arena.or(p_term, equality).unwrap();
    let forall_b = arena.forall(b, body).unwrap();
    let forall_x = arena.forall(x, forall_b).unwrap();
    let not_p = arena.not(p_term).unwrap();
    (arena, vec![forall_x, not_p])
}

#[test]
fn multi_binder_affine_ite_cover_is_source_checked() {
    let (mut arena, assertions) = small_cover_query();
    let certificate =
        quantified_counterexample_cover_refutation(&mut arena, &assertions, &config(5))
            .unwrap()
            .expect("one counterexample cube should cover p=false");
    assert_eq!(certificate.cases.len(), 1);
    assert_eq!(certificate.cases[0].bindings.len(), 2);
    assert!(check_quantified_counterexample_cover(
        &arena,
        &assertions,
        &certificate
    ));
    assert!(matches!(
        solve(&mut arena, &assertions, &config(5)).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn small_cover_reconstructs_through_the_lean_kernel() {
    let (mut arena, assertions) = small_cover_query();
    let certificate =
        quantified_counterexample_cover_refutation(&mut arena, &assertions, &config(5))
            .unwrap()
            .expect("one counterexample cube");
    let module = reconstruct_quantified_counterexample_cover_to_lean_module(
        &arena,
        &assertions,
        &certificate,
    )
    .expect("checked small cover should reconstruct");
    assert!(module.contains("theorem axeyum_refutation : False"));
    assert!(!module.contains("sorryAx"));
}

#[test]
fn small_cover_generated_module_is_byte_stable() {
    let (mut arena, assertions) = small_cover_query();
    let certificate =
        quantified_counterexample_cover_refutation(&mut arena, &assertions, &config(5))
            .unwrap()
            .expect("one counterexample cube");
    let module = reconstruct_quantified_counterexample_cover_to_lean_module(
        &arena,
        &assertions,
        &certificate,
    )
    .expect("checked small cover should reconstruct");
    // Re-pinned 2026-08-14 (was `7_814` / `0xeda4_bd52_aab5_6790`): `a5975725f` made
    // every reachable inductive a real Lean `inductive` instead of an opaque `axiom`.
    // Checked, not merely stable — Lean 4.30.0 accepts this module and `#print axioms`
    // reports only the query hypotheses, with no `sorryAx`.
    // The +1_640 of HEADER text that made this pin red on 2026-08-18 -- `b760fd6ae`
    // (+863, Lean's codegen constants) and `46724faec` (+777, `maxRecDepth`), the
    // third recurrence of one mechanism -- can no longer reach it: the pin below
    // covers the module BODY, and the banner is pinned once in
    // `axeyum-lean-kernel --test module_banner_pin`. If this moves, PROOF text
    // moved. See `crates/axeyum-lean-kernel/tests/support/lean_golden.rs`.
    // Re-pinned 2026-08-20 at the same 14_912-byte length: the native Bool
    // package now uses official Lean constructor order `[false, true]`, so the
    // checked `Bool.rec` proof writes its false minor before its true minor.
    // RE-PINNED 2026-08-30 -- a PERMUTATION, not an edit. Every one of the five
    // golden modules moved by +0 bytes with a different hash on the same day,
    // and the cause is shared: `a70e2dc4d` (four Int order-coercion mirrors)
    // and `07c9c9f09` (the sign-of-a-product family) added declarations that
    // reference `Int.le`/`Int.lt`, pulling both definitions earlier in the
    // dependency-ordered emission -- to directly after `inductive Int`.
    // Emitting a `def` earlier is always safe in Lean; a definition must
    // precede its uses, never follow them. Verified by dumping each module at
    // the previous pin commit and at HEAD: `LC_ALL=C sort | cmp` is IDENTICAL
    // for all five, so no character changed anywhere.
    //
    // `LC_ALL=C` is load-bearing in that check. Under this host's en_US.UTF-8,
    // GNU `sort` compares `--` and a blank line as EQUAL and breaks the tie by
    // input order, so a plain `sort | cmp` called two of these five "content
    // changed" when they are permutations like the rest.
    //
    // For the next mover: a `+0 bytes` delta on a golden body is the signature
    // of a reordering. `LC_ALL=C sort | cmp` on two dumps answers
    // "permutation or not" in one command, far cheaper than the bisect the
    // delta invites -- and three runs first, since a same-length hash change
    // is also what a nondeterministic render would produce.
    lean_golden::assert_golden_module(
        "counterexample-cover",
        &module,
        (14_912, 0x01ec_a1dd_2dc2_d94e),
    );
}

#[test]
fn oversized_cover_witness_declines_before_proof_building() {
    let (mut arena, assertions) = small_cover_query();
    let mut certificate =
        quantified_counterexample_cover_refutation(&mut arena, &assertions, &config(5))
            .unwrap()
            .expect("one counterexample cube");
    let (_, value) = certificate.cases[0]
        .bindings
        .iter_mut()
        .find(|(_, value)| matches!(value, Value::Int(_)))
        .expect("small cover has one Int witness");
    *value = Value::Int(5000);
    assert!(check_quantified_counterexample_cover(
        &arena,
        &assertions,
        &certificate
    ));
    assert!(
        reconstruct_quantified_counterexample_cover_to_lean_module(
            &arena,
            &assertions,
            &certificate,
        )
        .is_err()
    );
}

#[test]
fn malformed_source_cases_and_incomplete_covers_are_rejected() {
    let (mut arena, assertions) = small_cover_query();
    let certificate =
        quantified_counterexample_cover_refutation(&mut arena, &assertions, &config(5))
            .unwrap()
            .unwrap();

    let mut reordered = certificate.clone();
    reordered.cases[0].bindings.reverse();
    assert!(!check_quantified_counterexample_cover(
        &arena,
        &assertions,
        &reordered
    ));

    let mut changed = certificate.clone();
    changed.cases[0].bindings[1].1 = Value::Bool(true);
    assert!(!check_quantified_counterexample_cover(
        &arena,
        &assertions,
        &changed
    ));

    let mut duplicate = certificate.clone();
    duplicate.cases.push(duplicate.cases[0].clone());
    assert!(!check_quantified_counterexample_cover(
        &arena,
        &assertions,
        &duplicate
    ));

    let mut over_cap = certificate;
    while over_cap.cases.len() <= QUANT_COUNTEREXAMPLE_COVER_CASE_CAP {
        over_cap.cases.push(over_cap.cases[0].clone());
    }
    assert!(!check_quantified_counterexample_cover(
        &arena,
        &assertions,
        &over_cap
    ));
}

#[test]
fn public_cbqi_ite_row_has_checked_zero_trust_evidence() {
    let mut script = parse_script(CBQI_ITE).expect("parse 006-cbqi-ite");
    let assertions = assertions(&script);
    let report = produce_evidence(&mut script.arena, &assertions, &config(30)).unwrap();
    let Evidence::UnsatQuantifiedCounterexampleCover(certificate) = &report.evidence else {
        panic!(
            "expected counterexample-cover evidence, got {:?}",
            report.evidence
        );
    };
    assert!(!certificate.cases.is_empty());
    assert!(certificate.cases.len() <= QUANT_COUNTEREXAMPLE_COVER_CASE_CAP);
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
#[ignore = "public corpus kernel reconstruction; exercised explicitly in release validation"]
fn public_cbqi_ite_row_reconstructs_through_the_lean_kernel() {
    let mut script = parse_script(CBQI_ITE).expect("parse 006-cbqi-ite");
    let assertions = assertions(&script);
    let (fragment, module) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("006-cbqi-ite should reconstruct from its checked finite cover");
    assert_eq!(fragment, ProofFragment::QuantifiedCounterexampleCover);
    assert!(module.contains("theorem axeyum_refutation : False"));
    assert!(module.contains("inductive Bool"));
    assert!(!module.contains("axiom Bool.rec"));
    assert!(module.contains("def axeyum_proof_share_"));
    assert!(
        module.len() < 3_000_000,
        "compact cover module regressed to {} bytes",
        module.len()
    );
    assert!(!module.contains("sorryAx"));
}

#[test]
fn dropping_one_of_two_cover_cases_fails_closure() {
    let mut arena = TermArena::new();
    let p = arena.declare("p", Sort::Bool).unwrap();
    let q = arena.declare("q", Sort::Bool).unwrap();
    let x = arena.declare("x", Sort::Int).unwrap();
    let y = arena.declare("y", Sort::Int).unwrap();
    let p_term = arena.var(p);
    let q_term = arena.var(q);
    let x_term = arena.var(x);
    let y_term = arena.var(y);
    let x_ne_x = arena
        .eq(x_term, x_term)
        .and_then(|term| arena.not(term))
        .unwrap();
    let y_ne_y = arena
        .eq(y_term, y_term)
        .and_then(|term| arena.not(term))
        .unwrap();
    let p_body = arena.or(p_term, x_ne_x).unwrap();
    let q_body = arena.or(q_term, y_ne_y).unwrap();
    let forall_p = arena.forall(x, p_body).unwrap();
    let forall_q = arena.forall(y, q_body).unwrap();
    let both = arena.and(p_term, q_term).unwrap();
    let not_both = arena.not(both).unwrap();
    let assertions = vec![forall_p, forall_q, not_both];
    let certificate =
        quantified_counterexample_cover_refutation(&mut arena, &assertions, &config(5))
            .unwrap()
            .expect("two-cube cover");
    assert_eq!(certificate.cases.len(), 2);
    assert!(
        reconstruct_quantified_counterexample_cover_to_lean_module(
            &arena,
            &assertions,
            &certificate,
        )
        .is_err()
    );
    for index in 0..2 {
        let mut incomplete = certificate.clone();
        incomplete.cases.remove(index);
        assert!(!check_quantified_counterexample_cover(
            &arena,
            &assertions,
            &incomplete
        ));
    }
}

// Real-Lean toolchain discovery and skip accounting, shared with the other
// Lean-gated suites. Until this test existed, the golden pin above only
// asserted the rendered bytes matched a blessed hash -- never that a real Lean
// binary still accepts them. See `lean_probe.rs`'s module doc for the
// resolution policy (elan's toolchain directories are not on `PATH`).
#[path = "../../axeyum-lean-kernel/tests/support/lean_probe.rs"]
mod lean_probe;

/// **Real-Lean crosscheck**: the rendered small counterexample-cover module
/// must be accepted by a genuine `lean` binary (skips gracefully if none is
/// installed), and `#print axioms axeyum_refutation` must not depend on
/// `sorryAx`. This is the end-to-end kernel-checked payoff of ADR-0108 that
/// the byte pin alone cannot demonstrate.
#[test]
fn counterexample_cover_module_checks_in_real_lean() {
    let (mut arena, assertions) = small_cover_query();
    let certificate =
        quantified_counterexample_cover_refutation(&mut arena, &assertions, &config(5))
            .unwrap()
            .expect("one counterexample cube");
    let source = reconstruct_quantified_counterexample_cover_to_lean_module(
        &arena,
        &assertions,
        &certificate,
    )
    .expect("checked small cover should reconstruct");

    let Some(bin) = lean_probe::lean_bin_or_skip("counterexample-cover", 1) else {
        return;
    };
    let dir = std::env::temp_dir().join("axeyum_lean_counterexample_cover");
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("counterexample_cover.lean");
    std::fs::write(&file, &source).expect("write lean module");
    let out = Command::new(&bin).arg(&file).output().expect("run lean");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "lean REJECTED the counterexample-cover module\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}"
    );
    assert!(
        !stdout.contains("sorryAx"),
        "counterexample-cover proof depends on sorryAx:\n{stdout}"
    );
    assert!(
        stdout.contains("axeyum_refutation"),
        "missing #print axioms output:\n{stdout}"
    );
    eprintln!(
        "[lean ok] counterexample-cover: {}",
        stdout.trim().replace('\n', " | ")
    );
    lean_probe::report_checked("counterexample-cover", 1);
}
