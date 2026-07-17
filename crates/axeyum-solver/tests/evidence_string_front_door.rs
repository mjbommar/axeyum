//! Task #63 — P0 SOUNDNESS: `produce_evidence` returned WRONG verdicts with
//! `checked = true` on `QF_S`/`QF_SLIA` (the #62 dominance audit vs z3).
//!
//! Root cause: the arena front door [`produce_evidence`] takes `arena +
//! assertions`, but an unbounded string query cannot be faithfully represented
//! there — the term IR has no `str.in_re`/`str.replace` operators (they live only
//! in the bounded packed-BV encoding or the parser's word/membership side
//! channels), and a *word-only-fallback* script has an EMPTY flat assertion view,
//! so `produce_evidence(arena, &[])` trivially — and wrongly — reports `sat`.
//!
//! Fix: [`produce_evidence_smtlib`] is the string-capable text front door: it
//! delegates the decision to [`solve_smtlib`] (word / online CDCL(T) / membership
//! / length routes — Seq-level replay-checked `sat`, certified `unsat`) and wraps
//! the already-sound verdict. It NEVER fabricates a bounded model with
//! `checked = true`.
//!
//! These are the exact 7 instances the audit flagged (5 wrong-sat, 1 wrong-unsat,
//! 1 more wrong-sat), plus a negative test (an unsat-truth string query must not
//! yield a `checked = true` sat) and a non-string no-regression check.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::TermArena;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, produce_evidence, produce_evidence_smtlib, solve_smtlib,
};

fn cfg() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(30)),
        ..SolverConfig::default()
    }
}

fn corpus(rel: &str) -> String {
    let path = format!(
        "{}/../../corpus/public-curated/non-incremental/{rel}",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"))
}

fn evidence_verdict(ev: &Evidence) -> &'static str {
    match ev {
        Evidence::Unknown(_) => "unknown",
        Evidence::Sat(_) => "sat",
        _ => "unsat",
    }
}

fn solve_verdict(r: &CheckResult) -> &'static str {
    match r {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

/// The 7 audit-flagged instances: `produce_evidence_smtlib` must return the SAME
/// verdict as `solve_smtlib` + the declared `:status`, and must NEVER be a
/// `checked = true` sat on an unsat-truth query.
#[test]
fn string_front_door_matches_declared_status_on_audit_instances() {
    // (relative corpus path, declared status)
    let cases = [
        ("QF_S/cvc5-regress-clean/r1_QF_S_str002.smt2", "unsat"),
        (
            "QF_S/cvc5-regress-clean/r1_QF_S_instance1079-re-loop-cong.smt2",
            "unsat",
        ),
        (
            "QF_S/cvc5-regress-clean/r1_QF_S_instance3303-delta.smt2",
            "unsat",
        ),
        (
            "QF_S/cvc5-regress-clean/r0_QF_SLIA_norn-simp-rew.smt2",
            "unsat",
        ),
        (
            "QF_S/cvc5-regress-clean/r0_QF_SLIA_replace-find-base.smt2",
            "unsat",
        ),
        (
            "QF_SLIA/cvc5-regress-clean/cli__regress0__strings__replace-find-base.smt2",
            "unsat",
        ),
        (
            "QF_S/cvc5-regress-clean/r1_QF_SLIA_re-inter-stack-ovf.smt2",
            "sat",
        ),
    ];

    for (rel, want) in cases {
        let text = corpus(rel);

        // The text solver (correct) and the string evidence front door must agree
        // with each other and with the declared status.
        let solved = solve_smtlib(&text, &cfg())
            .unwrap_or_else(|e| panic!("[{rel}] solve_smtlib errored: {e:?}"));
        let report = produce_evidence_smtlib(&text, &cfg())
            .unwrap_or_else(|e| panic!("[{rel}] produce_evidence_smtlib errored: {e:?}"));

        assert_eq!(
            solve_verdict(&solved.result),
            want,
            "[{rel}] solve_smtlib disagrees with declared :status"
        );
        assert_eq!(
            evidence_verdict(&report.evidence),
            want,
            "[{rel}] produce_evidence_smtlib verdict != declared :status (P0 wrong verdict)"
        );

        // SOUNDNESS BAR: an unsat-truth string query must NEVER surface as a
        // `checked = true` sat (the exact failure class the audit caught).
        if want == "unsat" {
            assert!(
                !matches!(report.evidence, Evidence::Sat(_)),
                "[{rel}] produce_evidence_smtlib fabricated a sat on an UNSAT query"
            );
        }
    }
}

/// Negative test: a hand-written UNSAT word problem (each disjunct clashes) must
/// not yield a `checked = true` sat from the string evidence front door — it must
/// be decided `unsat`, and `Evidence::check` must not certify a spurious model.
#[test]
fn string_front_door_no_spurious_checked_sat_on_unsat_word_problem() {
    let text = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (or (= x (str.++ y "aa")) (= x (str.++ y "bb"))))
(assert (= x (str.++ y "cc")))
(check-sat)"#;

    let report = produce_evidence_smtlib(text, &cfg()).expect("produce_evidence_smtlib");
    assert!(
        !matches!(report.evidence, Evidence::Sat(_)),
        "spurious sat on an unsat word problem"
    );
    assert_eq!(evidence_verdict(&report.evidence), "unsat");

    // Whatever the evidence, re-validating it must not report a *satisfying model*
    // that does not exist: for the bare `unsat` verdict `check` returns true
    // (the verdict is trusted, no model claimed) but the evidence is NOT a `Sat`.
    let checked = report
        .evidence
        .check(&TermArena::new(), &[])
        .expect("check");
    assert!(checked, "unsat verdict must re-validate");
}

/// No-regression: a NON-string script routes through the ordinary arena
/// [`produce_evidence`] and yields the identical evidence (same verdict, same
/// `is_certified`), so every rich-certificate route is preserved.
#[test]
fn non_string_scripts_delegate_unchanged() {
    // QF_LIA unsat (integer infeasibility) — carries a Diophantine/Farkas cert.
    let lia = r"(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 2 x) (* 4 y)) 1))
(check-sat)";
    // QF_BV unsat — carries a DRAT proof.
    let bv = r"(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(assert (= a (bvadd a #x01)))
(check-sat)";
    // QF_BV sat — a replay-checked model.
    let bv_sat = r"(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(assert (= (bvand a #x0f) #x05))
(check-sat)";

    for text in [lia, bv, bv_sat] {
        let via_smtlib = produce_evidence_smtlib(text, &cfg()).expect("smtlib");

        let mut script = axeyum_smtlib::parse_script(text).expect("parse");
        let assertions = script.assertions.clone();
        let via_arena = produce_evidence(&mut script.arena, &assertions, &cfg()).expect("arena");

        assert_eq!(
            evidence_verdict(&via_smtlib.evidence),
            evidence_verdict(&via_arena.evidence),
            "verdict differs between front doors for a non-string script"
        );
        assert_eq!(
            via_smtlib.evidence.is_certified(),
            via_arena.evidence.is_certified(),
            "certification differs between front doors for a non-string script"
        );
        // The delegated report must independently re-validate.
        assert!(
            via_smtlib
                .evidence
                .check(&script.arena, &assertions)
                .expect("check"),
            "non-string evidence failed re-validation"
        );
    }
}
