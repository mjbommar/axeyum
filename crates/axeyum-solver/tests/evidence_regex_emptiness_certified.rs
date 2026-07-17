//! Integration gate for **string regex derivative-emptiness `unsat` → a certified
//! [`Evidence::UnsatRegexEmptiness`]** through the string-capable text evidence door
//! (P3.7 / Gap-7 ledger coverage, task #58, following #52).
//!
//! Before #58, [`produce_evidence_smtlib`] recorded every string `unsat` as a
//! correct-but-bare [`Evidence::Unsat(None)`] — sound, but Lean-uncertified, so the
//! dominance audit credited these rows `lean_checked = false`. #58 threads the same
//! kernel-checked derivative-emptiness certificate #52 wires into the live route
//! (`membership_unsat_lean_module`) into a transferable, self-re-checking evidence
//! object: [`Evidence::UnsatRegexEmptiness`] carries the deciding
//! [`Membership`](axeyum_strings::Membership), and [`Evidence::check`] re-derives the
//! emptiness closure from it from first principles and re-runs the kernel — the stored
//! module string is never trusted.
//!
//! The soundness invariants under test:
//! - a regex-emptiness `unsat` becomes `is_certified() == true` **and** `check()`
//!   re-validates (kernel-checked, not string-trusted);
//! - a satisfiable membership is never fabricated into a certified `unsat`;
//! - the yet-uncertified string `unsat` classes (word clash) stay a correct
//!   `Evidence::Unsat(None)` — no false certification;
//! - non-string scripts still route through `produce_evidence` unchanged.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::TermArena;
use axeyum_solver::{Evidence, SolverConfig, produce_evidence_smtlib};

fn cfg() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

/// `x ∈ (ab)+ ∧ x ∈ (ba)+`: two disjoint non-nullable languages — the intersection is
/// empty. The membership route decides `unsat` behind a re-checked derivative-emptiness
/// certificate (see `regex_emptiness_lean_reconstruct.rs`).
const DISJOINT_PLUS_UNSAT: &str = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.+ (str.to_re "ab"))))
(assert (str.in_re x (re.+ (str.to_re "ba"))))
(check-sat)"#;

#[test]
fn regex_emptiness_unsat_is_a_certified_evidence_variant() {
    let report = produce_evidence_smtlib(DISJOINT_PLUS_UNSAT, &cfg())
        .expect("produce evidence for a regex-emptiness unsat");

    // (1) The correct verdict, now carried as the transferable certified variant.
    let Evidence::UnsatRegexEmptiness {
        ref lean_module, ..
    } = report.evidence
    else {
        panic!(
            "expected a certified regex-emptiness unsat, got {:?}",
            report.evidence.kind_label()
        );
    };
    assert_eq!(report.evidence.kind_label(), "unsat-regex-emptiness");
    assert!(
        report.evidence.is_certified(),
        "a kernel-checked regex-emptiness refutation is certified evidence"
    );

    // (2) The carried module is the kernel-checked reconstruction (#44/#52 shape).
    assert!(
        lean_module.contains("theorem") && lean_module.contains("axeyum_refutation"),
        "the variant carries the reconstructed kernel-checked Lean `False` module"
    );

    // (3) `check()` re-derives the certificate from the self-contained `Membership`
    // from first principles and re-runs the kernel — it does NOT trust the stored
    // module string, and ignores the (empty/bounded) arena view. It must re-validate.
    let arena = TermArena::new();
    assert!(
        report
            .evidence
            .check(&arena, &[])
            .expect("re-check the regex-emptiness certificate"),
        "the regex-emptiness certificate must re-derive + kernel-check on re-check"
    );
}

#[test]
fn satisfiable_membership_is_never_fabricated_into_a_certified_unsat() {
    // x ∈ (ab)* — satisfiable (ε, "ab", …); there is no emptiness certificate, so the
    // verdict must be `sat` and NEVER a certified (or bare) `unsat`.
    let sat = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(check-sat)"#;
    let report = produce_evidence_smtlib(sat, &cfg()).expect("produce evidence for sat membership");
    assert!(
        matches!(report.evidence, Evidence::Sat(_)),
        "a satisfiable membership must be `sat`, got {:?}",
        report.evidence.kind_label()
    );
    assert!(
        !matches!(report.evidence, Evidence::UnsatRegexEmptiness { .. }),
        "a satisfiable membership must never be a certified regex-emptiness unsat"
    );
}

#[test]
fn word_clash_unsat_is_a_certified_alethe_variant() {
    // A pure word clash `x = "a" ∧ x = "b"`: correctly `unsat`, and now carried as the
    // self-checking Alethe `Evidence::UnsatWordClash` (#58b) — its `check()` re-runs the
    // embedded Alethe refutation to the empty clause, arena-free. Never a fabricated
    // `sat`, never a wrong verdict.
    let word = r#"(set-logic QF_S)
(declare-const x String)
(assert (= x "a"))
(assert (= x "b"))
(check-sat)"#;
    let report = produce_evidence_smtlib(word, &cfg()).expect("produce evidence for word clash");
    assert!(
        matches!(report.evidence, Evidence::UnsatWordClash(_)),
        "a word-clash unsat is a certified Alethe word-clash refutation, got {:?}",
        report.evidence.kind_label()
    );
    assert_eq!(report.evidence.kind_label(), "unsat-word-clash");
    assert!(
        report.evidence.is_certified(),
        "a self-checking Alethe word-clash refutation is certified evidence"
    );
    // `check()` re-runs the Alethe replay (arena-free); a fresh empty arena suffices.
    let arena = TermArena::new();
    assert!(
        report
            .evidence
            .check(&arena, &[])
            .expect("re-check the word-clash certificate"),
        "the word-clash Alethe certificate must re-validate on re-check"
    );
}

#[test]
fn non_string_script_is_unaffected() {
    // A QF_LIA unsat routes through the flat `produce_evidence` path unchanged.
    let lia = r"(set-logic QF_LIA)
(declare-const a Int)
(assert (> a 5))
(assert (< a 3))
(check-sat)";
    let report = produce_evidence_smtlib(lia, &cfg()).expect("produce evidence for QF_LIA unsat");
    assert!(
        !matches!(report.evidence, Evidence::Sat(_) | Evidence::Unknown(_)),
        "a QF_LIA `a>5 ∧ a<3` is unsat, got {:?}",
        report.evidence.kind_label()
    );
    assert!(
        !matches!(report.evidence, Evidence::UnsatRegexEmptiness { .. }),
        "a non-string script never yields a regex-emptiness variant"
    );
}
