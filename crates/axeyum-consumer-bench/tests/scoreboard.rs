//! Integration tests for the construction-known property scoreboard.
//!
//! The headline guarantee is **DISAGREE = 0**: no axeyum verdict may contradict a
//! property's construction-known status. These tests also pin the corpus shape
//! (a mix of provable and counterexample-bearing properties) and the verdict
//! contradiction logic.

use axeyum_consumer_bench::{Status, Verdict, corpus, render_scoreboard, run_corpus};

#[test]
fn corpus_has_a_real_mix() {
    let cases = corpus();
    assert!(
        cases.len() >= 12,
        "corpus should be substantial (>= 12 properties), got {}",
        cases.len()
    );
    let provable = cases
        .iter()
        .filter(|c| c.status == Status::ShouldProve)
        .count();
    let ce = cases
        .iter()
        .filter(|c| c.status == Status::ShouldFindCounterexample)
        .count();
    assert!(
        provable >= 4,
        "want several should-prove cases, got {provable}"
    );
    assert!(ce >= 4, "want several should-find-ce cases, got {ce}");
}

#[test]
fn corpus_names_are_unique() {
    let cases = corpus();
    let mut names: Vec<&str> = cases.iter().map(|c| c.name).collect();
    names.sort_unstable();
    let before = names.len();
    names.dedup();
    assert_eq!(before, names.len(), "corpus case names must be unique");
}

#[test]
fn disagree_is_zero_and_decisions_are_sound() {
    let cases = corpus();
    let (rows, agg) = run_corpus(&cases);

    // The hard soundness floor.
    assert_eq!(
        agg.disagree, 0,
        "soundness: an axeyum verdict contradicted a construction-known status"
    );

    // No individual row may be a contradiction either (defensive).
    for r in &rows {
        assert!(
            !r.is_disagreement(),
            "row `{}` contradicts its status {}: verdict {}",
            r.name,
            r.status,
            r.verdict.label()
        );
    }

    // Sanity: the totals are consistent.
    assert_eq!(agg.total, cases.len());
    assert_eq!(agg.proved + agg.counterexample + agg.unknown, agg.total);
}

#[test]
fn we_actually_prove_and_actually_refute_some_cases() {
    // Guard against a degenerate "everything Unknown" run that would trivially
    // satisfy DISAGREE = 0 without measuring anything.
    let cases = corpus();
    let (_rows, agg) = run_corpus(&cases);
    assert!(
        agg.proved > 0,
        "expected axeyum to prove at least one construction-known-true property"
    );
    assert!(
        agg.counterexample > 0,
        "expected axeyum to refute at least one construction-known-false property"
    );
}

#[test]
fn lean_cert_coverage_is_recorded() {
    // The differentiator: at least one Proved result should carry a verified Lean
    // module (the QF_BV / bit-identity fragment is reconstructable). This pins the
    // headline metric so a regression to zero coverage is caught.
    let cases = corpus();
    let (_rows, agg) = run_corpus(&cases);
    assert!(
        agg.lean_certified > 0,
        "expected nonzero Lean-cert coverage among the {} proved cases",
        agg.proved
    );
    // Coverage is a fraction in [0, 1].
    let cov = agg.lean_cert_coverage();
    assert!((0.0..=1.0).contains(&cov), "coverage out of range: {cov}");
}

#[test]
fn verdict_contradiction_logic() {
    // Proved-vs-CE mismatches are contradictions; Unknown never is.
    assert!(Verdict::Proved.contradicts(Status::ShouldFindCounterexample));
    assert!(Verdict::Counterexample.contradicts(Status::ShouldProve));
    assert!(!Verdict::Proved.contradicts(Status::ShouldProve));
    assert!(!Verdict::Counterexample.contradicts(Status::ShouldFindCounterexample));
    assert!(!Verdict::Unknown.contradicts(Status::ShouldProve));
    assert!(!Verdict::Unknown.contradicts(Status::ShouldFindCounterexample));

    assert!(Verdict::Proved.matches(Status::ShouldProve));
    assert!(Verdict::Counterexample.matches(Status::ShouldFindCounterexample));
    assert!(!Verdict::Unknown.matches(Status::ShouldProve));
}

#[test]
fn committed_render_is_deterministic() {
    let cases = corpus();
    let (rows, agg) = run_corpus(&cases);
    let a = render_scoreboard(&rows, &agg, false);
    let b = render_scoreboard(&rows, &agg, false);
    assert_eq!(a, b, "timing-free render must be byte-stable");
    assert!(a.contains("DISAGREE = 0"));
}
