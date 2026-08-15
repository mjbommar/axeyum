//! The committed SOS artifacts, checked from disk and pinned against the corpus.
//!
//! This suite answers three separate questions that are easy to conflate:
//!
//! 1. does every committed file parse and check? (the checker's job)
//! 2. does it parse back to exactly the corpus value it was emitted from? (so a
//!    hand-edit to a file is caught even if it happens to still check)
//! 3. does the checker reject the tampered fixtures? (the negative controls, in
//!    Rust as well as in the shell gate, so a broken shell gate is not the only
//!    thing standing between a false certificate and a green run)

use std::path::{Path, PathBuf};

use axeyum_cas::sos::{self, SosArtifact, corpus, json};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate lives two levels below the repository root")
        .to_path_buf()
}

fn read(relative: &str) -> String {
    let path = repo_root().join(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!("cannot read {}: {error}", path.display());
    })
}

#[test]
fn every_committed_artifact_parses_checks_and_matches_the_corpus() {
    let artifacts = corpus::all();
    assert_eq!(artifacts.len(), 3);
    for expected in &artifacts {
        let relative = format!("artifacts/sos-certificates/{}.json", expected.id());
        let parsed = json::from_json(&read(&relative))
            .unwrap_or_else(|message| panic!("{relative} did not parse: {message}"));
        assert_eq!(
            &parsed, expected,
            "{relative} differs from axeyum_cas::sos::corpus; re-emit it rather than hand-editing"
        );
        let report = sos::check(&parsed)
            .unwrap_or_else(|message| panic!("{relative} did not check: {message}"));
        assert!(
            !report.is_empty(),
            "{relative} discharged zero obligations, which is not a pass"
        );
    }
}

#[test]
fn the_obligation_counts_the_facts_pin_are_the_counts_this_checker_produces() {
    // These are the numbers `--expect-checks` carries in the fact ledger and in
    // scripts/check-sos-negative-controls.sh. Pinning them here means a change
    // in coverage shows up as a failing test rather than as a fact whose
    // checker quietly began asserting less.
    for (id, expected) in [
        ("damped-rotation-lyapunov", 8usize),
        ("energy-barrier-reachability", 6),
        ("motzkin-psd-not-sos", 5),
    ] {
        let artifact = corpus::by_id(id).expect("the artifact is in the corpus");
        let report = sos::check(&artifact).expect("it checks");
        assert_eq!(
            report.len(),
            expected,
            "{id} discharged {} obligations, the ledger pins {expected}",
            report.len()
        );
    }
}

#[test]
fn the_certified_decay_rate_and_overshoot_are_exact() {
    let artifact = corpus::by_id("damped-rotation-lyapunov").expect("in the corpus");
    let report = sos::check(&artifact).expect("it checks");
    let rate = report.rate.expect("a Lyapunov certificate reports a rate");
    assert_eq!((rate.numerator(), rate.denominator()), (1, 26));
}

#[test]
fn every_tampered_fixture_is_rejected() {
    let directory = repo_root().join("artifacts/instances/sos/negative-controls");
    let mut entries: Vec<PathBuf> = std::fs::read_dir(&directory)
        .unwrap_or_else(|error| panic!("cannot list {}: {error}", directory.display()))
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "json")
        })
        .collect();
    entries.sort();
    assert!(
        entries.len() >= 21,
        "only {} negative-control fixtures; a shrinking sweep is a weaker gate wearing the same \
         name",
        entries.len()
    );
    for path in &entries {
        let text = std::fs::read_to_string(path).expect("fixture readable");
        let outcome = json::from_json(&text).and_then(|artifact| sos::check(&artifact));
        assert!(
            outcome.is_err(),
            "{} was ACCEPTED; it is a committed FALSE certificate and must be rejected",
            path.display()
        );
    }
}

#[test]
fn the_moment_argument_needs_both_halves() {
    // The sharpest of the fixtures, asserted by name because it is the one a
    // checker that only ran the PSD test would accept: raising a single dual
    // value keeps the moment matrix positive semidefinite and flips the sign of
    // the functional on the form.
    let text = read("artifacts/instances/sos/negative-controls/motzkin-dual-nonneg-on-form.json");
    let artifact = json::from_json(&text).expect("the fixture is well formed; only its dual lies");
    let message = sos::check(&artifact).expect_err("it must be rejected");
    assert!(
        message.contains("strictly negative"),
        "expected the SIGN obligation to be the one that fails, got: {message}"
    );

    // And its sibling fails on the other half, so the two together show both
    // obligations are live.
    let text = read("artifacts/instances/sos/negative-controls/motzkin-dual-not-psd.json");
    let artifact = json::from_json(&text).expect("well formed");
    let message = sos::check(&artifact).expect_err("it must be rejected");
    assert!(
        message.contains("positive semidefinite"),
        "expected the PSD obligation to be the one that fails, got: {message}"
    );
}

#[test]
fn a_tampered_vector_field_breaks_a_certificate_that_never_mentions_a_derivative() {
    // The independence claim, asserted rather than described: no field of the
    // artifact carries V-dot, so the only way editing the dynamics can be
    // caught is if the checker recomputes it.
    for (fixture, obligation) in [
        (
            "artifacts/instances/sos/negative-controls/lyapunov-tampered-field.json",
            "v-dot-bounded-above",
        ),
        (
            "artifacts/instances/sos/negative-controls/barrier-tampered-field.json",
            "barrier-non-increasing-along-the-flow",
        ),
    ] {
        let artifact = json::from_json(&read(fixture)).expect("well formed");
        let message = sos::check(&artifact).expect_err("a tampered field must be rejected");
        assert!(
            message.contains(obligation),
            "{fixture}: expected `{obligation}` to fail, got: {message}"
        );
    }
}

#[test]
fn an_empty_set_does_not_satisfy_a_barrier_certificate() {
    for fixture in [
        "artifacts/instances/sos/negative-controls/barrier-initial-witness-outside.json",
        "artifacts/instances/sos/negative-controls/barrier-unsafe-witness-outside.json",
    ] {
        let artifact = json::from_json(&read(fixture)).expect("well formed");
        let message = sos::check(&artifact).expect_err("must be rejected");
        assert!(
            message.contains("may be empty"),
            "{fixture}: expected the non-vacuity obligation to fail, got: {message}"
        );
    }
}

#[test]
fn the_three_artifacts_answer_three_different_questions() {
    let artifacts = corpus::all();
    let mut kinds: Vec<&str> = artifacts.iter().map(SosArtifact::kind).collect();
    kinds.sort_unstable();
    assert_eq!(kinds, vec!["barrier", "lyapunov", "psd-not-sos"]);
}
