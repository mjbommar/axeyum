//! Re-check every committed geometry cofactor certificate **from the file**.
//!
//! Nothing here runs the certifier: each file is read, parsed, and handed to the
//! independent checker, which rebuilds the saturation generators, expands the
//! cofactor identity, re-evaluates it numerically, and replays every degenerate
//! and generic configuration. If the artifacts and the checker ever disagree,
//! this fails.
//!
//! Regenerate the files with
//! `cargo run -p axeyum-cas --release --example emit_geometry_certificates`.
//!
//! The tamper block at the end is the load-bearing half. A certificate directory
//! that accepts an edited file is a place to keep wrong proofs, and in this
//! domain the specific wrong proof to fear is one whose non-degeneracy conditions
//! have been quietly weakened — so the controls include *deleting a
//! counterexample* and *replacing a counterexample with a configuration that does
//! not actually break the theorem*, not only arithmetic edits.

use std::path::PathBuf;

use axeyum_cas::geometry_certify::GeometryCertificate;
use axeyum_cas::geometry_check::{CheckOptions, GeometryVerdict, check_certificate};
use axeyum_cas::geometry_json::{from_json, to_json};
use axeyum_cas::mvpoly::MvPoly;
use axeyum_ir::Rational;

fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../artifacts/geometry-certificates")
}

fn documents() -> Vec<(String, String, GeometryCertificate)> {
    let mut paths: Vec<PathBuf> = std::fs::read_dir(directory())
        .expect("the geometry certificate directory must exist")
        .map(|entry| entry.expect("readable directory entry").path())
        .filter(|path| path.extension().is_some_and(|kind| kind == "json"))
        .collect();
    paths.sort();
    assert!(
        !paths.is_empty(),
        "the geometry certificate directory is empty; this suite would examine nothing"
    );
    paths
        .into_iter()
        .map(|path| {
            let name = path
                .file_name()
                .expect("a file name")
                .to_string_lossy()
                .into_owned();
            let text = std::fs::read_to_string(&path).expect("readable certificate");
            let certificate =
                from_json(&text).unwrap_or_else(|reason| panic!("{name} does not parse: {reason}"));
            (name, text, certificate)
        })
        .collect()
}

/// Every committed certificate re-derives.
#[test]
fn every_committed_geometry_certificate_re_derives() {
    let mut checked = 0usize;
    let mut with_conditions = 0usize;
    let mut without_conditions = 0usize;
    for (name, _, certificate) in documents() {
        assert_eq!(
            name,
            format!("{}.json", certificate.id),
            "a certificate's file name must be its id"
        );
        match check_certificate(&certificate, &CheckOptions::default()) {
            GeometryVerdict::Verified(report) => {
                assert!(
                    report.conclusions_checked > 0,
                    "{name}: no conclusion was checked"
                );
                assert!(
                    report.numeric_points_checked > 0,
                    "{name}: the numeric cross-check evaluated nothing"
                );
                assert!(
                    report.generic_witnesses_checked > 0,
                    "{name}: no non-degenerate configuration was replayed"
                );
                if report.conditions_used.is_empty() {
                    without_conditions += 1;
                } else {
                    with_conditions += 1;
                    assert_eq!(
                        report.degenerate_witnesses_checked,
                        report.conditions_used.len(),
                        "{name}: one counterexample per used condition, exactly"
                    );
                }
                checked += 1;
            }
            GeometryVerdict::Rejected(reason) => {
                panic!("{name}: the independent checker rejected a committed certificate: {reason}")
            }
        }
    }
    assert!(checked >= 5, "the corpus must exercise several theorems");
    assert!(
        with_conditions > 0,
        "the corpus must contain a theorem that genuinely needs a non-degeneracy condition, or \
         the saturation route is untested"
    );
    assert!(
        without_conditions > 0,
        "the corpus must contain a theorem that needs NO condition, or the claim that this \
         distinction is measured rather than assumed is untested"
    );
}

/// A committed file that does not round-trip means the emitter and the reader
/// have drifted, which would make a regeneration produce a spurious diff and hide
/// a real one.
#[test]
fn every_committed_geometry_certificate_round_trips_byte_for_byte() {
    for (name, text, certificate) in documents() {
        assert_eq!(
            to_json(&certificate),
            text,
            "{name} does not round-trip; regenerate the artifacts"
        );
    }
}

fn first() -> GeometryCertificate {
    documents()
        .into_iter()
        .find(|(_, _, certificate)| !certificate.saturations.is_empty())
        .expect("at least one certificate uses a non-degeneracy condition")
        .2
}

fn rejected(certificate: &GeometryCertificate) -> String {
    match check_certificate(certificate, &CheckOptions::default()) {
        GeometryVerdict::Verified(_) => panic!("a tampered certificate was accepted"),
        GeometryVerdict::Rejected(reason) => reason,
    }
}

#[test]
fn a_cofactor_edited_by_one_is_rejected() {
    let mut certificate = first();
    let cofactors = &mut certificate.conclusions[0].cofactors;
    cofactors[0] = cofactors[0]
        .add(&MvPoly::constant(Rational::integer(1)))
        .expect("perturbation");
    let _ = rejected(&certificate);
}

#[test]
fn a_conclusion_edited_by_one_is_rejected() {
    let mut certificate = first();
    certificate.conclusions[0].poly = certificate.conclusions[0]
        .poly
        .add(&MvPoly::constant(Rational::integer(1)))
        .expect("perturbation");
    let _ = rejected(&certificate);
}

/// The condition in the file must be the condition the proof saturated by, or a
/// certificate could advertise a weak side condition and use a strong one.
#[test]
fn a_swapped_non_degeneracy_condition_is_rejected() {
    let mut certificate = first();
    certificate.saturations[0].condition = MvPoly::var(&certificate.coordinates[0]);
    let reason = rejected(&certificate);
    assert!(reason.contains("generator"), "unexpected reason: {reason}");
}

/// Deleting the counterexample must break the certificate: this is the control
/// that stops a proof from silently assuming non-degeneracy.
#[test]
fn removing_the_degenerate_counterexample_is_rejected() {
    let mut certificate = first();
    certificate.degenerate_witnesses.clear();
    let reason = rejected(&certificate);
    assert!(
        reason.contains("no degenerate counterexample"),
        "unexpected reason: {reason}"
    );
}

/// A "counterexample" that does not actually falsify a conclusion is not one.
#[test]
fn a_counterexample_that_does_not_break_the_theorem_is_rejected() {
    let mut certificate = first();
    let generic = certificate.generic_witnesses[0].assignment.clone();
    certificate.degenerate_witnesses[0].assignment = generic;
    let _ = rejected(&certificate);
}

/// A saturation the proof never used would advertise a weaker theorem than the
/// one proved.
#[test]
fn an_unused_saturation_is_rejected() {
    let mut certificate = first();
    let index = certificate.hypotheses.len();
    for conclusion in &mut certificate.conclusions {
        conclusion.cofactors[index] = MvPoly::zero();
    }
    let _ = rejected(&certificate);
}

/// One certificate's cofactors against another's generators must not verify.
#[test]
fn cofactors_from_a_neighbouring_certificate_are_rejected() {
    let all = documents();
    let mut victim = all[0].2.clone();
    let donor = all
        .iter()
        .find(|(_, _, other)| {
            other.id != victim.id
                && other.generators.len() == victim.generators.len()
                && !other.conclusions.is_empty()
        })
        .map(|(_, _, other)| other.clone());
    let Some(donor) = donor else {
        return; // no same-shape neighbour to swap with; the other controls cover it
    };
    victim.conclusions[0].cofactors = donor.conclusions[0].cofactors.clone();
    let _ = rejected(&victim);
}

#[test]
fn the_reader_refuses_malformed_files() {
    let (_, text, _) = documents().into_iter().next().expect("a certificate");
    assert!(
        from_json(&text[..text.len() / 2]).is_err(),
        "a truncated file must be refused"
    );
    assert!(
        from_json(&text.replace("axeyum-geometry-certificate", "some-other-format")).is_err(),
        "a foreign format tag must be refused"
    );
    let decimal = text.replacen("\"coefficient\": [", "\"coefficient\": [1.5, ", 1);
    assert!(
        from_json(&decimal).is_err(),
        "a decimal where an exact integer belongs must be refused"
    );
    assert!(
        from_json("{\"format\": \"axeyum-geometry-certificate\", \"version\": 1}").is_err(),
        "a document missing its content must be refused"
    );
}
