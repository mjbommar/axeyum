//! Re-check every committed creative-telescoping certificate **from the file**.
//!
//! This is what makes `artifacts/cas-certificates/*.json` evidence rather than
//! decoration: nothing here runs the search. Each file is read, parsed, and
//! handed to the independent checker, which re-derives the shift ratios from the
//! specification in the file and cross-checks them against exact bignum
//! factorials. If the artifacts and the checker ever disagree, this fails.
//!
//! Regenerate the files with
//! `cargo run -p axeyum-cas --example emit_telescoping_certificates`.
//!
//! The tamper block at the end is the load-bearing half: a certificate file that
//! has been edited must be **rejected**, or the artifact directory is a place to
//! keep wrong proofs.

use std::path::PathBuf;

use axeyum_cas::mvpoly::MvPoly;
use axeyum_cas::telescoping_check::{
    Verdict, check_certificate, check_closed_form, check_closed_form_symbolic,
};
use axeyum_cas::telescoping_json::{CertificateDocument, from_json, to_json};
use axeyum_ir::Rational;

/// The committed certificate directory.
fn directory() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../artifacts/cas-certificates")
}

/// Every committed certificate, parsed, in a deterministic order.
fn documents() -> Vec<(String, CertificateDocument)> {
    let mut paths: Vec<PathBuf> = std::fs::read_dir(directory())
        .expect("the certificate directory must exist")
        .map(|entry| entry.expect("readable directory entry").path())
        .filter(|path| path.extension().is_some_and(|kind| kind == "json"))
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            let name = path
                .file_name()
                .expect("a file name")
                .to_string_lossy()
                .into_owned();
            let text = std::fs::read_to_string(&path).expect("readable certificate");
            let document =
                from_json(&text).unwrap_or_else(|reason| panic!("{name} does not parse: {reason}"));
            (name, document)
        })
        .collect()
}

/// Run the checker over one document exactly as the file states it.
fn verify(name: &str, document: &CertificateDocument) {
    let verdict = check_certificate(&document.certificate, &document.options);
    assert!(
        verdict.is_verified(),
        "{name}: the independent checker rejected a committed certificate: {verdict:?}"
    );
    let Verdict::Verified(report) = verdict else {
        unreachable!("just asserted verified");
    };
    assert!(
        report.ratio_samples >= document.options.min_ratio_samples,
        "{name}: the ratio layer was not exercised"
    );
    assert!(
        report.recurrence_samples > 0,
        "{name}: no shift-variable sample confirmed the summed recurrence"
    );
    // The pointwise layer is the one a certificate pole silently skips, and it
    // is the one that ties `G` to `F`. Before this assertion existed, a file
    // whose window put every grid point on a pole confirmed the identity ZERO
    // times and was still `Verified`.
    assert!(
        report.pointwise_samples >= document.options.min_pointwise_samples,
        "{name}: the pointwise telescoping layer was not exercised to the floor \
         the file itself declares ({} confirmations, {} demanded, {} poles)",
        report.pointwise_samples,
        document.options.min_pointwise_samples,
        report.certificate_poles_in_window
    );
    assert!(
        document.options.min_pointwise_samples > 0,
        "{name}: a committed certificate must declare a positive pointwise floor"
    );

    if let Some(claim) = &document.closed_form {
        if claim.symbolic {
            let report = check_closed_form_symbolic(
                &document.certificate,
                &claim.term,
                claim.base,
                &document.options,
            )
            .unwrap_or_else(|reasons| panic!("{name}: symbolic closed form rejected: {reasons:?}"));
            assert!(report.base_cases > 0, "{name}: no symbolic base case ran");
            assert!(report.leading_zeros.is_empty());
        } else {
            let report = check_closed_form(
                &document.certificate,
                &claim.term,
                claim.base,
                &document.options,
            )
            .unwrap_or_else(|reasons| panic!("{name}: closed form rejected: {reasons:?}"));
            assert!(report.base_cases > 0, "{name}: no base case ran");
            assert!(report.leading_zeros.is_empty());
        }
    }
}

#[test]
fn every_committed_certificate_re_checks_from_the_file() {
    let all = documents();
    assert!(
        all.len() >= 7,
        "the certificate directory has shrunk to {} entries",
        all.len()
    );
    let mut with_closed_form = 0usize;
    let mut highest_order = 0usize;
    for (name, document) in &all {
        assert_eq!(
            format!("{}.json", document.id),
            *name,
            "a certificate's id must match its file name"
        );
        verify(name, document);
        if document.closed_form.is_some() {
            with_closed_form += 1;
        }
        highest_order = highest_order.max(document.certificate.order());
    }
    assert!(
        with_closed_form >= 5,
        "only {with_closed_form} certificate(s) carry a closed form"
    );
    assert!(
        highest_order >= 2,
        "no committed certificate exercises an order-2 recurrence"
    );
}

#[test]
fn the_committed_files_are_exactly_what_the_codec_writes() {
    // A committed file that does not round-trip means the emitter and the reader
    // have drifted apart, which would make a re-run of the emitter produce a
    // spurious diff and hide a real one.
    for (name, document) in documents() {
        let text = std::fs::read_to_string(directory().join(&name)).expect("readable");
        assert_eq!(
            to_json(&document),
            text,
            "{name} is not byte-identical to what the codec writes"
        );
    }
}

// ---------------------------------------------------------------------------
// Tamper control: an edited artifact must be rejected.
// ---------------------------------------------------------------------------

#[test]
fn a_tampered_certificate_file_is_rejected() {
    for (name, document) in documents() {
        // Perturb P by one, write it back out, read it back in: exactly what an
        // edited artifact would look like to the checker.
        let mut tampered = document.clone();
        tampered.certificate.certificate_numerator = tampered
            .certificate
            .certificate_numerator
            .add(&MvPoly::constant(Rational::integer(1)))
            .expect("no overflow");
        let round_tripped = from_json(&to_json(&tampered)).expect("the codec reads its own output");
        assert!(
            !check_certificate(&round_tripped.certificate, &round_tripped.options).is_verified(),
            "{name}: the checker ACCEPTED a certificate whose numerator was edited"
        );

        // Perturb the recurrence's leading coefficient.
        let mut tampered = document.clone();
        let last = tampered.certificate.recurrence.len() - 1;
        tampered.certificate.recurrence[last] = tampered.certificate.recurrence[last]
            .add(&MvPoly::constant(Rational::integer(1)))
            .expect("no overflow");
        let round_tripped = from_json(&to_json(&tampered)).expect("the codec reads its own output");
        assert!(
            !check_certificate(&round_tripped.certificate, &round_tripped.options).is_verified(),
            "{name}: the checker ACCEPTED a certificate whose recurrence was edited"
        );
    }
}

#[test]
fn a_certificate_re_pointed_at_another_summand_is_rejected() {
    let all = documents();
    // Give every certificate the *next* certificate's summand. All of these are
    // genuinely different sums, so every one of them must be refused.
    for index in 0..all.len() {
        let (name, document) = &all[index];
        let (other_name, other) = &all[(index + 1) % all.len()];
        if document.certificate.term == other.certificate.term {
            continue;
        }
        let mut swapped = document.clone();
        swapped.certificate.term = other.certificate.term.clone();
        assert!(
            !check_certificate(&swapped.certificate, &swapped.options).is_verified(),
            "{name}: the checker ACCEPTED its certificate re-pointed at {other_name}'s summand"
        );
    }
}

#[test]
fn a_corrupt_file_does_not_parse() {
    let (name, _) = &documents()[0];
    let text = std::fs::read_to_string(directory().join(name)).expect("readable");
    for (label, corrupt) in [
        ("truncated", text[..text.len() / 2].to_owned()),
        ("trailing garbage", format!("{text}}}")),
        (
            "wrong format tag",
            text.replace("axeyum-telescoping", "some-other"),
        ),
        (
            "decimal version",
            text.replacen("\"version\": 1", "\"version\": 1.5", 1),
        ),
        ("decimal coefficient", text.replacen(", 1]", ", 1.0]", 1)),
    ] {
        assert!(
            from_json(&corrupt).is_err(),
            "{name}: a {label} file parsed instead of being refused"
        );
    }
}

/// ADVERSARIAL. The pointwise floor is the ONLY thing separating accept from
/// reject here: the certificate, the grid, the window and every other demand
/// are byte-for-byte the committed ones, and the single changed field is the
/// number of pointwise confirmations required.
///
/// That is deliberate. A first attempt narrowed the window instead, and it was
/// not a valid fixture -- narrowing also starved the ratio layer, so the
/// rejection came from a different guard and proved nothing about this one.
///
/// The fixture certificate is the one with the largest measured pole count
/// (40 of 300 grid points), so it is the file on which pole-skipping -- the
/// mechanism that can drive the pointwise count down without any other layer
/// noticing -- is most active.
#[test]
fn a_pointwise_layer_below_its_declared_floor_is_rejected() {
    let all = documents();
    let (name, document) = all
        .iter()
        .find(|(name, _)| name == "chu-vandermonde-convolution.json")
        .expect("the fixture certificate must exist");

    let Verdict::Verified(honest) = check_certificate(&document.certificate, &document.options)
    else {
        panic!("{name}: the committed certificate must verify");
    };
    assert!(
        honest.certificate_poles_in_window > 0,
        "{name}: this fixture is chosen for its poles and has none"
    );

    let mut demanding = document.options.clone();
    demanding.min_pointwise_samples = honest.pointwise_samples + 1;
    match check_certificate(&document.certificate, &demanding) {
        Verdict::Verified(_) => panic!(
            "{name}: {} pointwise confirmations were accepted against a floor of {}",
            honest.pointwise_samples, demanding.min_pointwise_samples
        ),
        Verdict::Rejected(reasons) => {
            assert_eq!(
                reasons.len(),
                1,
                "{name}: only the pointwise floor may separate these two runs, got {reasons:?}"
            );
            assert!(
                reasons[0].contains("pointwise telescoping confirmation"),
                "{name}: rejected for the wrong reason: {reasons:?}"
            );
            assert!(
                reasons[0].contains("skipped as certificate poles"),
                "{name}: the refusal must say how many points the poles took: {reasons:?}"
            );
        }
    }
}

/// ADVERSARIAL. Options that demand nothing of the pointwise layer are refused
/// outright. This is the shape the checker had before the repair -- the layer
/// carried no demand at all -- so it must not be reachable by configuration.
#[test]
fn options_demanding_no_pointwise_confirmation_are_refused() {
    let all = documents();
    let (name, document) = all.first().expect("at least one committed certificate");

    assert!(
        check_certificate(&document.certificate, &document.options).is_verified(),
        "{name}: control must verify"
    );

    let mut undemanding = document.options.clone();
    undemanding.min_pointwise_samples = 0;
    match check_certificate(&document.certificate, &undemanding) {
        Verdict::Verified(_) => {
            panic!("{name}: a verification demanding no pointwise confirmation was accepted")
        }
        Verdict::Rejected(reasons) => assert!(
            reasons
                .iter()
                .any(|reason| reason.contains("demand no pointwise")),
            "{name}: rejected for the wrong reason: {reasons:?}"
        ),
    }
}

/// The `check` block must SAY what coverage the file was admitted under. A
/// certificate missing `min_pointwise_samples` is refused rather than given a
/// silent default, because a default would let a file be re-admitted under a
/// floor it never declared.
#[test]
fn a_certificate_without_a_declared_pointwise_floor_does_not_parse() {
    let (name, document) = documents()
        .into_iter()
        .next()
        .expect("at least one committed certificate");
    let text = to_json(&document);
    assert!(
        text.contains("\"min_pointwise_samples\""),
        "{name}: the emitted file must declare the pointwise floor"
    );
    let stripped = text.replace(
        &format!(
            ", \"min_pointwise_samples\": {}",
            document.options.min_pointwise_samples
        ),
        "",
    );
    assert_ne!(stripped, text, "the strip must actually remove the field");
    assert!(
        from_json(&stripped).is_err(),
        "{name}: a file with no declared pointwise floor must be refused"
    );
}
