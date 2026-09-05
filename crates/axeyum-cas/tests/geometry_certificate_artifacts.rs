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

use std::collections::BTreeMap;
use std::path::PathBuf;

use axeyum_cas::geometry_certify::{GeometryCertificate, evaluate_gaussian};
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
                    // At least one counterexample per used condition, not
                    // exactly one. This was `assert_eq!` until `simson-line`,
                    // which carries a FOURTH witness for a reason worth keeping:
                    // its three counterexamples live in `ℚ(i)` and refute the
                    // conditions over characteristic zero, while the fourth is
                    // rational and says the separate thing that over the REAL
                    // plane the theorem still needs a condition at all. Those are
                    // two different claims and the artifact should carry both.
                    //
                    // Relaxing to `>=` costs nothing, because the strong half of
                    // the old assertion is enforced by the checker rather than
                    // here: `check_certificate` rejects a certificate with a used
                    // condition that has no counterexample, and equally rejects a
                    // witness naming a condition the proof does not use. So an
                    // extra witness cannot be decorative -- it has to be a
                    // verified counterexample for a condition actually consumed.
                    assert!(
                        report.degenerate_witnesses_checked >= report.conditions_used.len(),
                        "{name}: fewer counterexamples ({}) than used conditions ({})",
                        report.degenerate_witnesses_checked,
                        report.conditions_used.len()
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
    saturated()
        .into_iter()
        .next()
        .expect("at least one certificate uses a non-degeneracy condition")
        .1
}

/// **Every** certificate that consumes a non-degeneracy condition, by name.
///
/// The controls below used to run against `first()` alone, which meant a newly
/// promoted theorem inherited the *claim* that its counterexample is load-bearing
/// without inheriting the test. `rhombus-diagonals-perpendicular` joined the
/// corpus on 2026-08-15 and would have been exactly that: a saturated certificate
/// whose degenerate witness nothing checked could be deleted from.
fn saturated() -> Vec<(String, GeometryCertificate)> {
    let all: Vec<(String, GeometryCertificate)> = documents()
        .into_iter()
        .filter(|(_, _, certificate)| !certificate.saturations.is_empty())
        .map(|(name, _, certificate)| (name, certificate))
        .collect();
    assert!(
        all.len() >= 2,
        "the saturation controls must cover every saturated certificate, and there should be \
         more than one by now; found {}",
        all.len()
    );
    all
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
    for (name, mut certificate) in saturated() {
        certificate.saturations[0].condition = MvPoly::var(&certificate.coordinates[0]);
        let reason = rejected(&certificate);
        assert!(reason.contains("generator"), "{name}: unexpected {reason}");
    }
}

/// Deleting the counterexample must break the certificate: this is the control
/// that stops a proof from silently assuming non-degeneracy. Run against **every**
/// saturated certificate, because that is the claim every one of them makes.
#[test]
fn removing_the_degenerate_counterexample_is_rejected() {
    for (name, mut certificate) in saturated() {
        certificate.degenerate_witnesses.clear();
        let reason = rejected(&certificate);
        assert!(
            reason.contains("no degenerate counterexample"),
            "{name}: unexpected {reason}"
        );
    }
}

/// A "counterexample" that does not actually falsify a conclusion is not one.
#[test]
fn a_counterexample_that_does_not_break_the_theorem_is_rejected() {
    for (_, mut certificate) in saturated() {
        let generic = certificate.generic_witnesses[0].assignment.clone();
        certificate.degenerate_witnesses[0].assignment = generic;
        // Substituting a rational configuration means substituting ALL of it. A
        // leftover imaginary part would leave the witness at some third point
        // that is neither the generic configuration nor the committed one, and
        // the rejection would then be evidence about nothing.
        certificate.degenerate_witnesses[0].imaginary.clear();
        let _ = rejected(&certificate);
    }
}

/// A `ℚ(i)` witness whose imaginary part is dropped stops being a counterexample,
/// and the checker must say so.
///
/// This is the control on the format extension itself. `simson-line`'s witnesses
/// are counterexamples *because* of their imaginary parts — the same real parts
/// alone are a perfectly ordinary configuration that satisfies the theorem — so a
/// checker that read the file and ignored the new field would accept a
/// certificate whose negative controls prove nothing. It would also look exactly
/// like a passing run.
#[test]
fn a_gaussian_counterexample_with_its_imaginary_part_dropped_is_rejected() {
    let mut covered = 0usize;
    for (name, mut certificate) in saturated() {
        let Some(slot) = certificate
            .degenerate_witnesses
            .iter()
            .position(axeyum_cas::geometry_certify::DegenerateWitness::is_gaussian)
        else {
            continue;
        };
        certificate.degenerate_witnesses[slot].imaginary.clear();
        let reason = rejected(&certificate);
        assert!(
            reason.contains("degenerate witness"),
            "{name}: unexpected {reason}"
        );
        covered += 1;
    }
    assert!(
        covered >= 1,
        "no committed certificate carries a Q(i) witness, so this control examined nothing -- \
         which is indistinguishable from passing"
    );
}

/// Exact rational configurations that sit **on** a degeneracy locus and yet do
/// **not** break the theorem — one usable set per coordinatisation in the corpus.
///
/// A control that only ever applies to some certificates degrades silently as the
/// corpus grows, which is exactly what happened before: the quadrilateral
/// configuration below was the only one, so a triangle theorem simply skipped the
/// hardest control in the suite. The table is keyed by nothing — each entry is
/// tried against each certificate and the ones whose coordinates it covers are
/// used — and the test asserts **full coverage** at the end, so the next
/// promotion cannot quietly opt out either.
fn on_locus_but_harmless() -> Vec<(&'static str, BTreeMap<String, Rational>)> {
    let at = |entries: &[(&str, i128, i128)]| -> BTreeMap<String, Rational> {
        entries
            .iter()
            .map(|(name, numerator, denominator)| {
                ((*name).to_string(), Rational::new(*numerator, *denominator))
            })
            .collect()
    };
    vec![
        // Collinear points, covering every theorem coordinatised in `a..d` and
        // `p`. `abd-not-collinear` and `abc-not-collinear` both genuinely fail,
        // and yet: the diagonals of the parallelogram (`AC` and `BD` share the
        // midpoint `(1,0)`) and of the rhombus (`AC·BD = (2,0)·(0,0) = 0`) behave,
        // and `P = (1,0)` lies on both medians *and* is the centroid, so
        // `3P = A + B + C` holds. The committed centroid counterexample is this
        // configuration with `P = (7,0)` instead.
        (
            "A=(0,0) B=(1,0) C=(2,0) D=P=(1,0), collinear and still true",
            at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 1, 1),
                ("by", 0, 1),
                ("cx", 2, 1),
                ("cy", 0, 1),
                ("dx", 1, 1),
                ("dy", 0, 1),
                ("px", 1, 1),
                ("py", 0, 1),
            ]),
        ),
        // `euler-line`, on the locus and harmless. A = B = (0,0), C = (1,0) is
        // collinear, so `abc-not-collinear` fails and the hypotheses stop pinning
        // the two centres: `|OA| = |OB|` is vacuous and both perpendicularity
        // conditions collapse to `hx = 0`. Choosing O = (1/2,0) and H = (0,0)
        // still satisfies every hypothesis, and O, G = (1/3,0) and H all lie on
        // the x-axis, so the conclusion holds. The committed counterexample is
        // this configuration with H = (0,1) instead — one coordinate apart, and
        // the difference between a counterexample and a bystander.
        (
            "A=B=(0,0) C=(1,0) O=(1/2,0) H=(0,0), degenerate but still collinear",
            at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 0, 1),
                ("by", 0, 1),
                ("cx", 1, 1),
                ("cy", 0, 1),
                ("ox", 1, 2),
                ("oy", 0, 1),
                ("hx", 0, 1),
                ("hy", 0, 1),
            ]),
        ),
        // `pappus-hexagon`, on the locus and harmless. Six points on the x-axis
        // with D = B and E = A: every incidence hypothesis is vacuous or forces
        // its point onto the x-axis, and `ae-meets-bd` fails outright. `X` is the
        // one free point (both of its lines are vacuous), and putting it back on
        // the x-axis at (0,0) leaves X, Y, Z collinear, so the conclusion holds.
        // The committed counterexample is this configuration with X = (0,1)
        // instead — again one coordinate apart.
        (
            "six points on the x-axis with X back on it, degenerate but still collinear",
            at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 1, 1),
                ("by", 0, 1),
                ("cx", 3, 1),
                ("cy", 0, 1),
                ("dx", 1, 1),
                ("dy", 0, 1),
                ("ex", 0, 1),
                ("ey", 0, 1),
                ("fx", 5, 1),
                ("fy", 0, 1),
                ("xx", 0, 1),
                ("xy", 0, 1),
                ("yx", 2, 1),
                ("yy", 0, 1),
                ("zx", 4, 1),
                ("zy", 0, 1),
            ]),
        ),
        // `simson-line`, on the locus and harmless -- and this one is on the
        // locus of ALL THREE conditions at once, which is the only way to be on
        // this certificate's locus at a rational point. A = B = C = (0,0)
        // collapses every side line, so all six foot hypotheses are vacuous and
        // the concyclicity determinant has three equal rows; putting the three
        // feet back on the x-axis leaves them collinear, so the conclusion holds.
        // The committed counterexample is this configuration with X = (0,1)
        // instead -- one coordinate apart, as with the two above.
        (
            "A=B=C=(0,0) with the three feet back on the x-axis, degenerate but still collinear",
            at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("bx", 0, 1),
                ("by", 0, 1),
                ("cx", 0, 1),
                ("cy", 0, 1),
                ("px", 1, 1),
                ("py", 0, 1),
                ("xx", 0, 1),
                ("xy", 0, 1),
                ("yx", 2, 1),
                ("yy", 0, 1),
                ("zx", 4, 1),
                ("zy", 0, 1),
            ]),
        ),
        // `tetrahedron-medians-concurrent`, on the locus and harmless. A=(0,0,0),
        // B=(4,0,0), C=(0,4,0), D=(2,2,0) all have z=0, so `abcd-not-coplanar`
        // genuinely fails -- and yet the medians from A and B still meet only at
        // the true centroid (3/2,3/2,0), so 4P = A+B+C+D holds. The committed
        // counterexample is instead A=(1,1,0), B=(0,0,0), C=(3,0,0), D=(0,3,0),
        // P=(5,5,0): there A is exactly the centroid of B,C,D, so the median from
        // A degenerates to every point being "on" it, and P is free to be
        // anything on the median from B -- which is where this configuration
        // differs and is why it is harmless while that one is not.
        (
            "A=(0,0,0) B=(4,0,0) C=(0,4,0) D=(2,2,0), coplanar but still the true centroid",
            at(&[
                ("ax", 0, 1),
                ("ay", 0, 1),
                ("az", 0, 1),
                ("bx", 4, 1),
                ("by", 0, 1),
                ("bz", 0, 1),
                ("cx", 0, 1),
                ("cy", 4, 1),
                ("cz", 0, 1),
                ("dx", 2, 1),
                ("dy", 2, 1),
                ("dz", 0, 1),
                ("px", 3, 2),
                ("py", 3, 2),
                ("pz", 0, 1),
            ]),
        ),
    ]
}

/// The sharper form of `a_counterexample_that_does_not_break_the_theorem_is_rejected`,
/// and the one that is actually hard to pass: a configuration that **does**
/// violate the non-degeneracy condition and yet does **not** break the theorem.
///
/// The substitution used by that test is a *generic* configuration, which fails on
/// two counts at once — it satisfies the conclusion and it does not annihilate the
/// condition — so a checker that only tested the second would pass it. Sitting on
/// the degeneracy locus is not enough; a counterexample has to falsify something.
#[test]
fn a_counterexample_on_the_locus_that_falsifies_nothing_is_rejected() {
    let candidates = on_locus_but_harmless();
    let mut covered = 0usize;
    let saturated = saturated();
    let total = saturated.len();
    for (name, certificate) in saturated {
        let mut used = false;
        for (description, configuration) in &candidates {
            if certificate
                .coordinates
                .iter()
                .any(|coordinate| !configuration.contains_key(coordinate))
            {
                continue;
            }
            assert!(
                certificate.saturations.iter().all(|saturation| saturation
                    .condition
                    .evaluate(configuration)
                    .expect("assigned")
                    .is_zero()),
                "{name}: `{description}` must actually violate the condition, or this control \
                 is testing nothing"
            );
            assert!(
                certificate.conclusions.iter().all(|conclusion| conclusion
                    .poly
                    .evaluate(configuration)
                    .expect("assigned")
                    .is_zero()),
                "{name}: `{description}` must NOT break the theorem, or it would be a legitimate \
                 counterexample and this control would be backwards"
            );
            assert!(
                certificate.hypotheses.iter().all(|hypothesis| hypothesis
                    .poly
                    .evaluate(configuration)
                    .expect("assigned")
                    .is_zero()),
                "{name}: `{description}` must satisfy every hypothesis, or the checker would \
                 reject it for the wrong reason"
            );
            let mut tampered = certificate.clone();
            tampered.degenerate_witnesses[0].assignment = configuration.clone();
            tampered.degenerate_witnesses[0].imaginary.clear();
            let _ = rejected(&tampered);
            used = true;
            covered += 1;
            break;
        }
        assert!(
            used,
            "{name}: no on-locus-but-harmless configuration covers this certificate's \
             coordinates. Add one to `on_locus_but_harmless` -- skipping is how this control \
             quietly stopped applying to a newly promoted theorem once already."
        );
    }
    assert_eq!(
        covered, total,
        "every saturated certificate must be covered by this control"
    );
    assert!(
        covered >= 3,
        "this control examined only {covered} certificates"
    );
}

/// The condition set of every committed certificate is minimal **absolutely**,
/// and the artifact carries the proof.
///
/// ADR-0455 draws the distinction: a minimal-subset claim is absolute only if
/// every subset test was *decided*, and budget-relative otherwise. For the
/// Gröbner route "decided" means a reduction that returned a verdict, which is a
/// statement about a budget. Here it means something stronger and cheaper.
///
/// If a conclusion `c` lay in the ideal generated by the hypotheses together with
/// `d·z − 1` for each condition `d` in a subset `S`, then `c` would vanish at
/// every common zero of those generators. So a single configuration that
///
/// - satisfies every hypothesis,
/// - keeps every condition in `S` nonzero (so `z := 1/d` extends it to a zero of
///   the Rabinowitsch generators), and
/// - **falsifies** a conclusion
///
/// refutes `S` outright, with no budget, no monomial order and no algorithm in
/// the argument. That configuration is exactly the degenerate counterexample the
/// checker already replays — so for every certificate using a single condition,
/// its own negative control is the proof that the condition is required.
///
/// This test says so as an assertion rather than in prose, and it is stated for
/// arbitrary subsets so it keeps its force when a theorem needs two.
#[test]
fn every_used_condition_set_is_minimal_absolutely() {
    let mut checked = 0usize;
    let mut expected = 0usize;
    for (name, certificate) in saturated() {
        let conditions = certificate.saturations.len();
        expected += (1usize << conditions) - 1;
        assert!(
            conditions <= 8,
            "{name}: {conditions} conditions is too many to enumerate the proper subsets of"
        );
        // Every PROPER subset must be refuted by some committed counterexample.
        for mask in 0u32..(1u32 << conditions) {
            if mask == (1u32 << conditions) - 1 {
                continue; // the full set is what the certificate proves
            }
            let subset: Vec<usize> = (0..conditions)
                .filter(|index| mask & (1 << index) != 0)
                .collect();
            let refuted = certificate.degenerate_witnesses.iter().any(|witness| {
                // Over `ℚ(i)`, because the identity a certificate carries has
                // rational coefficients and is therefore a theorem of every field
                // of characteristic zero. A refutation only has to live in one of
                // them to be a refutation. `simson-line` is the case that needs
                // this: over `ℝ` no configuration isolates one of its three
                // conditions, and over `ℚ(i)` each of them has one.
                let Some(point) = witness.point() else {
                    return false;
                };
                let hypotheses_hold = certificate.hypotheses.iter().all(|hypothesis| {
                    matches!(evaluate_gaussian(&hypothesis.poly, &point), Some(value) if value.is_zero())
                });
                let subset_survives = subset.iter().all(|&index| {
                    matches!(
                        evaluate_gaussian(&certificate.saturations[index].condition, &point),
                        Some(value) if !value.is_zero()
                    )
                });
                let broken = certificate.conclusions.iter().any(|conclusion| {
                    matches!(evaluate_gaussian(&conclusion.poly, &point), Some(value) if !value.is_zero())
                });
                hypotheses_hold && subset_survives && broken
            });
            let named: Vec<&str> = subset
                .iter()
                .map(|&index| certificate.saturations[index].condition_id.as_str())
                .collect();
            assert!(
                refuted,
                "{name}: no committed configuration refutes the condition subset {named:?}, so \
                 the minimality of this certificate's condition set is only budget-relative and \
                 the fact must say so (ADR-0455)"
            );
            checked += 1;
        }
    }
    // The count is derived from the certificates rather than written down. A
    // hand-written total is how a gate stops measuring what it claims to: the
    // first version of this lane's diary said "6 proper subsets" against four
    // one-condition certificates, which is 4.
    assert_eq!(
        checked, expected,
        "the enumeration must visit every proper subset of every saturated certificate"
    );
    assert!(
        checked >= 3,
        "this test examined {checked} subsets; every saturated certificate has at least one \
         proper subset to refute"
    );
}

/// A saturation the proof never used would advertise a weaker theorem than the
/// one proved.
#[test]
fn an_unused_saturation_is_rejected() {
    for (_, mut certificate) in saturated() {
        let index = certificate.hypotheses.len();
        for conclusion in &mut certificate.conclusions {
            conclusion.cofactors[index] = MvPoly::zero();
        }
        let _ = rejected(&certificate);
    }
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
