//! Regenerate `artifacts/geometry-certificates/*.json` from the committed corpus.
//!
//! A file is written **only after** the independent checker
//! ([`axeyum_cas::geometry_check`]) has accepted the certificate the certifier
//! produced, and only when its bytes differ from what is already on disk — so a
//! regeneration that changes nothing leaves the tree clean.
//!
//! Run from the repository root:
//! `cargo run -p axeyum-cas --release --example emit_geometry_certificates`
//!
//! Trailing arguments restrict the run to the named corpus ids, which is how a
//! single theorem is re-timed without paying for the whole corpus.

use std::path::PathBuf;

use axeyum_cas::geometry_certify::{ProofOutcome, certify, geometry_limits};
use axeyum_cas::geometry_check::{CheckOptions, GeometryVerdict, check_certificate};
use axeyum_cas::geometry_corpus::corpus;
use axeyum_cas::geometry_json::to_json;

fn main() {
    let directory =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../artifacts/geometry-certificates");
    std::fs::create_dir_all(&directory).expect("the certificate directory must be creatable");

    let mut written = 0usize;
    let mut unchanged = 0usize;
    let mut failed = 0usize;

    let wanted: Vec<String> = std::env::args().skip(1).collect();
    for problem in corpus() {
        if !wanted.is_empty() && !wanted.contains(&problem.id) {
            continue;
        }
        let started = std::time::Instant::now();
        let outcome = certify(&problem, geometry_limits());
        let elapsed = started.elapsed();
        let certificate = match outcome {
            ProofOutcome::Certified(certificate) => *certificate,
            ProofOutcome::NotInSaturatedIdeal {
                conclusion_id,
                remainder,
            } => {
                println!(
                    "  FAILED   {:<38} conclusion `{conclusion_id}` has a {}-term remainder \
                     ({elapsed:.1?})",
                    problem.id,
                    remainder.term_count()
                );
                failed += 1;
                continue;
            }
            ProofOutcome::Declined(reason) => {
                println!("  DECLINED {:<38} {reason:?} ({elapsed:.1?})", problem.id);
                failed += 1;
                continue;
            }
        };

        match check_certificate(&certificate, &CheckOptions::default()) {
            GeometryVerdict::Verified(report) => {
                let text = to_json(&certificate);
                let path = directory.join(format!("{}.json", certificate.id));
                let same = std::fs::read_to_string(&path).is_ok_and(|old| old == text);
                if same {
                    unchanged += 1;
                } else {
                    std::fs::write(&path, &text).expect("the certificate must be writable");
                    written += 1;
                }
                println!(
                    "  ok       {:<38} conditions={:?} conclusions={} degenerate={} generic={} \
                     numeric={} ({elapsed:.1?}){}",
                    certificate.id,
                    report.conditions_used,
                    report.conclusions_checked,
                    report.degenerate_witnesses_checked,
                    report.generic_witnesses_checked,
                    report.numeric_points_checked,
                    if same { "" } else { "  [written]" }
                );
            }
            GeometryVerdict::Rejected(reason) => {
                println!("  REJECTED {:<38} {reason}", certificate.id);
                failed += 1;
            }
        }
    }

    println!("\n{written} written, {unchanged} unchanged, {failed} failed");
    if failed > 0 {
        std::process::exit(1);
    }
}
