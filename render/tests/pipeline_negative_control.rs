//! Exit criterion 5 of `04-prototype-plan.md`: the negative control on the
//! PIPELINE itself, run against the real certificate corpus.
//!
//! THE CRITERION AS WRITTEN DOES NOT DESCRIBE THIS SYSTEM, and this file is
//! where that was adjudicated (see `15-integrate-diary.md` and the dated note
//! in `04-prototype-plan.md`). It says:
//!
//! > mutate one d(k) value in the run record -> the rendered table changes AND
//! > the claim whose bound it violates flips to red.
//!
//! Both halves cannot happen at once here, because two guards landed between
//! the criterion being written and the pipeline existing:
//!
//! 1. the document declares the run record's SHA-256 in its own provenance and
//!    assembly re-hashes it on every build, so editing a `d(k)` inside the
//!    record is REFUSED before anything renders (fail-closed law rule 4); and
//! 2. the table is `from_run` -- it holds a reference into the record rather
//!    than a copy of its rows -- so there is no second place the number could
//!    disagree with itself.
//!
//! The honest behaviour is therefore two behaviours, and both are tested here:
//!
//! * TAMPER with the record -> the build refuses. Nothing renders at all,
//!   which is strictly stronger than rendering it in red.
//! * RE-RUN a mutated producer, so the record is a genuine recording of a
//!   genuinely different computation -> the rendered table changes AND the
//!   claim that rests on it flips red, with no edit to the document.
//!
//! The second half uses `run-mutant-M1.json`: a real record from a real run of
//! `producers/mutants/noh_wt_certificate_emitrun_m1.rs`, the paper repository's
//! own `M1-weight-loses-the-parity-term.patch` applied verbatim. It exits 1,
//! its `outcome` is `refuted`, and its `d-table` row for k = 5 reads 0 where
//! the production record reads 1. Nothing in this file fabricates a number.

mod common;

use std::path::{Path, PathBuf};

use axeyum_render::assemble::{AssembleError, AssembleOptions, Assembler, ResolvedKind};
use axeyum_render::ir::EvidenceStatus;

const CERT_DIR: &str = "render/examples-input/cert";
const M1_ID: &str = "R:noh-wt-certificate-mutant-m1";

/// Copy the certificate corpus into a scratch root, preserving repo-relative
/// layout.
///
/// The layout matters: both the document and the run record declare their
/// inputs by repo-relative path, and assembly re-hashes them against
/// `repo_root`. Staging a faithful miniature repository is what makes a
/// tampered COPY visible to the same guard that would see a tampered original,
/// without writing to the shared checkout.
fn stage(name: &str) -> PathBuf {
    let root = common::scratch(name);
    for rel in [
        "render/examples-input/cert/certificate.doc.json",
        "render/examples-input/cert/run-certificate.json",
        "render/examples-input/cert/run-mutant-M1.json",
        "render/producers/build-certificate-manifest.py",
        "render/producers/noh_wt_certificate_emitrun.rs",
        "render/producers/mutants/noh_wt_certificate_emitrun_m1.rs",
    ] {
        let dst = root.join(rel);
        std::fs::create_dir_all(dst.parent().expect("has a parent")).expect("mkdir");
        std::fs::copy(common::repo_root().join(rel), &dst)
            .unwrap_or_else(|e| panic!("copy {rel}: {e}"));
    }
    root
}

fn assemble_staged(
    root: &Path,
) -> Result<axeyum_render::assemble::ResolvedDocument, AssembleError> {
    let manifest = root.join(CERT_DIR).join("certificate.doc.json");
    let opts = AssembleOptions::new(
        root.to_path_buf(),
        manifest.parent().expect("dir").to_path_buf(),
    );
    Assembler::new(opts).assemble_path(&manifest)
}

/// The `d(k)` cell of the row for this k, out of the resolved table block.
fn d_of(doc: &axeyum_render::assemble::ResolvedDocument, k: &str) -> String {
    for b in &doc.blocks {
        if let ResolvedKind::Table { columns, rows, .. } = &b.kind {
            let kcol = columns.iter().position(|c| c.key == "k");
            let dcol = columns.iter().position(|c| c.key == "d");
            if let (Some(ki), Some(di)) = (kcol, dcol)
                && let Some(row) = rows.iter().find(|r| r[ki] == k)
            {
                return row[di].clone();
            }
        }
    }
    panic!("no d(k) table row for k = {k}");
}

fn status_of(doc: &axeyum_render::assemble::ResolvedDocument, needle: &str) -> EvidenceStatus {
    doc.claims
        .iter()
        .find(|(l, _)| l.contains(needle))
        .map_or_else(
            || panic!("no claim mentioning `{needle}` in {:?}", doc.claims),
            |(_, s)| *s,
        )
}

/// The control. Without it, both tests below could pass over a corpus that
/// never assembled or a table that was never there.
#[test]
fn the_committed_certificate_assembles_and_reports_the_measured_slack() {
    let root = stage("cert-baseline");
    let doc = assemble_staged(&root).expect("the committed certificate assembles");
    assert_eq!(d_of(&doc, "5"), "1", "d(5) is 1 for the admissible weight");
    assert_eq!(status_of(&doc, "Theorem 3"), EvidenceStatus::Evidence);
    assert_eq!(status_of(&doc, "Theorem 4"), EvidenceStatus::Evidence);
}

/// Half one: tampering with the record is refused, not rendered.
#[test]
fn editing_a_measurement_inside_the_run_record_is_refused() {
    let root = stage("cert-tampered-record");
    let record_path = root.join(CERT_DIR).join("run-certificate.json");
    let mut record: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&record_path).expect("record readable"))
            .expect("record parses");

    // One cell of one row: d(5) := 0, the value the M1 mutant actually
    // produces. Everything else in the file is untouched.
    let rows = record["tables"]["d-table"]["rows"]
        .as_array_mut()
        .expect("d-table rows");
    let mut edited = 0;
    for row in rows.iter_mut() {
        if row[0] == serde_json::json!(5) {
            row[4] = serde_json::json!(0);
            edited += 1;
        }
    }
    assert_eq!(edited, 1, "exactly one row should carry k = 5");
    std::fs::write(
        &record_path,
        serde_json::to_string_pretty(&record).expect("serializable"),
    )
    .expect("scratch writable");

    let err = assemble_staged(&root).expect_err("a tampered record must refuse the build");
    assert!(
        matches!(err, AssembleError::HashMismatch { .. }),
        "expected a hash refusal, got: {err}"
    );
}

/// Half two: a record from a genuinely different RUN changes the table and
/// flips the claim, with the document untouched except for which record it
/// points at.
#[test]
fn a_record_from_a_mutated_run_changes_the_table_and_flips_the_claim() {
    let root = stage("cert-mutant-run");
    let manifest_path = root.join(CERT_DIR).join("certificate.doc.json");
    let mut doc: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&manifest_path).expect("manifest readable"))
            .expect("manifest parses");

    // Point the table and the admissibility claim at the mutant's record. This
    // is the ONLY edit: no number is written into the document, and the
    // claim's declared status stays exactly what it was.
    for b in doc["blocks"].as_array_mut().expect("blocks") {
        let is_theorem_3 = b["id"] == "claim-theorem-3";
        let kind = &mut b["kind"];
        if kind["type"] == "table" {
            kind["from_run"]["run_record"] = serde_json::json!("run-mutant-M1.json");
            kind["from_run"]["record_id"] = serde_json::json!(M1_ID);
        }
        if is_theorem_3 {
            let ev = &mut kind["evidence"][0];
            ev["run_record"] = serde_json::json!("run-mutant-M1.json");
            ev["record_id"] = serde_json::json!(M1_ID);
            // The M1 record declares `role: negative-control`, so the citation
            // must declare it too -- the pairing guard added in round 2. That
            // is not a workaround: it is the reason a page cannot quote a
            // mutant as support by accident.
            ev["role"] = serde_json::json!("negative-control");
        }
    }
    std::fs::write(
        &manifest_path,
        serde_json::to_string_pretty(&doc).expect("serializable"),
    )
    .expect("scratch writable");

    let resolved = assemble_staged(&root).expect("the mutant's record still assembles");

    assert_eq!(
        d_of(&resolved, "5"),
        "0",
        "the rendered table must carry the mutant's measurement, not the production one"
    );
    assert_eq!(
        status_of(&resolved, "Theorem 3"),
        EvidenceStatus::Refuted,
        "the claim whose bound the mutant violates must flip red"
    );
    // And the claim that does NOT rest on the violated bound must not move: a
    // renderer that turned the whole page red would be decorating, not
    // propagating.
    assert_eq!(
        status_of(&resolved, "Theorem 4"),
        EvidenceStatus::Evidence,
        "an unrelated claim must keep its status"
    );

    // Every emitter must say so, in its own bytes.
    for (format, needle) in [
        (
            "md",
            "**Claim -- Theorem 3 (the closed-form weight is admissible)** [REFUTED]",
        ),
        (
            "tex",
            "\\axclaim{Theorem 3 (the closed-form weight is admissible)}{REFUTED}",
        ),
    ] {
        let emitter = axeyum_render::emitter_for(format).expect("emitter exists");
        let bytes = emitter.emit(&resolved).primary;
        assert!(
            bytes.contains(needle),
            "{format} output does not carry `{needle}`"
        );
        assert!(
            bytes.contains(" 0 ") || bytes.contains("| 0 |") || bytes.contains("& 0 "),
            "{format} output does not carry the mutant's zero anywhere"
        );
    }
}
