//! Rust <-> Python round-trip: the two implementations of the format must agree.
//!
//! `render/src/ir.rs` and `artifacts/ontology/docir.schema.json` are two
//! independent definitions of Doc-IR, and this file is the third party that
//! makes a disagreement visible:
//!
//! 1. Rust parses the fixture into its serde model and re-emits canonical JSON.
//! 2. `scripts/validate-docir.py` validates THAT output against the schema --
//!    so a field Rust silently dropped, renamed or invented fails here.
//! 3. The Python canonicalizer re-emits it, and the two byte strings must be
//!    equal -- so a difference in key order, number formatting or escaping
//!    fails here too.
//!
//! If `python3` is missing the tests FAIL rather than skip. A skipped
//! two-implementation check is a one-implementation check that looks like two.

mod common;

use std::path::Path;
use std::process::Command;

use axeyum_render::canonical_json;
use axeyum_render::ir::{Document, RunRecord};

fn python() -> Command {
    let mut c = Command::new("python3");
    c.current_dir(common::repo_root());
    c
}

fn validator() -> &'static str {
    "scripts/validate-docir.py"
}

fn run(args: &[&str]) -> (bool, String, String) {
    let out = python().args(args).output().unwrap_or_else(|e| {
        panic!(
            "python3 {args:?} could not run: {e}. \
             This test does not skip: a two-implementation check that silently \
             becomes a one-implementation check is worse than no check."
        )
    });
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

fn round_trip(name: &str, rust_canonical: &str, kind: &str) {
    let dir = common::scratch(name);
    let path = dir.join("canonical.json");
    std::fs::write(&path, rust_canonical).expect("scratch writable");
    let rel = relative(&path);

    let (ok, stdout, stderr) = run(&[validator(), "--kind", kind, "--require-jsonschema", &rel]);
    assert!(
        ok,
        "python validation of Rust output failed\nstdout: {stdout}\nstderr: {stderr}"
    );

    let (ok, python_canonical, stderr) = run(&[validator(), "--canonicalize", &rel]);
    assert!(ok, "python canonicalization failed: {stderr}");
    assert_eq!(
        python_canonical, rust_canonical,
        "Rust and Python disagree on the canonical form of {name}"
    );
}

fn relative(path: &Path) -> String {
    path.strip_prefix(common::repo_root())
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}

#[test]
fn document_round_trips_through_python() {
    let raw = std::fs::read(common::fixtures_dir().join(common::DOC_FILE)).expect("readable");
    let doc: Document = serde_json::from_slice(&raw).expect("the fixture parses into the IR");
    let canonical = canonical_json(&doc).expect("serializable");
    round_trip("schema-doc", &canonical, "document");
}

#[test]
fn run_record_round_trips_through_python() {
    let raw = std::fs::read(common::fixtures_dir().join(common::RECORD_FILE)).expect("readable");
    let rec: RunRecord = serde_json::from_slice(&raw).expect("the record parses into the IR");
    let canonical = canonical_json(&rec).expect("serializable");
    round_trip("schema-record", &canonical, "run-record");
}

/// The committed fixtures validate as they stand, not only after a Rust
/// round-trip -- otherwise Rust could be normalising away a schema violation.
#[test]
fn the_committed_fixtures_validate_against_the_schema() {
    let (ok, stdout, stderr) = run(&[
        validator(),
        "--require-jsonschema",
        "render/tests/fixtures/fixture-doc.json",
        "render/tests/fixtures/run-fact-ledger-check.json",
    ]);
    assert!(
        ok,
        "committed fixtures failed validation\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("2 file(s)"),
        "the validator must report what it checked: {stdout}"
    );
}

/// The validator must be able to FAIL, or it is a checker that cannot fail.
/// Two mutations, each hitting a different guard.
#[test]
fn the_python_validator_rejects_what_it_should() {
    let dir = common::scratch("schema-negative");

    let mut doc = common::fixture_doc_json();
    common::first_claim_mut(&mut doc)["kind"]["evidence"] = serde_json::json!([]);
    let no_evidence = dir.join("no-evidence.json");
    common::write_json(&no_evidence, &doc);
    let (ok, _, stderr) = run(&[validator(), &relative(&no_evidence)]);
    assert!(!ok, "a claim with no evidence must fail python validation");
    assert!(
        stderr.contains("carries no evidence"),
        "the reason is named: {stderr}"
    );

    let mut rec = common::fixture_record_json();
    rec["provenance"]["exit_status"] = serde_json::json!(1);
    let red = dir.join("red.json");
    common::write_json(&red, &rec);
    let (ok, _, stderr) = run(&[validator(), &relative(&red)]);
    assert!(
        !ok,
        "a failed run that still says `established` must fail validation"
    );
    assert!(
        stderr.contains("cannot also have found"),
        "the reason is named: {stderr}"
    );
}

/// A validator pointed at nothing must not report success -- the empty-check
/// trap this repository has shipped repeatedly.
#[test]
fn the_python_validator_refuses_to_pass_an_empty_check() {
    let (ok, _, stderr) = run(&[validator()]);
    assert!(!ok, "validating zero files must not exit 0");
    assert!(
        stderr.contains("empty check"),
        "the reason is named: {stderr}"
    );
}
