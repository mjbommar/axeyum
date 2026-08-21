//! Shared test scaffolding.
//!
//! The fixture is REAL: two entries of this repository's fact ledger and a run
//! record produced by `render/tests/fixtures/make_run_record.py`, which performs
//! an actual check over actual files. Nothing here fabricates evidence; the
//! negative tests mutate COPIES in a scratch directory and never touch the
//! shared checkout.

#![allow(dead_code)]

use std::path::{Path, PathBuf};

use axeyum_render::assemble::{AssembleError, AssembleOptions, Assembler, ResolvedDocument};

pub const DOC_FILE: &str = "fixture-doc.json";
pub const RECORD_FILE: &str = "run-fact-ledger-check.json";

/// The package directory (`render/`).
pub fn package_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The repository root.
pub fn repo_root() -> PathBuf {
    package_root()
        .parent()
        .expect("render/ has a parent")
        .to_path_buf()
}

/// `render/tests/fixtures`.
pub fn fixtures_dir() -> PathBuf {
    package_root().join("tests/fixtures")
}

/// `render/tests/golden`.
pub fn golden_dir() -> PathBuf {
    package_root().join("tests/golden")
}

/// The fixture manifest as JSON, for tests that mutate a copy.
pub fn fixture_doc_json() -> serde_json::Value {
    let raw = std::fs::read(fixtures_dir().join(DOC_FILE)).expect("fixture doc readable");
    serde_json::from_slice(&raw).expect("fixture doc parses")
}

/// The fixture run record as JSON, for tests that mutate a copy.
pub fn fixture_record_json() -> serde_json::Value {
    let raw = std::fs::read(fixtures_dir().join(RECORD_FILE)).expect("fixture record readable");
    serde_json::from_slice(&raw).expect("fixture record parses")
}

/// Assemble the real fixture against the real ledger.
pub fn assemble_fixture() -> ResolvedDocument {
    assemble_fixture_maybe(false).expect("the committed fixture assembles")
}

/// Assemble the real fixture, returning the error if it refuses.
pub fn assemble_fixture_maybe(strict: bool) -> Result<ResolvedDocument, AssembleError> {
    let mut opts = AssembleOptions::new(repo_root(), fixtures_dir());
    opts.strict = strict;
    Assembler::new(opts).assemble_path(&fixtures_dir().join(DOC_FILE))
}

/// A clean scratch directory under `render/target`, named for the test.
///
/// The path is built from a compile-time literal plus the caller's name, never
/// from an environment variable, so an empty variable cannot make the cleanup
/// walk somewhere else.
pub fn scratch(name: &str) -> PathBuf {
    assert!(
        !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '-'),
        "scratch name must be a simple slug"
    );
    let dir = package_root().join("target/test-scratch").join(name);
    if dir.exists() {
        std::fs::remove_dir_all(&dir).expect("scratch removable");
    }
    std::fs::create_dir_all(&dir).expect("scratch creatable");
    dir
}

/// Write a mutated manifest and record into `dir` and assemble them against the
/// real repository root and fact ledger.
pub fn assemble_mutated(
    dir: &Path,
    doc: &serde_json::Value,
    record: &serde_json::Value,
    strict: bool,
) -> Result<ResolvedDocument, AssembleError> {
    write_json(&dir.join(DOC_FILE), doc);
    write_json(&dir.join(RECORD_FILE), record);
    let mut opts = AssembleOptions::new(repo_root(), dir.to_path_buf());
    opts.strict = strict;
    Assembler::new(opts).assemble_path(&dir.join(DOC_FILE))
}

/// Assemble the fixture against a SUBSTITUTE fact ledger, for tests about what
/// happens when a ledger entry is not what the reference asked for.
pub fn assemble_with_facts_dir(
    dir: &Path,
    facts_dir: &Path,
    doc: &serde_json::Value,
) -> Result<ResolvedDocument, AssembleError> {
    write_json(&dir.join(DOC_FILE), doc);
    std::fs::copy(fixtures_dir().join(RECORD_FILE), dir.join(RECORD_FILE))
        .expect("record copyable");
    let mut opts = AssembleOptions::new(repo_root(), dir.to_path_buf());
    opts.facts_dir = facts_dir.to_path_buf();
    Assembler::new(opts).assemble_path(&dir.join(DOC_FILE))
}

pub fn write_json(path: &Path, value: &serde_json::Value) {
    let text = serde_json::to_string_pretty(value).expect("serializable") + "\n";
    std::fs::write(path, text).expect("scratch writable");
}

/// The rendered status of the claim with this label.
pub fn claim_status(doc: &ResolvedDocument, label: &str) -> axeyum_render::ir::EvidenceStatus {
    doc.claims
        .iter()
        .find(|(l, _)| l == label)
        .map_or_else(|| panic!("no claim labelled `{label}`"), |(_, s)| *s)
}

/// Mutate the first claim block in place.
pub fn first_claim_mut(doc: &mut serde_json::Value) -> &mut serde_json::Value {
    doc["blocks"]
        .as_array_mut()
        .expect("blocks is an array")
        .iter_mut()
        .find(|b| b["kind"]["type"] == "claim")
        .expect("the fixture has a claim block")
}

/// Mutate the first statement block in place.
pub fn first_statement_mut(doc: &mut serde_json::Value) -> &mut serde_json::Value {
    doc["blocks"]
        .as_array_mut()
        .expect("blocks is an array")
        .iter_mut()
        .find(|b| b["kind"]["type"] == "statement")
        .expect("the fixture has a statement block")
}
