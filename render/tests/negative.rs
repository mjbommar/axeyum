//! The fail-closed law, one test per rule, each tied to a named guard.
//!
//! Delete-one-guard discipline (CLAUDE.md; 03-architecture.md's testing
//! section). These are MEASURED results, not intentions: each guard below was
//! deleted in turn on 2026-08-21 and the whole suite was re-run with
//! `--no-fail-fast` (without that flag cargo stops after the first failing
//! binary and the counts are wrong -- the first pass of this exercise reported
//! three of these numbers too low for exactly that reason).
//!
//! | guard deleted (`src/assemble.rs`) | tests that died |
//! |---|---|
//! | `evidence.is_empty()` in `resolve_claim` | 1 -- `claim_without_evidence_is_a_build_error` |
//! | `map_err(|_| DanglingFactRef)` on the ledger read | **0** -- see below |
//! | `fact.id != *id` in `resolve_formal_ref` | 1 -- `a_fact_file_whose_id_disagrees_with_the_reference_is_a_build_error` |
//! | BOTH dangling-ref guards together | 2 -- and that is the property test |
//! | `actual != input.sha256` in `verify_inputs` | 2 -- `input_hash_mismatch_is_a_build_error`, `stale_mtimes_cannot_produce_a_stale_render` |
//! | `e.exit_status != 0` in `rendered_status` | 2 -- the unit test and `nonzero_exit_status_demotes_the_claim` |
//! | the `strict` block in `resolve_claim` | 1 -- `nonzero_exit_status_is_an_error_in_strict_mode` |
//!
//! THE ZERO IS THE INTERESTING ROW and it is left in rather than tidied away.
//! Deleting the missing-file arm alone kills nothing, because removing that
//! refusal means inventing ledger content in its place, and any invented
//! content fails the id comparison. So rule 3 is carried by the id comparison;
//! the missing-file arm only improves the error message. Deleting both kills
//! two tests, which is what makes the property -- not either guard -- tested.
//! The rows that killed two tests are two levels of the same property (unit and
//! integration), not two properties sharing one check.
//!
//! Every mutation happens on a COPY in `render/target/test-scratch`; the shared
//! checkout is never written to.

mod common;

use axeyum_render::assemble::AssembleError;
use axeyum_render::ir::EvidenceStatus;
use common::{
    assemble_mutated, first_claim_mut, first_statement_mut, fixture_doc_json, fixture_record_json,
    scratch,
};

/// Control: the committed fixture assembles. Without this, a mutation test that
/// passed for the wrong reason (a fixture that never assembled at all) would be
/// indistinguishable from one that passed for the right one.
#[test]
fn the_committed_fixture_assembles_and_every_claim_is_checked() {
    let doc = common::assemble_fixture();
    assert_eq!(doc.claims.len(), 3, "the fixture makes three claims");
    for (label, status) in &doc.claims {
        assert_eq!(
            *status,
            EvidenceStatus::Checked,
            "claim `{label}` should render CHECKED"
        );
    }
}

/// Rule 1: a claim with no evidence is a build error, not a warning.
#[test]
fn claim_without_evidence_is_a_build_error() {
    let dir = scratch("claim-without-evidence");
    let mut doc = fixture_doc_json();
    first_claim_mut(&mut doc)["kind"]["evidence"] = serde_json::json!([]);

    let err = assemble_mutated(&dir, &doc, &fixture_record_json(), false)
        .expect_err("a claim with no evidence must refuse to render");
    match err {
        AssembleError::ClaimWithoutEvidence { block, label } => {
            assert_eq!(block, "claim-bool-and-comm");
            assert!(
                label.contains("bool-and-comm"),
                "error names the claim: {label}"
            );
        }
        other => panic!("expected ClaimWithoutEvidence, got {other}"),
    }
}

/// Rule 3: a fact id that resolves to nothing is a build error -- the renderer
/// must not fall back to a plausible-looking statement.
#[test]
fn dangling_fact_ref_is_a_build_error() {
    let dir = scratch("dangling-fact-ref");
    let mut doc = fixture_doc_json();
    first_statement_mut(&mut doc)["kind"]["ref"]["id"] =
        serde_json::json!("F:no-such-fact-exists-here");

    let err = assemble_mutated(&dir, &doc, &fixture_record_json(), false)
        .expect_err("a dangling fact reference must refuse to render");
    match err {
        AssembleError::DanglingFactRef { id, .. } => {
            assert_eq!(id, "F:no-such-fact-exists-here");
        }
        other => panic!("expected DanglingFactRef, got {other}"),
    }
}

/// Rule 3, the load-bearing half: a ledger file that EXISTS but is not the
/// entry the reference asked for is a build error too.
///
/// Measured, and worth writing down: deleting the missing-file guard alone
/// kills nothing, because any content invented in its place fails this check.
/// So the id comparison is the guard that actually enforces rule 3, and the
/// missing-file arm only improves the error message. That is the redundancy
/// direction this repository has been burned by, inverted -- two guards, one
/// property, both tested -- and it is only safe because THIS test exists.
#[test]
fn a_fact_file_whose_id_disagrees_with_the_reference_is_a_build_error() {
    let dir = scratch("fact-id-disagrees");
    let facts = dir.join("facts");
    std::fs::create_dir_all(&facts).expect("scratch facts dir");
    // A real ledger entry, filed under a different id than it declares.
    std::fs::copy(
        common::repo_root().join("artifacts/facts/F-excluded-middle.json"),
        facts.join("F-bool-and-comm.json"),
    )
    .expect("copyable");
    std::fs::copy(
        common::repo_root().join("artifacts/facts/F-excluded-middle.json"),
        facts.join("F-excluded-middle.json"),
    )
    .expect("copyable");

    let err = common::assemble_with_facts_dir(&dir, &facts, &fixture_doc_json())
        .expect_err("a ledger file that declares a different id must refuse to render");
    match err {
        AssembleError::DanglingFactRef { id, .. } => assert_eq!(id, "F:bool-and-comm"),
        other => panic!("expected DanglingFactRef, got {other}"),
    }
}

/// Rule 4: evidence that describes bytes which are no longer there is a build
/// error. One flipped hex digit in the recorded digest is enough.
#[test]
fn input_hash_mismatch_is_a_build_error() {
    let dir = scratch("input-hash-mismatch");
    let mut record = fixture_record_json();
    let declared = record["provenance"]["inputs"][1]["sha256"]
        .as_str()
        .expect("a declared digest")
        .to_string();
    let mut tampered = declared.clone();
    // Flip one nibble; still a well-formed digest, just not this file's.
    let first = tampered.remove(0);
    tampered.insert(0, if first == '0' { '1' } else { '0' });
    record["provenance"]["inputs"][1]["sha256"] = serde_json::json!(tampered.clone());

    let err = assemble_mutated(&dir, &fixture_doc_json(), &record, false)
        .expect_err("a digest that does not match the bytes must refuse to render");
    match err {
        AssembleError::HashMismatch {
            path,
            declared: d,
            actual,
            ..
        } => {
            assert!(
                path.contains("artifacts/facts/"),
                "error names the file: {path}"
            );
            assert_eq!(d, tampered, "error reports what the run recorded");
            assert_eq!(actual, declared, "error reports what is on disk now");
        }
        other => panic!("expected HashMismatch, got {other}"),
    }
}

/// Rule 2: a run that did not complete cannot establish anything. The claim
/// still renders -- that is the point of the non-strict mode -- but it renders
/// in its failure styling, and no styling path leads back to green.
#[test]
fn nonzero_exit_status_demotes_the_claim() {
    let dir = scratch("nonzero-exit-demotes");
    let mut record = fixture_record_json();
    // Exit 1 while STILL claiming `established`: the shape of a checker that
    // reports success because it finished. The Python validator rejects that
    // combination in a file; this asserts that Rust also refuses to reward it.
    record["provenance"]["exit_status"] = serde_json::json!(1);
    assert_eq!(
        record["outcome"], "established",
        "the combination under test"
    );

    let doc = assemble_mutated(&dir, &fixture_doc_json(), &record, false)
        .expect("non-strict mode renders the demoted claim rather than refusing");
    for (label, status) in &doc.claims {
        assert_eq!(
            *status,
            EvidenceStatus::Open,
            "claim `{label}` rests on a run that exited 1 and must not render as established"
        );
    }
}

/// Rule 2, refuted half: a run that found a counterexample demotes to REFUTED,
/// which is read from the record's `outcome` and never guessed.
#[test]
fn a_refuting_run_renders_the_claim_refuted() {
    let dir = scratch("refuting-run");
    let mut record = fixture_record_json();
    record["provenance"]["exit_status"] = serde_json::json!(1);
    record["outcome"] = serde_json::json!("refuted");

    let doc = assemble_mutated(&dir, &fixture_doc_json(), &record, false)
        .expect("non-strict mode renders the refuted claim");
    for (label, status) in &doc.claims {
        assert_eq!(
            *status,
            EvidenceStatus::Refuted,
            "claim `{label}` should render REFUTED"
        );
    }
}

/// Rule 2, strict half: the same red evidence is a build error under `--strict`.
#[test]
fn nonzero_exit_status_is_an_error_in_strict_mode() {
    let dir = scratch("nonzero-exit-strict");
    let mut record = fixture_record_json();
    record["provenance"]["exit_status"] = serde_json::json!(3);

    let err = assemble_mutated(&dir, &fixture_doc_json(), &record, true)
        .expect_err("strict mode must refuse to render over red evidence");
    match err {
        AssembleError::RedEvidence {
            exit_status,
            record,
            ..
        } => {
            assert_eq!(exit_status, 3);
            assert_eq!(record, "R:fixture-fact-ledger-check");
        }
        other => panic!("expected RedEvidence, got {other}"),
    }
}

/// A run record whose id is not the one the manifest expects: the manifest is
/// pointed at a rebuilt-but-different record, which is how a document quietly
/// stops describing the run it names.
#[test]
fn record_id_mismatch_is_a_build_error() {
    let dir = scratch("record-id-mismatch");
    let mut record = fixture_record_json();
    record["id"] = serde_json::json!("R:some-other-run");

    let err = assemble_mutated(&dir, &fixture_doc_json(), &record, false)
        .expect_err("a record id that does not match the reference must refuse");
    assert!(
        matches!(err, AssembleError::RecordIdMismatch { .. }),
        "expected RecordIdMismatch, got {err}"
    );
}

/// A reference to a claim key the record does not carry. The error lists the
/// keys that ARE there, because the usual cause is a rename.
#[test]
fn missing_claim_key_is_a_build_error() {
    let dir = scratch("missing-claim-key");
    let mut doc = fixture_doc_json();
    first_claim_mut(&mut doc)["kind"]["evidence"][0]["claim_key"] =
        serde_json::json!("not-a-key-in-the-record");

    let err = assemble_mutated(&dir, &doc, &fixture_record_json(), false)
        .expect_err("a claim key the record does not carry must refuse");
    match err {
        AssembleError::MissingClaimKey { key, available, .. } => {
            assert_eq!(key, "not-a-key-in-the-record");
            assert!(
                available.contains(&"f-bool-and-comm".to_string()),
                "the error lists the keys that do exist: {available:?}"
            );
        }
        other => panic!("expected MissingClaimKey, got {other}"),
    }
}

/// The record's own claim status is a CAP: a document that declares `proved`
/// over a run that only claims `evidence` renders at `evidence`.
#[test]
fn a_run_records_status_caps_the_documents_claim() {
    let dir = scratch("record-status-caps");
    let mut doc = fixture_doc_json();
    first_claim_mut(&mut doc)["kind"]["status"] = serde_json::json!("proved");
    let mut record = fixture_record_json();
    record["claims"][0]["status"] = serde_json::json!("evidence");

    let resolved = assemble_mutated(&dir, &doc, &record, false).expect("assembles");
    assert_eq!(
        common::claim_status(&resolved, "Ledger record of F:bool-and-comm"),
        EvidenceStatus::Evidence,
        "a declared status is a ceiling; the record's status lowers it"
    );
}

/// And the reverse must NOT happen: a strong record cannot raise a modest
/// declaration. This is the "no styling path from red evidence to a green
/// claim" property in its positive form.
#[test]
fn a_strong_record_cannot_raise_a_modest_declaration() {
    let dir = scratch("record-cannot-raise");
    let mut doc = fixture_doc_json();
    first_claim_mut(&mut doc)["kind"]["status"] = serde_json::json!("evidence");
    let mut record = fixture_record_json();
    record["claims"][0]["status"] = serde_json::json!("proved");

    let resolved = assemble_mutated(&dir, &doc, &record, false).expect("assembles");
    assert_eq!(
        common::claim_status(&resolved, "Ledger record of F:bool-and-comm"),
        EvidenceStatus::Evidence,
        "assembly can only lower a status"
    );
}
