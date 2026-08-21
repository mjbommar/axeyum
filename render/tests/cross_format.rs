//! The cross-format property: every emitter reports the same claims with the
//! same statuses.
//!
//! The claims are recovered FROM THE EMITTED BYTES, not from the resolved
//! document. That distinction is the whole test: reading the resolved document
//! would prove that two emitters were handed the same data, which is trivially
//! true. Parsing their output proves they both said so -- and makes an omitted
//! claim a failing test rather than a silently shorter page.
//!
//! DESIGN's HTML emitter joins this test in round 2 (contract point 5 in the
//! crate documentation): it must emit each label paired with the exact
//! uppercase badge token, recoverable by a parser like the two below.

mod common;

use axeyum_render::{Emitter, emit_md::MarkdownEmitter, emit_tex::LatexEmitter};

/// Recover `(label, badge)` from Markdown: lines of the form
/// `**Claim -- LABEL** [BADGE]`.
fn claims_from_markdown(md: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for line in md.lines() {
        let Some(rest) = line.strip_prefix("**Claim -- ") else {
            continue;
        };
        let Some((label, tail)) = rest.split_once("** [") else {
            continue;
        };
        let Some(badge) = tail.strip_suffix(']') else {
            continue;
        };
        out.push((label.to_string(), badge.to_string()));
    }
    out
}

/// Recover `(label, badge)` from LaTeX: `\axclaim{LABEL}{BADGE}`.
fn claims_from_latex(tex: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut rest = tex;
    while let Some(at) = rest.find("\\axclaim{") {
        rest = &rest[at + "\\axclaim{".len()..];
        let Some(end_label) = rest.find('}') else {
            break;
        };
        let label = rest[..end_label].to_string();
        rest = &rest[end_label + 1..];
        let Some(open) = rest.strip_prefix('{') else {
            continue;
        };
        let Some(end_badge) = open.find('}') else {
            break;
        };
        out.push((label, open[..end_badge].to_string()));
        rest = &open[end_badge + 1..];
    }
    out
}

#[test]
fn markdown_and_latex_report_the_same_claims_and_statuses() {
    let doc = common::assemble_fixture();
    let md = claims_from_markdown(&MarkdownEmitter.emit(&doc).primary);
    let tex = claims_from_latex(&LatexEmitter.emit(&doc).primary);

    assert!(
        !md.is_empty(),
        "recovered no claims from the Markdown output at all"
    );
    assert_eq!(
        md, tex,
        "the two formats disagree about what this document claims"
    );
}

/// And both agree with what assembly computed. This is the direction that
/// catches an emitter which invents or paraphrases a badge.
#[test]
fn both_formats_agree_with_the_resolved_document() {
    let doc = common::assemble_fixture();
    let expected: Vec<(String, String)> = doc
        .claims
        .iter()
        .map(|(l, s)| (l.clone(), s.badge().to_string()))
        .collect();

    assert_eq!(
        claims_from_markdown(&MarkdownEmitter.emit(&doc).primary),
        expected
    );
    assert_eq!(
        claims_from_latex(&LatexEmitter.emit(&doc).primary),
        expected
    );
}

/// The property must be sensitive to a demotion: when the evidence turns red,
/// BOTH formats must say so, in step.
#[test]
fn a_demotion_moves_both_formats_together() {
    let dir = common::scratch("cross-format-demotion");
    let mut record = common::fixture_record_json();
    record["provenance"]["exit_status"] = serde_json::json!(1);
    record["outcome"] = serde_json::json!("refuted");
    let doc = common::assemble_mutated(&dir, &common::fixture_doc_json(), &record, false)
        .expect("non-strict mode renders the demoted document");

    let md = claims_from_markdown(&MarkdownEmitter.emit(&doc).primary);
    let tex = claims_from_latex(&LatexEmitter.emit(&doc).primary);
    assert_eq!(md, tex, "the formats must demote together");
    assert!(
        md.iter().all(|(_, badge)| badge == "REFUTED"),
        "every claim over refuting evidence must render REFUTED, got {md:?}"
    );
}

/// The parsers themselves must be able to fail; otherwise this whole file is a
/// checker that cannot fail. Feed each one output from the OTHER format.
#[test]
fn the_recovery_parsers_are_not_vacuous() {
    let doc = common::assemble_fixture();
    let md_bytes = MarkdownEmitter.emit(&doc).primary;
    let tex_bytes = LatexEmitter.emit(&doc).primary;

    assert!(
        claims_from_latex(&md_bytes).is_empty(),
        "the LaTeX parser found claims in Markdown output; it is matching something too loose"
    );
    assert!(
        claims_from_markdown(&tex_bytes).is_empty(),
        "the Markdown parser found claims in LaTeX output; it is matching something too loose"
    );
}
