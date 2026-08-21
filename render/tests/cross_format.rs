//! The cross-format property: every emitter reports the same claims with the
//! same statuses.
//!
//! The claims are recovered FROM THE EMITTED BYTES, not from the resolved
//! document. That distinction is the whole test: reading the resolved document
//! would prove that two emitters were handed the same data, which is trivially
//! true. Parsing their output proves they both said so -- and makes an omitted
//! claim a failing test rather than a silently shorter page.
//!
//! The HTML emitter joined this test in round 2 (contract point 5 in the crate
//! documentation): it emits each label paired with the exact uppercase badge
//! token as `data-claim` / `data-status` on the claim card, recovered by
//! `claims_from_html` below. All three sets must be equal.
//!
//! The HTML half is behind the `html` cargo feature, which is ON BY DEFAULT
//! since round 2 -- and `render/check.sh` additionally asserts by NAME that
//! the three-format test ran, because a feature-gated test that compiles to
//! nothing is this repository's signature inert gate.

mod common;

#[cfg(feature = "html")]
use axeyum_render::emit_html::HtmlEmitter;
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

/// Recover `(label, badge)` from HTML: `data-claim="LABEL" data-status="BADGE"`
/// on a claim card, in document order.
///
/// The attribute values are HTML-escaped on the way out (`esc_attr`), so they
/// are unescaped here. Doing that is the point rather than a nuisance: a label
/// containing `&` must come back as `&`, or the three sets differ for a
/// reason that has nothing to do with what the document claims.
#[cfg(feature = "html")]
fn claims_from_html(html: &str) -> Vec<(String, String)> {
    fn unescape(s: &str) -> String {
        let mut out = String::with_capacity(s.len());
        let mut rest = s;
        while let Some(amp) = rest.find('&') {
            out.push_str(&rest[..amp]);
            rest = &rest[amp..];
            let Some(semi) = rest.find(';') else {
                break;
            };
            let entity = &rest[1..semi];
            match entity {
                "amp" => out.push('&'),
                "lt" => out.push('<'),
                "gt" => out.push('>'),
                "quot" => out.push('"'),
                _ => {
                    let decoded = entity
                        .strip_prefix('#')
                        .and_then(|n| match n.strip_prefix('x').or(n.strip_prefix('X')) {
                            Some(hex) => u32::from_str_radix(hex, 16).ok(),
                            None => n.parse::<u32>().ok(),
                        })
                        .and_then(char::from_u32);
                    match decoded {
                        Some(c) => out.push(c),
                        // Not an entity this emitter produces: keep it verbatim
                        // rather than guessing, so a mismatch stays visible.
                        None => out.push_str(&rest[..=semi]),
                    }
                }
            }
            rest = &rest[semi + 1..];
        }
        out.push_str(rest);
        out
    }

    let mut out = Vec::new();
    let mut rest = html;
    while let Some(at) = rest.find("data-claim=\"") {
        rest = &rest[at + "data-claim=\"".len()..];
        let Some(end) = rest.find('"') else { break };
        let label = unescape(&rest[..end]);
        rest = &rest[end + 1..];
        let Some(tail) = rest.strip_prefix(" data-status=\"") else {
            continue;
        };
        let Some(end) = tail.find('"') else { break };
        out.push((label, unescape(&tail[..end])));
        rest = &tail[end + 1..];
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
/// The criterion from `04-prototype-plan.md`: the (claim, status) set is
/// identical across ALL THREE formats. Markdown and LaTeX agreeing is a
/// two-way check; the third format is where an emitter that renders a badge
/// from its own judgment would show up.
#[cfg(feature = "html")]
#[test]
fn all_three_formats_report_the_same_claims_and_statuses() {
    let doc = common::assemble_fixture();
    let md = claims_from_markdown(&MarkdownEmitter.emit(&doc).primary);
    let tex = claims_from_latex(&LatexEmitter.emit(&doc).primary);
    let html = claims_from_html(&HtmlEmitter.emit(&doc).primary);

    assert!(!html.is_empty(), "recovered no claims from the HTML output");
    assert_eq!(md, html, "Markdown and HTML disagree");
    assert_eq!(tex, html, "LaTeX and HTML disagree");

    let expected: Vec<(String, String)> = doc
        .claims
        .iter()
        .map(|(l, s)| (l.clone(), s.badge().to_string()))
        .collect();
    assert_eq!(html, expected, "HTML disagrees with the resolved document");
}

/// The same property over the two REAL P0 manifests, not the test fixture: the
/// certificate page and the fact pilot. A property that holds only on the
/// fixture is a property about the fixture.
#[cfg(feature = "html")]
#[test]
fn the_committed_p0_manifests_agree_across_all_three_formats() {
    let mut checked = 0usize;
    for manifest in [
        "examples-input/cert/certificate.doc.json",
        "examples-input/cert/certificate-negative-control.doc.json",
        "examples-input/facts/facts-pilot.doc.json",
    ] {
        let path = common::package_root().join(manifest);
        let mut opts = axeyum_render::assemble::AssembleOptions::new(
            common::repo_root(),
            path.parent().expect("manifest has a parent").to_path_buf(),
        );
        opts.strict = false;
        let doc = axeyum_render::assemble::Assembler::new(opts)
            .assemble_path(&path)
            .unwrap_or_else(|e| panic!("{manifest} must assemble: {e}"));
        let md = claims_from_markdown(&MarkdownEmitter.emit(&doc).primary);
        let tex = claims_from_latex(&LatexEmitter.emit(&doc).primary);
        let html = claims_from_html(&HtmlEmitter.emit(&doc).primary);
        assert_eq!(md, tex, "{manifest}: markdown vs latex");
        assert_eq!(md, html, "{manifest}: markdown vs html");
        checked += md.len();
    }
    // The fact pilot legitimately carries no claims (see 13-facts-diary), so
    // this counts claims across the set rather than requiring each to have one.
    assert!(
        checked >= 3,
        "recovered only {checked} claim(s) across the P0 manifests; the corpus went quiet"
    );
}

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
    #[cfg(feature = "html")]
    assert_eq!(
        md,
        claims_from_html(&HtmlEmitter.emit(&doc).primary),
        "the formats must demote together"
    );
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

    // Same control for the third parser, in both directions: the HTML parser
    // must find nothing in the other two formats, and neither of them may find
    // anything in HTML. A parser that matched everything would make the
    // three-way property trivially true.
    #[cfg(feature = "html")]
    {
        let html_bytes = HtmlEmitter.emit(&doc).primary;
        assert!(claims_from_html(&md_bytes).is_empty());
        assert!(claims_from_html(&tex_bytes).is_empty());
        assert!(claims_from_markdown(&html_bytes).is_empty());
        assert!(claims_from_latex(&html_bytes).is_empty());
    }
}
