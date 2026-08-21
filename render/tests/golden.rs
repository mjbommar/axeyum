//! Byte-exact golden files for the Markdown and LaTeX emitters.
//!
//! The golden is a REAL document: two entries of this repository's fact ledger,
//! resolved through a run record that a real script produced by really checking
//! them. That matters more than it sounds -- a golden over invented evidence
//! tests the formatter and nothing else, while this one fails if the ledger
//! entries change, which is exactly the coupling the strand exists to create.
//!
//! To refresh after an intentional change:
//!
//! ```sh
//! python3 render/tests/fixtures/make_run_record.py   # if the ledger moved
//! UPDATE_GOLDEN=1 cargo test --manifest-path render/Cargo.toml --test golden
//! git diff render/tests/golden                       # READ THE DIFF
//! ```
//!
//! Reading the diff is not optional: the whole value of a golden is that a
//! change nobody intended shows up as a change nobody intended.

mod common;

use std::path::Path;

use axeyum_render::{Emitter, emit_md::MarkdownEmitter, emit_tex::LatexEmitter};

fn compare(name: &str, actual: &str) {
    let path = common::golden_dir().join(name);
    if std::env::var_os("UPDATE_GOLDEN").is_some() {
        std::fs::create_dir_all(common::golden_dir()).expect("golden dir");
        std::fs::write(&path, actual).expect("golden writable");
        eprintln!("UPDATE_GOLDEN: wrote {}", path.display());
        return;
    }
    let expected = read_golden(&path);
    if expected != actual {
        let scratch = common::scratch("golden-actual");
        let out = scratch.join(name);
        std::fs::write(&out, actual).expect("scratch writable");
        panic!(
            "golden mismatch for {name}\n  expected: {}\n  actual:   {}\n  \
             first difference at byte {}\n  \
             If the change is intended: UPDATE_GOLDEN=1 cargo test --test golden",
            path.display(),
            out.display(),
            first_difference(&expected, actual)
        );
    }
}

fn read_golden(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| {
        panic!(
            "cannot read golden {}: {e}\n  \
             If this is a new golden: UPDATE_GOLDEN=1 cargo test --test golden",
            path.display()
        )
    })
}

fn first_difference(a: &str, b: &str) -> usize {
    a.bytes()
        .zip(b.bytes())
        .position(|(x, y)| x != y)
        .unwrap_or_else(|| a.len().min(b.len()))
}

#[test]
fn markdown_golden() {
    let doc = common::assemble_fixture();
    let out = MarkdownEmitter.emit(&doc);
    compare("fixture-fact-ledger.md", &out.primary);
    assert!(
        out.aux.is_empty(),
        "this fixture's figures are files, not inline SVG"
    );
}

#[test]
fn latex_golden() {
    let doc = common::assemble_fixture();
    let out = LatexEmitter.emit(&doc);
    compare("fixture-fact-ledger.tex", &out.primary);
    // The side files are part of the contract: a fragment that arrives without
    // its style package does not compile, and the compile gate needs a wrapper.
    let names: Vec<&str> = out.aux.keys().map(String::as_str).collect();
    assert_eq!(
        names,
        vec!["axeyum.sty", "fixture-fact-ledger-standalone.tex"]
    );
    compare("axeyum.sty", &out.aux["axeyum.sty"]);
    compare(
        "fixture-fact-ledger-standalone.tex",
        &out.aux["fixture-fact-ledger-standalone.tex"],
    );
}

/// Both emitters are ASCII-only (repository-wide rule), and neither smuggles a
/// byte in from the ledger without noticing.
#[test]
fn every_emitted_byte_is_ascii() {
    let doc = common::assemble_fixture();
    for (format, out) in [
        (MarkdownEmitter.format_name(), MarkdownEmitter.emit(&doc)),
        (LatexEmitter.format_name(), LatexEmitter.emit(&doc)),
    ] {
        let mut files = vec![(format.to_string(), out.primary)];
        files.extend(out.aux);
        for (name, body) in files {
            if let Some(pos) = body.bytes().position(|b| !b.is_ascii()) {
                panic!("{format} output `{name}` has a non-ASCII byte at offset {pos}");
            }
        }
    }
}

/// The verbosity tiers are honoured mechanically: a `detail` block's body must
/// not appear in the body of the Markdown document except inside a fold, and an
/// `archive` block's CONTENT must not appear at all.
#[test]
fn verbosity_tiers_are_honoured_in_markdown() {
    let doc = common::assemble_fixture();
    let md = MarkdownEmitter.emit(&doc).primary;

    assert!(
        md.contains("<details>"),
        "the fixture has a detail-tier block"
    );
    // The excluded-middle statement is detail-tier; its formal statement may
    // appear only after a <details> opener.
    let fold = md.find("<details>").expect("a fold");
    let formal = md
        .find("(assert (or p (not p)))")
        .expect("the detail block's content");
    assert!(
        formal > fold,
        "detail content must be inside the fold, not before it"
    );

    // The include block is archive-tier: a link, and no inlined JSON.
    assert!(
        md.contains("*Archived --"),
        "the archive tier renders as a one-line link"
    );
    assert!(
        !md.contains("\"schema_version\": 1"),
        "archive-tier content must not be inlined into the document"
    );
}

/// LaTeX `detail` mode is configurable, and the fixture selects `appendix`.
#[test]
fn latex_detail_mode_moves_detail_blocks_to_the_end() {
    let doc = common::assemble_fixture();
    let tex = LatexEmitter.emit(&doc).primary;
    let marker = tex.find("\\axdetailref{1}").expect("a reference in place");
    let section = tex
        .find("\\subsection*{Details}")
        .expect("the details section");
    let body = tex
        .find("(assert (or p (not p)))")
        .expect("the moved content");
    assert!(
        marker < section,
        "the in-place reference comes before the appendix"
    );
    assert!(section < body, "the detail body sits inside the appendix");
}
