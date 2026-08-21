//! Determinism, and the mtime attack this repository is specifically prone to.
//!
//! Identical inputs must give byte-identical outputs (01, rule 4). The second
//! half is sharper: cargo decides freshness by MTIME, so a source file OLDER
//! than a cached artifact is invisible to it, and `git archive | tar -x` stamps
//! every file with the COMMIT time -- which has produced green gates over code
//! that was never compiled. Assembly is immune by construction because it
//! re-hashes every declared input on every build, and this file is the evidence
//! that it actually does.

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use axeyum_render::assemble::{AssembleError, AssembleOptions, Assembler};
use axeyum_render::{Emitter, emit_md::MarkdownEmitter, emit_tex::LatexEmitter};

/// Files the fixture document reaches, relative to the repository root.
const NEEDED: &[&str] = &[
    "artifacts/ontology/fact.schema.json",
    "artifacts/facts/F-bool-and-comm.json",
    "artifacts/facts/F-excluded-middle.json",
    "artifacts/lean-imports/bool-and-comm.ndjson",
    "render/tests/fixtures/fixture-footprints.svg",
    "render/tests/fixtures/run-fact-ledger-check.json",
    "render/tests/fixtures/fixture-doc.json",
];

#[test]
fn two_builds_are_byte_identical() {
    let first_md = MarkdownEmitter.emit(&common::assemble_fixture()).primary;
    let second_md = MarkdownEmitter.emit(&common::assemble_fixture()).primary;
    assert_eq!(first_md, second_md, "Markdown output must be reproducible");

    let first_tex = LatexEmitter.emit(&common::assemble_fixture());
    let second_tex = LatexEmitter.emit(&common::assemble_fixture());
    assert_eq!(
        first_tex.primary, second_tex.primary,
        "LaTeX output must be reproducible"
    );
    assert_eq!(
        first_tex.aux, second_tex.aux,
        "side files must be reproducible too"
    );
}

/// Nothing in the pipeline reads a clock: the rendered epoch is the one the
/// manifest supplies, not the one the machine has.
#[test]
fn the_rendered_epoch_comes_from_the_manifest_not_the_machine() {
    let doc = common::assemble_fixture();
    assert_eq!(doc.epoch_unix, 1_787_312_215, "the fixture pins its epoch");
    assert_eq!(doc.epoch_source, "commit");

    let md = MarkdownEmitter.emit(&doc).primary;
    assert!(
        md.contains("Epoch 1787312215"),
        "the emitted epoch is the manifest's"
    );
    let now = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .expect("a sane clock")
        .as_secs();
    assert!(
        !md.contains(&now.to_string()),
        "the current time must not appear anywhere in the output"
    );
}

/// A copy of the inputs with ancient mtimes renders identically -- and the same
/// copy with one byte CHANGED refuses, even though its mtime still says it is
/// old. That is the difference between hashing and stat-ing.
#[test]
fn stale_mtimes_cannot_produce_a_stale_render() {
    let root = common::scratch("mtime-attack");
    for rel in NEEDED {
        copy_into(&common::repo_root(), &root, Path::new(rel));
    }
    // 2020-01-01: older than any artifact this repository has cached.
    let ancient = SystemTime::UNIX_EPOCH + Duration::from_secs(1_577_836_800);
    for rel in NEEDED {
        let f = fs::File::options()
            .write(true)
            .open(root.join(rel))
            .expect("scratch file writable");
        f.set_modified(ancient).expect("mtime settable");
    }

    let rendered = render_from(&root).expect("an old-but-unchanged copy still renders");
    assert_eq!(
        rendered,
        MarkdownEmitter.emit(&common::assemble_fixture()).primary,
        "the render must not depend on where the inputs live or how old they look"
    );

    // Now change the bytes without touching the mtime.
    let victim = root.join("artifacts/facts/F-bool-and-comm.json");
    let mut text = fs::read_to_string(&victim).expect("readable");
    text.push('\n');
    fs::write(&victim, text).expect("writable");
    let f = fs::File::options()
        .write(true)
        .open(&victim)
        .expect("writable");
    f.set_modified(ancient).expect("mtime settable");

    let err = render_from(&root).expect_err("changed bytes must refuse, whatever the mtime says");
    match err {
        AssembleError::HashMismatch { path, .. } => {
            assert!(
                path.ends_with("F-bool-and-comm.json"),
                "the error names the file: {path}"
            );
        }
        other => panic!("expected HashMismatch, got {other}"),
    }
}

fn render_from(root: &Path) -> Result<String, AssembleError> {
    let manifest_dir = root.join("render/tests/fixtures");
    let opts = AssembleOptions::new(root.to_path_buf(), manifest_dir.clone());
    let doc = Assembler::new(opts).assemble_path(&manifest_dir.join(common::DOC_FILE))?;
    Ok(MarkdownEmitter.emit(&doc).primary)
}

fn copy_into(from_root: &Path, to_root: &Path, rel: &Path) {
    let dest: PathBuf = to_root.join(rel);
    fs::create_dir_all(dest.parent().expect("a parent")).expect("scratch dirs");
    fs::copy(from_root.join(rel), &dest)
        .unwrap_or_else(|e| panic!("copy {} -> {}: {e}", rel.display(), dest.display()));
}
