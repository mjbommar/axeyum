//! Mandatory M3 differential for the immutable TL2.11 source population.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

const DIAGNOSTIC: &str = "has a non positive occurrence of the datatypes being declared";

#[derive(Clone, Copy)]
struct SourceCase {
    id: &'static str,
    relative_path: &'static str,
    module: &'static str,
    accepted: bool,
}

const SOURCES: [SourceCase; 4] = [
    SourceCase {
        id: "construct-matrix-positive",
        relative_path: "docs/plan/fixtures/lean4export-v4.30-construct-matrix.lean",
        module: "AxeyumConstructMatrix",
        accepted: true,
    },
    SourceCase {
        id: "negative-domain",
        relative_path: "docs/plan/fixtures/lean4export-v4.30-construct-matrix-negative.lean",
        module: "AxeyumConstructMatrixNegative",
        accepted: false,
    },
    SourceCase {
        id: "negative-mixed",
        relative_path: "docs/plan/fixtures/lean-v4.30-strict-positivity-negative-mixed.lean",
        module: "AxeyumStrictPositivityMixed",
        accepted: false,
    },
    SourceCase {
        id: "negative-deep",
        relative_path: "docs/plan/fixtures/lean-v4.30-strict-positivity-negative-deep.lean",
        module: "AxeyumStrictPositivityDeep",
        accepted: false,
    },
];

fn lean_bin() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("AXEYUM_LEAN_BIN") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return Some(path);
        }
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|directory| directory.join("lean"))
        .find(|candidate| candidate.is_file())
}

fn run_lean(lean: &Path, directory: &Path, module: &str) -> Output {
    Command::new(lean)
        .current_dir(directory)
        .args(["-j1", "-s", "1024", "-M", "4096", "-o"])
        .arg(format!("{module}.olean"))
        .arg(format!("{module}.lean"))
        .output()
        .expect("run pinned official Lean strict-positivity cross-check")
}

fn combined_output(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

#[test]
fn frozen_sources_repeat_against_pinned_lean_4_30() {
    let Some(lean) = lean_bin() else {
        assert_ne!(
            std::env::var("AXEYUM_REQUIRE_LEAN").as_deref(),
            Ok("1"),
            "AXEYUM_REQUIRE_LEAN=1 but no Lean binary was found"
        );
        eprintln!("[skip] real Lean is optional locally; CI requires it");
        return;
    };

    let version = Command::new(&lean)
        .arg("--version")
        .output()
        .expect("query official Lean version");
    let version_text = combined_output(&version);
    assert!(version.status.success(), "{version_text}");
    assert!(
        version_text.contains("version 4.30.0")
            && version_text.contains("commit d024af099ca4bf2c86f649261ebf59565dc8c622"),
        "TL2.11 requires exact pinned Lean, got: {version_text}"
    );

    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "axeyum_strict_positivity_crosscheck_{}_{}",
        std::process::id(),
        nonce
    ));
    std::fs::create_dir_all(&root).expect("create strict-positivity cross-check root");
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");

    let mut accepted = 0_usize;
    let mut rejected = 0_usize;
    let mut diagnostics = 0_usize;
    for repetition in 1..=2 {
        for source in SOURCES {
            let directory = root.join(format!("run{repetition}-{}", source.id));
            std::fs::create_dir(&directory).expect("create fresh source directory");
            let destination = directory.join(format!("{}.lean", source.module));
            std::fs::copy(repository.join(source.relative_path), &destination)
                .expect("copy immutable Lean source");
            let output = run_lean(&lean, &directory, source.module);
            let text = combined_output(&output);
            if source.accepted {
                assert!(
                    output.status.success(),
                    "run {repetition} {} unexpectedly rejected:\n{text}",
                    source.id
                );
                assert!(
                    directory.join(format!("{}.olean", source.module)).is_file(),
                    "run {repetition} {} did not produce its olean",
                    source.id
                );
                accepted += 1;
            } else {
                assert!(
                    !output.status.success(),
                    "run {repetition} {} unexpectedly admitted",
                    source.id
                );
                assert!(
                    text.contains(DIAGNOSTIC),
                    "run {repetition} {} failed for the wrong reason:\n{text}",
                    source.id
                );
                assert!(
                    !directory.join(format!("{}.olean", source.module)).exists(),
                    "run {repetition} {} published an olean after rejection",
                    source.id
                );
                rejected += 1;
                diagnostics += 1;
            }
        }
    }

    assert_eq!((accepted, rejected, diagnostics), (2, 6, 6));
    println!(
        "LEAN_STRICT_POSITIVITY_CROSSCHECK|sources=4|runs=8|accepted=2|rejected=6|diagnostics=6"
    );
    std::fs::remove_dir_all(&root).expect("remove owned strict-positivity temp root");
}
