//! External acceptance: a development this kernel checked is replayed into the
//! **real Lean kernel** from our official `lean4export` NDJSON 3.1.0 stream.
//!
//! This is the only check in the repository that is neither our own kernel
//! agreeing with itself nor Lean's *elaborator* reading surface syntax.
//! `scripts/lean/replay-lean4export.lean` parses the stream and hands each
//! declaration to `Lean.Environment.addDeclCore` — Lean's own kernel type
//! checker — starting from `mkEmptyEnvironment`, so nothing can be silently
//! satisfied by Lean's `Init` and no implicit argument, coercion or code
//! generator is involved.
//!
//! Lean is optional locally and mandatory under `AXEYUM_REQUIRE_LEAN=1`, like
//! the other cross-checks in this crate. The negative control is not optional:
//! if the same binary accepts a tampered stream, a pass above proves nothing.

use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_kernel::{Kernel, Lean4ExportMetadata, build_logic_prelude, build_nat_prelude};

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

fn replay_script() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/lean/replay-lean4export.lean")
        .canonicalize()
        .expect("the replay script must exist")
}

/// A development with two theorems of *different* statements, so a proof can be
/// swapped onto the wrong statement for the negative control.
fn development() -> String {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    build_nat_prelude(&mut kernel).expect("nat prelude must build");
    let anonymous = kernel.anon();
    let zero = kernel.level_zero();

    let true_const = kernel.const_(logic.true_, vec![]);
    let trivial = kernel.const_(logic.true_intro, vec![]);
    let first = kernel.name_str(anonymous, "axeyum_replay_trivial");
    kernel
        .add_declaration(axeyum_lean_kernel::Declaration::Theorem {
            name: first,
            uparams: Vec::new(),
            ty: true_const,
            value: trivial,
        })
        .expect("True must be provable");

    let eq = kernel.const_(logic.eq, vec![zero]);
    let goal = kernel.app(eq, true_const);
    let goal = kernel.app(goal, trivial);
    let goal = kernel.app(goal, trivial);
    let refl = kernel.const_(logic.eq_refl, vec![zero]);
    let proof = kernel.app(refl, true_const);
    let proof = kernel.app(proof, trivial);
    let second = kernel.name_str(anonymous, "axeyum_replay_refl");
    kernel
        .add_declaration(axeyum_lean_kernel::Declaration::Theorem {
            name: second,
            uparams: Vec::new(),
            ty: goal,
            value: proof,
        })
        .expect("reflexivity must be provable");

    kernel
        .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
        .expect("the checked development must export")
}

/// The `"value":<n>` field of the `record_index`-th (0-based) theorem record.
fn theorem_value(stream: &str, record_index: usize) -> (String, u64) {
    let record = stream
        .lines()
        .filter(|line| line.starts_with("{\"thm\":"))
        .nth(record_index)
        .expect("theorem record must exist");
    let tail = record
        .split_once("\"value\":")
        .expect("theorem record carries a value")
        .1;
    let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
    (
        record.to_owned(),
        digits.parse().expect("value index is numeric"),
    )
}

fn run_replay(lean: &Path, stream: &str, name: &str) -> (bool, String) {
    let directory = std::env::temp_dir().join(format!("axeyum_replay_{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("create replay directory");
    let file = directory.join(format!("{name}.ndjson"));
    std::fs::write(&file, stream).expect("write replay stream");
    let output = Command::new(lean)
        .arg("--run")
        .arg(replay_script())
        .arg(&file)
        .output()
        .expect("run the Lean replay script");
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (output.status.success(), combined)
}

#[test]
fn the_real_lean_kernel_accepts_an_axeyum_development_and_rejects_a_tampered_one() {
    let stream = development();
    assert!(
        stream.lines().count() > 100,
        "the development must be non-trivial"
    );

    let Some(lean) = lean_bin() else {
        assert_ne!(
            std::env::var("AXEYUM_REQUIRE_LEAN").as_deref(),
            Ok("1"),
            "AXEYUM_REQUIRE_LEAN=1 but no Lean binary was found"
        );
        eprintln!("[skip] real Lean is optional locally; CI requires it");
        return;
    };

    let (accepted, report) = run_replay(&lean, &stream, "development");
    assert!(
        accepted,
        "the real Lean kernel rejected the export:\n{report}"
    );
    assert!(
        report.contains("the real Lean kernel accepted"),
        "the replay script must report what it admitted: {report}"
    );

    // Negative control: give the equality theorem the proof of `True`. Both
    // proofs are closed and already declared, so this is a pure type mismatch
    // that only a real type checker can catch.
    let (trivial_record, trivial_value) = theorem_value(&stream, 0);
    let (refl_record, refl_value) = theorem_value(&stream, 1);
    assert_ne!(trivial_value, refl_value);
    let tampered = stream.replace(
        &refl_record,
        &refl_record.replace(
            &format!("\"value\":{refl_value}"),
            &format!("\"value\":{trivial_value}"),
        ),
    );
    assert_ne!(tampered, stream, "the negative control must change bytes");
    assert!(!trivial_record.is_empty());

    let (accepted, report) = run_replay(&lean, &tampered, "tampered");
    assert!(
        !accepted,
        "the real Lean kernel accepted a mismatched proof; the positive result is worthless:\n{report}"
    );
    assert!(
        report.contains("REAL LEAN KERNEL REJECTED"),
        "the rejection must come from the kernel: {report}"
    );
}
