//! Differential TL2.5 structure-eta controls against the pinned official Lean
//! binary used by CI.
//!
//! Local development may omit Lean; `AXEYUM_REQUIRE_LEAN=1` makes a missing
//! binary fail closed. The positive module must accept `rfl` for the standard
//! record reconstruction, while the field-duplication mutation must reject it.

use std::path::PathBuf;
use std::process::{Command, Output};

#[path = "support/lean_probe.rs"]
mod lean_probe;

fn run_lean(lean: &PathBuf, file: &std::path::Path) -> Output {
    Command::new(lean)
        // Keep this gate viable under the repository's hard 4 GiB process
        // bound. Lean's default thread stack reservation can itself exhaust a
        // virtual-memory limit on high-core hosts, even for this tiny module.
        .args(["-j", "1", "-s", "1024", "-M", "4096"])
        .arg(file)
        .output()
        .expect("run official Lean structure-eta cross-check")
}

#[test]
fn positive_and_false_equality_controls_agree_with_real_lean() {
    // The positive structure-eta control and the false-equality control.
    let Some(lean) = lean_probe::lean_bin_or_skip("structure-eta", 2) else {
        return;
    };

    let directory = std::env::temp_dir().join(format!(
        "axeyum_structure_eta_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create Lean cross-check directory");

    let positive_source = r"
structure AxeyumEtaPair where
  left : Nat
  right : Nat

example (p : AxeyumEtaPair) :
    AxeyumEtaPair.mk p.left p.right = p := rfl
";
    let positive_file = directory.join("StructureEtaPositive.lean");
    std::fs::write(&positive_file, positive_source).expect("write positive Lean control");
    let positive = run_lean(&lean, &positive_file);
    assert!(
        positive.status.success(),
        "official Lean rejected positive structure eta ({})\nstdout:\n{}\nstderr:\n{}\nsource:\n{positive_source}",
        lean.display(),
        String::from_utf8_lossy(&positive.stdout),
        String::from_utf8_lossy(&positive.stderr),
    );

    let negative_source = r"
structure AxeyumEtaPair where
  left : Nat
  right : Nat

axiom p : AxeyumEtaPair

example : AxeyumEtaPair.mk p.left p.left = p := rfl
";
    let negative_file = directory.join("StructureEtaNegative.lean");
    std::fs::write(&negative_file, negative_source).expect("write negative Lean control");
    let negative = run_lean(&lean, &negative_file);
    let negative_stdout = String::from_utf8_lossy(&negative.stdout);
    let negative_stderr = String::from_utf8_lossy(&negative.stderr);
    assert!(
        !negative.status.success(),
        "official Lean accepted the false structure equality\nstdout:\n{negative_stdout}\nstderr:\n{negative_stderr}\nsource:\n{negative_source}",
    );
    let negative_output = format!("{negative_stdout}\n{negative_stderr}");
    assert!(
        negative_output.contains("rfl") || negative_output.contains("type mismatch"),
        "negative control failed for an unexpected reason: {negative_output}"
    );

    let _ = std::fs::remove_dir_all(directory);
    lean_probe::report_checked("structure-eta", 2);
}
