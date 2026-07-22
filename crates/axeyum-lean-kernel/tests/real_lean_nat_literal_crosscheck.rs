//! Differential TL2.7 Nat literal controls against pinned official Lean 4.30.

use std::path::PathBuf;
use std::process::{Command, Output};

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

fn run_lean(lean: &PathBuf, file: &std::path::Path) -> Output {
    Command::new(lean)
        .args(["-j", "1", "-s", "1024", "-M", "4096"])
        .arg(file)
        .output()
        .expect("run official Lean Nat literal cross-check")
}

#[test]
fn constructor_offset_recursor_and_false_controls_agree_with_lean_4_30() {
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
    let version_text = format!(
        "{}{}",
        String::from_utf8_lossy(&version.stdout),
        String::from_utf8_lossy(&version.stderr)
    );
    assert!(version.status.success(), "{version_text}");
    assert!(
        version_text.contains("4.30.0"),
        "TL2.7 comparison requires pinned Lean 4.30.0, got: {version_text}"
    );

    let directory = std::env::temp_dir().join(format!(
        "axeyum_nat_literal_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create Nat literal cross-check directory");

    let positive_source = r"
example : nat_lit 0 = Nat.zero := rfl

example :
    nat_lit 3 = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := rfl

example :
    nat_lit 340282366920938463463374607431768211456 =
      Nat.succ (nat_lit 340282366920938463463374607431768211455) := rfl

example :
    Nat.rec (motive := fun _ => Nat)
      Nat.zero (fun _ ih => Nat.succ ih) (nat_lit 3) = nat_lit 3 := rfl
";
    let positive_file = directory.join("NatLiteralPositive.lean");
    std::fs::write(&positive_file, positive_source).expect("write positive Lean control");
    let positive = run_lean(&lean, &positive_file);
    assert!(
        positive.status.success(),
        "official Lean rejected positive Nat literal controls ({})\nstdout:\n{}\nstderr:\n{}\nsource:\n{positive_source}",
        lean.display(),
        String::from_utf8_lossy(&positive.stdout),
        String::from_utf8_lossy(&positive.stderr),
    );

    let negative_source = r"
example : nat_lit 37 = Nat.succ (nat_lit 37) := rfl
";
    let negative_file = directory.join("NatLiteralNegative.lean");
    std::fs::write(&negative_file, negative_source).expect("write negative Lean control");
    let negative = run_lean(&lean, &negative_file);
    let negative_stdout = String::from_utf8_lossy(&negative.stdout);
    let negative_stderr = String::from_utf8_lossy(&negative.stderr);
    assert!(
        !negative.status.success(),
        "official Lean accepted the false Nat literal equality\nstdout:\n{negative_stdout}\nstderr:\n{negative_stderr}\nsource:\n{negative_source}"
    );
    let negative_output = format!("{negative_stdout}\n{negative_stderr}");
    assert!(
        negative_output.contains("rfl") || negative_output.contains("type mismatch"),
        "negative control failed for an unexpected reason: {negative_output}"
    );

    let _ = std::fs::remove_dir_all(directory);
}
