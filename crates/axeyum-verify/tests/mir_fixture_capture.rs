//! Reproducibility gate for the committed compiler-MIR fixture.

use std::path::Path;
use std::process::Command;

#[test]
fn committed_mir_fixture_is_current_and_replay_status_is_explicit() {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let workspace = manifest_dir
        .parent()
        .and_then(Path::parent)
        .expect("axeyum-verify must be nested under the workspace crates directory");
    let output = Command::new("python3")
        .arg(workspace.join("scripts/check-verify-mir-fixture.py"))
        .arg("--verify")
        .output()
        .expect("python3 must execute the repository MIR fixture checker");

    assert!(
        output.status.success(),
        "MIR fixture check failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stdout = String::from_utf8(output.stdout).expect("checker output must be UTF-8 JSON");
    assert!(stdout.contains("\"content_valid\":true"), "{stdout}");
    assert!(
        stdout.contains("\"compiler_replay\":\"exact\"")
            || stdout.contains("\"compiler_replay\":\"unavailable\""),
        "checker must report replay status explicitly: {stdout}",
    );
}
