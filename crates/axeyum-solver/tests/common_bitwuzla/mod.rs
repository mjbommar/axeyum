//! Fail-closed Bitwuzla subprocess helper for publication differential gates.
//!
//! The official Bitwuzla CLI accepts SMT-LIB 2 on stdin and exposes a
//! millisecond wall-clock limit. Routine tests may omit the external binary;
//! publication commands make its presence and complete decision explicit.

#![allow(dead_code)]

use std::io::Write as _;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Duration;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum DetailedVerdict {
    Sat,
    Unsat,
    Unknown,
    Failure(String),
}

/// Resolve an explicit binary, `PATH`, or the reproducible reference checkout.
pub fn bitwuzla_bin() -> Option<String> {
    let responds = |bin: &str| -> bool {
        Command::new(bin)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|status| status.success())
    };

    if let Ok(bin) = std::env::var("AXEYUM_BITWUZLA_BIN") {
        return responds(&bin).then_some(bin);
    }
    if responds("bitwuzla") {
        return Some("bitwuzla".to_string());
    }
    let reference = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../references/bitwuzla/build/src/main/bitwuzla");
    let reference = reference.to_string_lossy().into_owned();
    responds(&reference).then_some(reference)
}

/// Decide one valid generated script. Process, parser, and output failures are
/// distinct from an explicit solver `unknown` so callers can fail closed.
pub fn bitwuzla_decide_detailed(bin: &str, text: &str, timeout: Duration) -> DetailedVerdict {
    let timeout_ms = timeout.as_millis().max(1);
    let mut child = match Command::new(bin)
        .arg("--lang")
        .arg("smt2")
        .arg("--seed")
        .arg("0")
        .arg("--time-limit")
        .arg(timeout_ms.to_string())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(error) => return DetailedVerdict::Failure(format!("spawn failed: {error}")),
    };
    if let Some(stdin) = child.stdin.as_mut()
        && let Err(error) = stdin.write_all(text.as_bytes())
    {
        return DetailedVerdict::Failure(format!("stdin write failed: {error}"));
    }
    drop(child.stdin.take());
    let output = match child.wait_with_output() {
        Ok(output) => output,
        Err(error) => return DetailedVerdict::Failure(format!("wait failed: {error}")),
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() {
        return DetailedVerdict::Failure(format!(
            "exit={} stdout={stdout:?} stderr={stderr:?}",
            output.status
        ));
    }
    for line in stdout.lines() {
        match line.trim() {
            "sat" => return DetailedVerdict::Sat,
            "unsat" => return DetailedVerdict::Unsat,
            "unknown" => return DetailedVerdict::Unknown,
            _ => {}
        }
    }
    DetailedVerdict::Failure(format!(
        "exit={} stdout={stdout:?} stderr={stderr:?}",
        output.status
    ))
}
