//! Shared cvc5 differential-oracle helper for the string/word test suites.
//!
//! cvc5 is provisioned as a **second** differential oracle (alongside the system
//! Z3 binary) because Z3-only validation is weakest exactly on strings, and the
//! committed string corpora are cvc5 regressions. This module resolves the cvc5
//! binary and shells SMT-LIB 2 text through it, parsing a coarse sat/unsat/skip
//! verdict.
//!
//! Provisioning (recorded for reproducibility):
//!   - binary: official static release `cvc5-Linux-x86_64-static.zip`
//!     (cvc5 1.3.4, `git f3b21c4`) from
//!     <https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-Linux-x86_64-static.zip>,
//!     installed at `~/.local/bin/cvc5` (a fully static, no-shared-lib binary).
//!   - flags: `--lang smt2 --strings-exp` (extended string functions on) with a
//!     per-invocation `--tlimit=<ms>` wall-clock budget; the text is piped on
//!     stdin (cvc5 solves stdin when given no file argument).
//!
//! Absence is a **SKIP, not a failure**: CI without cvc5 stays green. The binary
//! is resolved once via [`cvc5_bin`]; callers thread the resolved path into
//! [`cvc5_decide`].

#![allow(dead_code)]

use std::io::Write as _;
use std::process::{Command, Stdio};
use std::time::Duration;

/// A coarse verdict label shared with the Z3 oracle harness.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Verdict {
    Sat,
    Unsat,
    /// Unknown / unsupported / declined / timeout / parse-error — neutral.
    Skip,
}

/// Detailed cvc5 outcome for gates where a valid generated script must not
/// hide a parser/process failure inside an adjudication-neutral timeout.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum DetailedVerdict {
    Sat,
    Unsat,
    /// cvc5 explicitly returned `unknown` (normally its resource limit).
    Unknown,
    /// Spawn, I/O, exit-status, or output-protocol failure.
    Failure(String),
}

/// Resolve the cvc5 binary path, or `None` if cvc5 is unavailable.
///
/// Tries `AXEYUM_CVC5_BIN`, `cvc5` on `PATH`, then the conventional user
/// install location `~/.local/bin/cvc5`. A binary is accepted only if
/// `--version` exits cleanly, so a broken drop-in is treated as absent.
pub fn cvc5_bin() -> Option<String> {
    let responds = |bin: &str| -> bool {
        Command::new(bin)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|s| s.success())
    };

    if let Ok(bin) = std::env::var("AXEYUM_CVC5_BIN") {
        return responds(&bin).then_some(bin);
    }
    if responds("cvc5") {
        return Some("cvc5".to_string());
    }
    if let Ok(home) = std::env::var("HOME") {
        let p = format!("{home}/.local/bin/cvc5");
        if responds(&p) {
            return Some(p);
        }
    }
    None
}

/// Decide a script by piping the text to the cvc5 binary on stdin.
///
/// Runs `<bin> --lang smt2 --strings-exp --tlimit=<ms>` and reads the first
/// `sat` / `unsat` / `unknown` token on stdout. Any spawn/IO/parse error, an
/// `unknown`, or an `(error …)` (e.g. an unsupported `set-logic` such as
/// `QF_SEQ`) is an adjudication-neutral [`Verdict::Skip`]. A Rust-side kill
/// backstops cvc5's internal `--tlimit` in case the process wedges before
/// solving.
pub fn cvc5_decide(bin: &str, text: &str, timeout: Duration) -> Verdict {
    match cvc5_decide_detailed(bin, text, timeout) {
        DetailedVerdict::Sat => Verdict::Sat,
        DetailedVerdict::Unsat => Verdict::Unsat,
        DetailedVerdict::Unknown | DetailedVerdict::Failure(_) => Verdict::Skip,
    }
}

/// Decide a script while preserving explicit `unknown` versus process/parser
/// failure. Existing string fuzzers use [`cvc5_decide`]'s conservative coarse
/// contract; publication-grade generated-input gates use this function and
/// fail closed on [`DetailedVerdict::Failure`].
pub fn cvc5_decide_detailed(bin: &str, text: &str, timeout: Duration) -> DetailedVerdict {
    let tlimit_ms = timeout.as_millis().max(1);
    let mut child = match Command::new(bin)
        .arg("--lang")
        .arg("smt2")
        .arg("--strings-exp")
        .arg(format!("--tlimit={tlimit_ms}"))
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
