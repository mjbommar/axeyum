//! Killable process boundary for whole-call `QF_BV` certificate work.
//!
//! The in-memory certificate API has a cooperative proof-search deadline, but
//! lowering, encoding, and completed-proof checking deliberately run to
//! completion. Publication evidence that claims a hard wall bound therefore
//! runs the complete parse -> construct -> prove -> self-recheck route in a
//! child copy of the same executable. The parent can kill and reap that child
//! without dropping the selected UNSAT row from the denominator.

use std::ffi::OsString;
use std::fs;
use std::io;
use std::path::Path;
use std::process::{Child, Command, ExitCode, Output, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{EndToEndUnsatOutcome, certify_qf_bv_unsat_end_to_end_within};
use serde_json::{Value as JsonValue, json};
use sha2::{Digest, Sha256};

const WORKER_FLAG: &str = "--qfbv-certificate-worker";
const WORKER_PROTOCOL: &str = "axeyum-qfbv-certificate-worker-v1";
const HASH_PREFIX: &str = "sha256:";
const POLL_INTERVAL: Duration = Duration::from_millis(1);
const MAX_DIAGNOSTIC_BYTES: usize = 4096;

/// Parent-side classification of a completed or terminated worker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IsolatedStatus {
    Certified,
    NotCertified,
    SatisfiableContradiction,
    RecheckFailed,
    Error,
}

/// Result of one whole-call process-isolated certification attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IsolatedResult {
    pub(crate) status: IsolatedStatus,
    pub(crate) detail: Option<String>,
    pub(crate) hard_timeout: bool,
}

enum WaitOutcome {
    Completed(Output),
    TimedOut(Output),
}

/// Handles the private worker protocol before normal benchmark CLI parsing.
///
/// Returning `None` means this is an ordinary `axeyum-bench` invocation.
pub(crate) fn maybe_worker_main() -> Option<ExitCode> {
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() != Some(std::ffi::OsStr::new(WORKER_FLAG)) {
        return None;
    }
    let remaining = args.collect::<Vec<_>>();
    Some(worker_main(&remaining))
}

/// Runs the complete certificate call in a killable child process.
pub(crate) fn certify_file_isolated(
    file: &Path,
    expected_source_hash: &str,
    cooperative_deadline: Duration,
    process_timeout: Duration,
) -> IsolatedResult {
    let started = Instant::now();
    let executable = match std::env::current_exe() {
        Ok(value) => value,
        Err(error) => return isolated_error(format!("resolve current executable: {error}")),
    };
    let mut command = Command::new(executable);
    command
        .arg(WORKER_FLAG)
        .arg(file)
        .arg(expected_source_hash)
        .arg(cooperative_deadline.as_millis().to_string())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let child = match command.spawn() {
        Ok(value) => value,
        Err(error) => return isolated_error(format!("spawn certificate worker: {error}")),
    };
    let remaining = process_timeout.saturating_sub(started.elapsed());
    match wait_with_timeout(child, remaining) {
        Ok(WaitOutcome::TimedOut(output)) => IsolatedResult {
            status: IsolatedStatus::NotCertified,
            detail: Some(timeout_detail(&output)),
            hard_timeout: true,
        },
        Ok(WaitOutcome::Completed(output)) => parse_worker_output(&output),
        Err(error) => isolated_error(format!("wait for certificate worker: {error}")),
    }
}

fn worker_main(args: &[OsString]) -> ExitCode {
    let result = worker_result(args);
    println!(
        "{}",
        json!({
            "protocol": WORKER_PROTOCOL,
            "status": result.status,
            "self_rechecked": result.self_rechecked,
            "detail": result.detail,
        })
    );
    ExitCode::SUCCESS
}

struct WorkerResult {
    status: &'static str,
    self_rechecked: bool,
    detail: Option<String>,
}

fn worker_result(args: &[OsString]) -> WorkerResult {
    if args.len() != 3 {
        return worker_error(format!(
            "worker protocol expected file, source hash, and deadline; got {} fields",
            args.len()
        ));
    }
    let file = Path::new(&args[0]);
    let expected_hash = match args[1].to_str() {
        Some(value) if value.starts_with(HASH_PREFIX) => value,
        _ => return worker_error("worker received an invalid source hash".to_owned()),
    };
    let deadline_ms = match args[2].to_str().and_then(|value| value.parse::<u64>().ok()) {
        Some(value) if value > 0 => value,
        _ => return worker_error("worker received an invalid cooperative deadline".to_owned()),
    };
    let source = match fs::read(file) {
        Ok(value) => value,
        Err(error) => return worker_error(format!("read {}: {error}", file.display())),
    };
    let actual_hash = content_hash(&source);
    if actual_hash != expected_hash {
        return worker_error(format!(
            "source identity changed before certification: expected {expected_hash}, got {actual_hash}"
        ));
    }
    let text = match std::str::from_utf8(&source) {
        Ok(value) => value,
        Err(error) => return worker_error(format!("{} is not UTF-8: {error}", file.display())),
    };
    let script = match parse_script(text) {
        Ok(value) => value,
        Err(error) => return worker_error(format!("parse {}: {error}", file.display())),
    };
    if script.commands.iter().any(|command| {
        matches!(command, ScriptCommand::CheckSatAssuming(assumptions) if !assumptions.is_empty())
    }) {
        return worker_error(
            "check-sat-assuming assumptions are not represented by the flat assertion view"
                .to_owned(),
        );
    }
    if script.assertions.is_empty() && source_has_constraints(text) {
        return worker_error(
            "flat assertion view is empty despite constraint-bearing source text".to_owned(),
        );
    }

    let deadline = Instant::now() + Duration::from_millis(deadline_ms);
    match certify_qf_bv_unsat_end_to_end_within(&script.arena, &script.assertions, Some(deadline)) {
        Ok(outcome @ EndToEndUnsatOutcome::Certified { .. }) => match outcome.recheck() {
            Ok(true) => WorkerResult {
                status: "certified",
                self_rechecked: true,
                detail: None,
            },
            Ok(false) => WorkerResult {
                status: "recheck-failed",
                self_rechecked: false,
                detail: Some(
                    "certificate text did not independently re-derive both refutations".to_owned(),
                ),
            },
            Err(error) => WorkerResult {
                status: "recheck-failed",
                self_rechecked: false,
                detail: Some(format!("certificate recheck error: {error}")),
            },
        },
        Ok(EndToEndUnsatOutcome::NotCertified) => WorkerResult {
            status: "not-certified",
            self_rechecked: false,
            detail: Some("cooperative proof-search deadline or uncovered operation".to_owned()),
        },
        Ok(EndToEndUnsatOutcome::Satisfiable) => WorkerResult {
            status: "satisfiable-contradiction",
            self_rechecked: false,
            detail: Some("end-to-end route returned satisfiable after primary UNSAT".to_owned()),
        },
        Err(error) => worker_error(error.to_string()),
    }
}

fn wait_with_timeout(mut child: Child, timeout: Duration) -> io::Result<WaitOutcome> {
    let deadline = Instant::now() + timeout;
    loop {
        if child.try_wait()?.is_some() {
            return child.wait_with_output().map(WaitOutcome::Completed);
        }
        let now = Instant::now();
        if now >= deadline {
            // `kill` can race with a just-exited worker. In either case, reap it;
            // the parent deadline has expired, so no late output earns credit.
            let _ = child.kill();
            return child.wait_with_output().map(WaitOutcome::TimedOut);
        }
        thread::sleep(POLL_INTERVAL.min(deadline.saturating_duration_since(now)));
    }
}

fn parse_worker_output(output: &Output) -> IsolatedResult {
    if !output.status.success() {
        return isolated_error(format!(
            "certificate worker exited with {}: {}",
            output.status,
            diagnostic(&output.stderr)
        ));
    }
    let stdout = match std::str::from_utf8(&output.stdout) {
        Ok(value) => value.trim(),
        Err(error) => return isolated_error(format!("worker stdout is not UTF-8: {error}")),
    };
    let value: JsonValue = match serde_json::from_str(stdout) {
        Ok(value) => value,
        Err(error) => {
            return isolated_error(format!(
                "worker emitted invalid protocol JSON: {error}; stdout={}",
                diagnostic(&output.stdout)
            ));
        }
    };
    if value.get("protocol").and_then(JsonValue::as_str) != Some(WORKER_PROTOCOL) {
        return isolated_error("worker protocol identity mismatch".to_owned());
    }
    let status = value.get("status").and_then(JsonValue::as_str);
    let self_rechecked = value
        .get("self_rechecked")
        .and_then(JsonValue::as_bool)
        .unwrap_or(false);
    let detail = value
        .get("detail")
        .and_then(JsonValue::as_str)
        .map(ToOwned::to_owned);
    let status = match status {
        Some("certified") if self_rechecked => IsolatedStatus::Certified,
        Some("certified") => {
            return isolated_error("worker claimed certified without self-recheck".to_owned());
        }
        Some("not-certified") => IsolatedStatus::NotCertified,
        Some("satisfiable-contradiction") => IsolatedStatus::SatisfiableContradiction,
        Some("recheck-failed") => IsolatedStatus::RecheckFailed,
        Some("error") => IsolatedStatus::Error,
        Some(other) => return isolated_error(format!("unknown worker status `{other}`")),
        None => return isolated_error("worker status is missing".to_owned()),
    };
    IsolatedResult {
        status,
        detail,
        hard_timeout: false,
    }
}

fn source_has_constraints(text: &str) -> bool {
    text.contains("(assert") || text.contains("(constraint") || text.contains("check-sat-assuming")
}

fn content_hash(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let digest = Sha256::digest(bytes);
    let mut encoded = String::with_capacity(HASH_PREFIX.len() + digest.len() * 2);
    encoded.push_str(HASH_PREFIX);
    for byte in digest {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn timeout_detail(output: &Output) -> String {
    let stderr = diagnostic(&output.stderr);
    if stderr.is_empty() {
        "hard whole-certificate process timeout; worker killed and reaped".to_owned()
    } else {
        format!("hard whole-certificate process timeout; worker killed and reaped; stderr={stderr}")
    }
}

fn diagnostic(bytes: &[u8]) -> String {
    let length = bytes.len().min(MAX_DIAGNOSTIC_BYTES);
    String::from_utf8_lossy(&bytes[..length]).trim().to_owned()
}

fn worker_error(detail: String) -> WorkerResult {
    WorkerResult {
        status: "error",
        self_rechecked: false,
        detail: Some(detail),
    }
}

fn isolated_error(detail: String) -> IsolatedResult {
    IsolatedResult {
        status: IsolatedStatus::Error,
        detail: Some(detail),
        hard_timeout: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn certified_protocol_requires_explicit_self_recheck() {
        let output = |self_rechecked| Output {
            status: success_status(),
            stdout: serde_json::to_vec(&json!({
                "protocol": WORKER_PROTOCOL,
                "status": "certified",
                "self_rechecked": self_rechecked,
                "detail": null,
            }))
            .unwrap(),
            stderr: Vec::new(),
        };
        assert_eq!(
            parse_worker_output(&output(true)).status,
            IsolatedStatus::Certified
        );
        assert_eq!(
            parse_worker_output(&output(false)).status,
            IsolatedStatus::Error
        );
    }

    #[cfg(unix)]
    #[test]
    fn hard_timeout_kills_and_reaps_child() {
        let child = Command::new("sleep")
            .arg("30")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let started = Instant::now();
        let outcome = wait_with_timeout(child, Duration::from_millis(5)).unwrap();
        assert!(matches!(outcome, WaitOutcome::TimedOut(_)));
        assert!(started.elapsed() < Duration::from_secs(2));
    }

    #[cfg(unix)]
    fn success_status() -> std::process::ExitStatus {
        use std::os::unix::process::ExitStatusExt;
        std::process::ExitStatus::from_raw(0)
    }

    #[cfg(windows)]
    fn success_status() -> std::process::ExitStatus {
        use std::os::windows::process::ExitStatusExt;
        std::process::ExitStatus::from_raw(0)
    }
}
