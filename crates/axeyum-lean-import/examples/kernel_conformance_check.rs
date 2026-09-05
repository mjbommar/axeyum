//! Check **one** case of the public Lean Kernel Arena conformance corpus with
//! this kernel, using the arena's own checker contract.
//!
//! The corpus is `leanprover/lean-kernel-arena` (<https://arena.lean-lang.org>);
//! its published tarball unpacks into `good/` (the official kernel accepts) and
//! `bad/` (the official kernel rejects) subtrees of `lean4export` NDJSON.
//! `scripts/check-kernel-conformance.py` drives this binary once per case, with
//! a per-case timeout, and scores the two halves separately.
//!
//! One case per process is deliberate. The arena's own performance cases are
//! built to make a checker diverge, and an in-process sweep has no way to bound
//! one of them: a wedged case would take the whole run with it and the harness
//! could not report which case wedged. A `timeout` around a child process can.
//!
//! **Exit codes** are the arena's external-checker contract verbatim:
//!
//! | code | meaning | produced by |
//! |---|---|---|
//! | 0 | accepted | `Ok(_)` |
//! | 1 | rejected | [`ImportError::Kernel`] (full mode only), `Malformed`, `Json` |
//! | 2 | declined — cannot judge | [`ImportError::Unsupported`] |
//! | 3 | error in the checker | `Io`, `LineLimit`, `RecordLimit`, bad usage |
//!
//! A decline is not a reject: it is a refusal to judge, and the gate scores it
//! in its own column so it can never be hidden inside a pass rate.
//!
//! **Two modes, and the second is the control.**
//!
//! - `--mode full` uses [`import_ndjson`]: parse the stream *and* put every
//!   declaration through the trusted gate.
//! - `--mode parse-only` uses [`census_ndjson`], which reads the identical bytes
//!   with the identical reader but **records kernel declines instead of failing
//!   on them**. That is the arena's own `parse-only` control reproduced in-tree:
//!   a checker that accepts everything it can parse. It must score near-perfectly
//!   on the accept half and badly on the reject half. If it does not score badly
//!   on the reject half, this harness is not measuring the kernel at all and the
//!   `full` numbers mean nothing.
//!
//! Usage:
//!
//! ```text
//! kernel_conformance_check [--mode full|parse-only] <case.ndjson>
//! ```

use std::fmt::Write as _;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::process::ExitCode;

use axeyum_lean_import::{ImportError, ImportLimits, census_ndjson, import_ndjson};

/// Arena checker exit code: accepted.
const EXIT_ACCEPT: u8 = 0;
/// Arena checker exit code: rejected.
const EXIT_REJECT: u8 = 1;
/// Arena checker exit code: declined (the checker cannot handle this input).
const EXIT_DECLINE: u8 = 2;
/// Arena checker exit code: an error in the checker itself.
const EXIT_ERROR: u8 = 3;

fn main() -> ExitCode {
    let (verdict, class, detail) = match run() {
        Ok(triple) => triple,
        Err(message) => (EXIT_ERROR, "usage".to_owned(), sanitize(&message)),
    };
    println!("KERNEL-CONFORMANCE-CASE verdict={verdict} class={class} detail={detail}");
    ExitCode::from(verdict)
}

fn run() -> Result<(u8, String, String), String> {
    let mut path: Option<PathBuf> = None;
    let mut parse_only = false;
    let mut arguments = std::env::args().skip(1);
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--mode" => {
                parse_only = match arguments.next().as_deref() {
                    Some("full") => false,
                    Some("parse-only") => true,
                    other => return Err(format!("unknown --mode {other:?}")),
                };
            }
            other if other.starts_with("--") => return Err(format!("unknown argument {other}")),
            other => {
                if path.replace(PathBuf::from(other)).is_some() {
                    return Err("exactly one case path is accepted".to_owned());
                }
            }
        }
    }
    let path = path.ok_or_else(|| {
        "usage: kernel_conformance_check [--mode full|parse-only] <case.ndjson>".to_owned()
    })?;
    let file = File::open(&path).map_err(|error| format!("{}: {error}", path.display()))?;
    let reader = BufReader::new(file);
    let outcome = if parse_only {
        census_ndjson(reader, ImportLimits::default()).map(|_| ())
    } else {
        import_ndjson(reader, ImportLimits::default()).map(|_| ())
    };
    Ok(match outcome {
        Ok(()) => (EXIT_ACCEPT, "ok".to_owned(), "-".to_owned()),
        Err(error) => classify(&error),
    })
}

fn classify(error: &ImportError) -> (u8, String, String) {
    let (verdict, class) = match error {
        ImportError::Kernel { source, .. } => (EXIT_REJECT, kernel_class(source)),
        ImportError::Malformed { .. } => (EXIT_REJECT, "malformed".to_owned()),
        ImportError::Json { .. } => (EXIT_REJECT, "json".to_owned()),
        ImportError::Unsupported { code, .. } => (EXIT_DECLINE, format!("unsupported:{code}")),
        ImportError::Io(_) => (EXIT_ERROR, "io".to_owned()),
        ImportError::LineLimit { .. } => (EXIT_ERROR, "line_limit".to_owned()),
        ImportError::RecordLimit { .. } => (EXIT_ERROR, "record_limit".to_owned()),
    };
    (verdict, class, sanitize(&format!("{error}")))
}

/// The leading identifier of the kernel error's `Debug` rendering. `KernelError`
/// has fifty-plus variants owned by another crate, so an exhaustive match here
/// would be a maintenance trap that fails closed on the wrong side; this mirrors
/// the cluster key `axeyum-lean-import`'s own census already uses.
fn kernel_class(source: &axeyum_lean_kernel::KernelError) -> String {
    let rendered = format!("{source:?}");
    let head: String = rendered
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .collect();
    format!("kernel:{head}")
}

/// One field of one whitespace-separated record: collapse everything that would
/// break the line format, and bound the length so a single pathological message
/// cannot dominate the artifact.
fn sanitize(text: &str) -> String {
    let mut out = String::new();
    for c in text.chars().take(200) {
        if c.is_whitespace() || c == '|' {
            out.push('_');
        } else {
            let _ = write!(out, "{c}");
        }
    }
    if out.is_empty() { "-".to_owned() } else { out }
}
