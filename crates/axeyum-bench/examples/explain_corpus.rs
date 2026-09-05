//! Per-file `check_auto_explained` probe for a corpus directory or exact list.
//!
//! This complements `measure_corpus`: the measured aggregate is the scoreboard,
//! while this probe shows which files moved and which route declined.
//!
//! ```text
//! cargo run -p axeyum-bench --example explain_corpus -- <dir> [timeout_ms] [--json] [--timed-trace]
//! cargo run -p axeyum-bench --example explain_corpus -- --list <file> [timeout_ms] [--json] [--timed-trace]
//! ```
//!
//! With `--json` the probe emits one JSON object per line (JSONL) instead of
//! prose, embedding the route trace via
//! [`RouteTrace::to_json`](axeyum_solver::route_trace::RouteTrace::to_json).
//! That is the persistable form the bridge-catalogue replay validator consumes:
//! it needs the observed dispatch order as data, not as `Display` text.
//!
//! `--timed-trace` (JSON mode only; a no-op without `--json`) switches the
//! embedded trace to
//! [`RouteTrace::to_json_with_timing`](axeyum_solver::route_trace::RouteTrace::to_json_with_timing),
//! which adds an `"elapsed_ns"` member to each attempt. This is what makes a
//! declined route's cost visible instead of just its outcome — the answer to
//! "where did the 24 s go" the 2026-08-21 linear-arithmetic diagnosis had to
//! reconstruct by hand from per-file TSVs because this instrument did not
//! exist yet. Off by default so every existing committed JSONL artifact
//! (which pins `trace` to the plain `to_json` schema) stays reproducible.
//!
//! In directory mode `file` remains the historical basename. In exact-list
//! mode it is the complete list entry, so a trace can be joined to a committed
//! benchmark population without basename ambiguity. Every line has `file` and
//! `status`; `status` is one of `decided`,
//! `word-first-fallback`, `ingest-unsupported`, `ingest-resource-limit`,
//! `skipped-scoped`, `read-error`, `parse-error`, or `error`. `verdict` is
//! present on the decided statuses and typed ingest records. `trace` is present
//! only on `decided`; the narrow ADR-0376 wide-integer `ingest-unsupported`
//! class instead carries explicit `route`/`reason`/`kind` terminal provenance
//! because solver dispatch never began. `detail` is present on typed ingest and
//! error records.

use std::collections::BTreeSet;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use axeyum_smtlib::{SmtError, parse_script};
use axeyum_solver::route_trace::push_json_string;
use axeyum_solver::{CheckResult, SolverConfig, check_auto_explained, solve_smtlib};

const WORKER_IDENTITY_ENV: &str = "AXEYUM_EXPLAIN_CORPUS_IDENTITY";
const WORKER_FILE_FLAG: &str = "--__worker-file";

fn collect_smt2(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            collect_smt2(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "smt2") {
            out.push(path);
        }
    }
}

fn read_exact_list(path: &Path) -> Result<Vec<PathBuf>, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("cannot read list {}: {error}", path.display()))?;
    let mut seen = BTreeSet::new();
    let mut files = Vec::new();
    for (index, raw) in text.lines().enumerate() {
        let entry = raw.trim();
        if entry.is_empty() {
            continue;
        }
        let file = PathBuf::from(entry);
        if file.extension().is_none_or(|extension| extension != "smt2") {
            return Err(format!(
                "{}:{} is not an .smt2 path: {entry}",
                path.display(),
                index + 1
            ));
        }
        if !file.is_file() {
            return Err(format!(
                "{}:{} does not name a file: {entry}",
                path.display(),
                index + 1
            ));
        }
        if !seen.insert(file.clone()) {
            return Err(format!(
                "{}:{} duplicates an earlier path: {entry}",
                path.display(),
                index + 1
            ));
        }
        files.push(file);
    }
    if files.is_empty() {
        return Err(format!("list {} contains no benchmarks", path.display()));
    }
    Ok(files)
}

/// A solver verdict, stripped of its payload.
///
/// The token and refusal logic below is keyed on this rather than on
/// [`CheckResult`] so it is a pure function of three values -- `CheckResult`'s
/// `Unknown` and `Sat` payloads are `#[non_exhaustive]` and cannot be built
/// outside `axeyum-solver`, which would have left this module's decisions
/// testable only through a solver call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Bare {
    Sat,
    Unsat,
    Unknown,
}

impl Bare {
    fn of(result: &CheckResult) -> Self {
        match result {
            CheckResult::Sat(_) => Self::Sat,
            CheckResult::Unsat => Self::Unsat,
            CheckResult::Unknown(_) => Self::Unknown,
        }
    }

    /// The bare SMT-LIB token. Used ONLY to render `front_door_verdict` under
    /// `--confirm`, which really is `solve_smtlib`'s answer. Everything this
    /// tool says on its own behalf goes through [`flat_token`].
    fn label(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
        }
    }
}

/// The token this tool prints for a verdict its **flat** route produced.
///
/// NOT `sat` / `unsat` / `unknown`, on purpose, and this is the whole fix.
///
/// `check_auto_explained` decides the flat assertion view. The shipped front
/// door is `solve_smtlib`, which applies the ADR-0052 `StringGate`, the word /
/// online / membership routes, and the multi-`check-sat` lifecycle on top of
/// it. Those are not the same function and they do not agree. Measured
/// 2026-08-21 over 397 committed benchmarks (`quantified/{BV,LIA,UF}`, `QF_S`,
/// `QF_SLIA`, `QF_LIA`, `QF_UF`, `QF_NRA`, 5 s cap, both binaries built from
/// the same commit), **134 of 397 disagreed** — 33.8%:
///
/// ```text
///  71  this tool ERRORS on a query the front door DECIDES (41 sat, 30 unsat)
///  46  this tool printed `unsat-UNCONFIRMED`; the front door says unsat 30,
///      unknown 13, and **sat 3**
///  17  this tool says `unknown`; the front door decides (9 unsat, 8 sat)
/// ```
///
/// and in the other direction, a two-`check-sat` script the front door refuses
/// outright (`solve_smtlib` is single-query) was flattened here into one
/// conjunction and answered — `(assert (> x 0)) (check-sat) (assert (< x 0))
/// (check-sat)` printed `unsat`, which is not the answer to either query in the
/// file.
///
/// **The obvious way to measure this over-counts, by 59.** Comparing against
/// the `smtcomp_cli` binary instead of against `solve_smtlib` scores 193, not
/// 134, because SMT-COMP §7.1.2 requires the CLI to print `unknown` for an
/// error — so 58 files this tool reports `parse-error` on, which
/// `solve_smtlib` also rejects, look from outside like "it failed where the
/// front door answered". They are both sides declining, which
/// [`agrees_with_front_door`] counts as agreement. Running the comparison
/// INSIDE the process (`--confirm`) is what distinguishes them; that is most of
/// why the flag exists.
///
/// CLAUDE.md has said "never use it as an oracle" since a fabricated `unsat`
/// became the foundation of a whole lever. A doc comment did not stop that, and
/// the output line is what people read. So the output line now says it: no
/// verdict this tool emits can be `grep -x`'d as an SMT-LIB answer, and the
/// shapes where the divergence is structural are refused instead of answered.
fn flat_token(result: Bare) -> &'static str {
    match result {
        Bare::Sat => "flat-sat",
        Bare::Unsat => "flat-unsat",
        Bare::Unknown => "flat-unknown",
    }
}

/// The token for a verdict that came from `solve_smtlib` — the real front door
/// — which the word-first fallback path uses. Still prefixed: one field with
/// two provenances and no marking is how a diagnostic gets quoted as an answer.
fn front_door_token(result: Bare) -> &'static str {
    match result {
        Bare::Sat => "front-door-sat",
        Bare::Unsat => "front-door-unsat",
        Bare::Unknown => "front-door-unknown",
    }
}

/// No route ran, so there is no verdict — not even `unknown`, which is a
/// solver answer and would be a claim this tool did not earn.
const NOT_ATTEMPTED: &str = "not-attempted";

/// Why this tool declines to print a verdict for a script at all.
///
/// Refusing is the half of the fix that a label cannot do. A prefixed token
/// still invites "well, `flat-unsat` probably means unsat"; on these two shapes
/// it demonstrably does not, so there is nothing to print.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Refusal {
    /// `solve_smtlib` refuses a script with more than one `check-sat`
    /// (`smtlib_single_query`: "use `solve_smtlib_incremental`"). The flat view
    /// has no such notion: it conjoins every assertion in the file and answers
    /// the query that results, which is not any `check-sat` in the script.
    MultiCheckSat,
    /// A bounded-string script whose flat route says `unsat`. The front door
    /// runs `StringGate::confirm`, which downgrades a bounded-encoding `unsat`
    /// when bound-independence is not established. This tool used to print
    /// `unsat-UNCONFIRMED` here — a verdict with a caveat is still a verdict,
    /// and on 3 of the 46 files that printed it the front door returns `sat`.
    StringGateUnconfirmed,
}

impl Refusal {
    fn status(self) -> &'static str {
        match self {
            Refusal::MultiCheckSat => "refused-multi-check-sat",
            Refusal::StringGateUnconfirmed => "refused-string-gate-unconfirmed",
        }
    }

    fn reason(self) -> &'static str {
        match self {
            Refusal::MultiCheckSat => {
                "the flat view conjoins every assertion; solve_smtlib refuses a \
                 multi-check-sat script and this tool must not answer a query the file \
                 does not ask"
            }
            Refusal::StringGateUnconfirmed => {
                "bounded-string unsat is not confirmed without ADR-0052 StringGate::confirm, \
                 which the flat route bypasses; the front door decides some of these sat"
            }
        }
    }
}

/// Whether a script must be refused BEFORE any route runs.
fn pre_solve_refusal(check_sats: u32) -> Option<Refusal> {
    (check_sats > 1).then_some(Refusal::MultiCheckSat)
}

/// Whether a flat-route verdict must be withheld AFTER the route ran.
fn post_solve_refusal(result: Bare, uses_bounded_strings: bool) -> Option<Refusal> {
    // Only the `unsat` direction is at risk: the gate downgrades a bounded
    // `unsat`, it never promotes a `sat`.
    (uses_bounded_strings && result == Bare::Unsat).then_some(Refusal::StringGateUnconfirmed)
}

/// Emits one JSONL record. `extra` is pre-rendered JSON (already-escaped
/// members such as `"verdict":"sat","trace":{…}`) appended verbatim; only the
/// caller-supplied `file` and `status` are escaped here, using the solver's own
/// escaper so this example cannot drift from `RouteTrace::to_json`.
fn emit_json(file: &str, status: &str, extra: &str) {
    let mut line = String::from("{\"file\":");
    push_json_string(&mut line, file);
    line.push_str(",\"status\":");
    push_json_string(&mut line, status);
    // Structural, on EVERY record, including the error and refusal ones. A
    // consumer that filters on it cannot accidentally treat this stream as a
    // verdict source, and a reader who greps one line still sees it.
    line.push_str(",\"oracle\":false,\"front_door\":\"solve_smtlib\"");
    line.push_str(extra);
    line.push('}');
    println!("{line}");
}

/// Do this tool and the front door agree about a file?
///
/// Both declining IS agreement -- a multi-`check-sat` script that this tool
/// refuses and `solve_smtlib` rejects as unsupported is the two of them saying
/// the same thing. Calling that a divergence would bury the divergences that
/// matter under the ones the fix created.
fn agrees_with_front_door(front_door: &Result<Bare, String>, flat: Option<Bare>) -> bool {
    match (front_door, flat) {
        (Ok(front), Some(flat)) => *front == flat,
        // This tool produced no verdict and neither did the front door.
        (Err(_), None) => true,
        // One of them answered and the other did not: the asymmetry that reads
        // as "axeyum cannot do this" when it can.
        _ => false,
    }
}

/// Renders `,"front_door_verdict":"…","agrees":bool` under `--confirm`.
///
/// `front_door_verdict` carries the BARE SMT-LIB token on purpose: it is
/// `solve_smtlib`'s answer, the one thing in this stream that is authoritative.
/// `agrees` is false whenever the two differ at all, including when this tool
/// refused or errored and the front door decided — that asymmetry is 71 of the
/// 193 divergences and reads as "axeyum cannot do this", which is false.
fn confirm_member(front_door: &Result<Bare, String>, flat: Option<Bare>) -> String {
    let mut out = String::from(",\"front_door_verdict\":");
    let agrees = agrees_with_front_door(front_door, flat);
    match front_door {
        Ok(result) => push_json_string(&mut out, result.label()),
        Err(error) => {
            push_json_string(&mut out, "error");
            out.push_str(",\"front_door_error\":");
            push_json_string(&mut out, error);
        }
    }
    out.push_str(if agrees {
        ",\"agrees\":true"
    } else {
        ",\"agrees\":false"
    });
    out
}

/// Renders `,"refusal":"…"` for a refused record.
fn refusal_member(refusal: Refusal) -> String {
    let mut out = String::from(",\"verdict\":\"");
    out.push_str(NOT_ATTEMPTED);
    out.push_str("\",\"refusal\":");
    push_json_string(&mut out, refusal.reason());
    out
}

/// Renders `,"detail":"…"` for an error record.
fn detail_member(detail: &str) -> String {
    let mut out = String::from(",\"detail\":");
    push_json_string(&mut out, detail);
    out
}

/// Recognizes only ADR-0376's valid-but-unrepresentable wide integer literal.
/// Other unsupported input remains a generic parse error and cannot silently
/// enter a corpus census as this narrower, understood class.
fn is_wide_integer_unsupported(detail: &str) -> bool {
    const PREFIX: &str = "integer literal `";
    const SUFFIX: &str = "` exceeds the modeled `Int` range";
    detail
        .strip_prefix(PREFIX)
        .and_then(|rest| rest.strip_suffix(SUFFIX))
        .is_some_and(|digits| {
            !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn validate_worker_output(
    stdout: &[u8],
    stderr: &[u8],
    identity: &str,
    json: bool,
) -> Result<(), String> {
    if !stderr.is_empty() {
        return Err(format!(
            "worker for {identity} emitted {} stderr bytes: {}",
            stderr.len(),
            String::from_utf8_lossy(stderr).trim()
        ));
    }
    if stdout.is_empty() {
        return Err(format!("worker for {identity} emitted no output"));
    }
    if !json {
        return Ok(());
    }
    let text = std::str::from_utf8(stdout)
        .map_err(|error| format!("worker for {identity} emitted non-UTF-8 JSON: {error}"))?;
    let mut lines = text.lines();
    let line = lines
        .next()
        .ok_or_else(|| format!("worker for {identity} emitted no JSON record"))?;
    if lines.next().is_some() {
        return Err(format!(
            "worker for {identity} emitted more than one JSON record"
        ));
    }
    let record: serde_json::Value = serde_json::from_str(line)
        .map_err(|error| format!("worker for {identity} emitted malformed JSON: {error}"))?;
    if record.get("file").and_then(serde_json::Value::as_str) != Some(identity) {
        return Err(format!(
            "worker for {identity} emitted a different file identity"
        ));
    }
    Ok(())
}

fn run_isolated_file(
    path: &Path,
    identity: &str,
    timeout_ms: u64,
    json: bool,
    confirm: bool,
    timed_trace: bool,
) -> Result<Vec<u8>, String> {
    let executable = std::env::current_exe()
        .map_err(|error| format!("cannot locate explain_corpus executable: {error}"))?;
    let mut command = Command::new(executable);
    command
        .env(WORKER_IDENTITY_ENV, identity)
        .arg(WORKER_FILE_FLAG)
        .arg(path)
        .arg(timeout_ms.to_string());
    if json {
        command.arg("--json");
    }
    if confirm {
        command.arg("--confirm");
    }
    if timed_trace {
        command.arg("--timed-trace");
    }
    let output = command
        .output()
        .map_err(|error| format!("cannot start worker for {identity}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "worker for {identity} exited {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    validate_worker_output(&output.stdout, &output.stderr, identity, json)?;
    Ok(output.stdout)
}

#[allow(clippy::too_many_lines)] // linear CLI driver: arg parsing + per-file loop + summary
fn main() {
    let raw: Vec<String> = std::env::args().collect();
    // `--json` may appear anywhere; strip it before positional parsing so the
    // existing `<dir> [timeout_ms]` call sites keep working unchanged.
    let json = raw.iter().any(|arg| arg == "--json");
    // Cross-check every file against `solve_smtlib` in the same process and
    // stamp whether the two agree. OFF by default because it re-solves each
    // file (measured 39 s -> ~2x on a 397-file sweep), but it is the mode that
    // makes this tool self-measuring: the divergence census in `flat_token`'s
    // comment is what it prints.
    let confirm = raw.iter().any(|arg| arg == "--confirm");
    // Embeds `RouteTrace::to_json_with_timing` instead of the default
    // `to_json` (see the module docs). A no-op without `--json`.
    let timed_trace = raw.iter().any(|arg| arg == "--timed-trace");
    let args: Vec<String> = raw
        .into_iter()
        .filter(|arg| arg != "--json" && arg != "--confirm" && arg != "--timed-trace")
        .collect();
    let usage = "usage: explain_corpus <dir> [timeout_ms] [--json] [--confirm] [--timed-trace]\n       explain_corpus --list <file> [timeout_ms] [--json] [--confirm] [--timed-trace]";
    let exact_list = args.get(1).is_some_and(|arg| arg == "--list");
    let single_file = args.get(1).is_some_and(|arg| arg == WORKER_FILE_FLAG);
    let (input, timeout_arg) = if exact_list || single_file {
        let Some(path) = args.get(2) else {
            eprintln!("{usage}");
            std::process::exit(2);
        };
        (PathBuf::from(path), args.get(3))
    } else {
        let Some(path) = args.get(1) else {
            eprintln!("{usage}");
            std::process::exit(2);
        };
        (PathBuf::from(path), args.get(2))
    };
    let timeout_ms: u64 = timeout_arg.and_then(|s| s.parse().ok()).unwrap_or(10_000);
    let files = if exact_list {
        read_exact_list(&input).unwrap_or_else(|error| {
            eprintln!("explain_corpus: {error}");
            std::process::exit(2);
        })
    } else if single_file {
        vec![input.clone()]
    } else {
        let mut files = Vec::new();
        collect_smt2(&input, &mut files);
        if files.is_empty() {
            eprintln!("explain_corpus: no .smt2 under {}", input.display());
            std::process::exit(2);
        }
        files
    };

    // A corpus stream is ordered, but its files are semantically independent.
    // Run exactly one inherited-limit worker at a time so dropping a file also
    // lets the OS reclaim fragmented allocator arenas. The hidden worker
    // marker prevents recursive isolation; every worker record is validated
    // before the parent forwards it.
    if !single_file {
        // The banner is the parent's, on stderr: a worker writing ANY stderr is
        // an error by `validate_worker_output`, and a banner on stdout would
        // corrupt the JSONL stream.
        eprintln!(
            "explain_corpus: DIAGNOSTIC ONLY -- this is `check_auto_explained` on the FLAT \
             assertion view, not the shipped front door. Measured 2026-08-21 it disagreed \
             with `solve_smtlib` on 134 of 397 committed benchmarks. Every verdict below is \
             prefixed `flat-` or `front-door-` for that reason. For an answer, run \
             `smtcomp_cli` (which IS `solve_smtlib`){}",
            if confirm {
                "; --confirm is on, so each record also carries the front door's verdict."
            } else {
                "; pass --confirm to have this tool cross-check itself."
            }
        );
        let mut stdout = std::io::stdout().lock();
        for path in &files {
            let identity = if exact_list {
                path.to_string_lossy()
            } else {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .unwrap_or("<non-utf8>")
                    .into()
            };
            let output = run_isolated_file(path, &identity, timeout_ms, json, confirm, timed_trace)
                .unwrap_or_else(|error| {
                    eprintln!("explain_corpus: {error}");
                    std::process::exit(1);
                });
            stdout.write_all(&output).unwrap_or_else(|error| {
                eprintln!("explain_corpus: cannot write worker output: {error}");
                std::process::exit(1);
            });
            stdout.flush().unwrap_or_else(|error| {
                eprintln!("explain_corpus: cannot flush worker output: {error}");
                std::process::exit(1);
            });
        }
        return;
    }

    let config = SolverConfig::default().with_timeout(Duration::from_millis(timeout_ms));
    let identity_override = std::env::var(WORKER_IDENTITY_ENV).unwrap_or_else(|_| {
        eprintln!("explain_corpus: internal worker identity is missing");
        std::process::exit(2);
    });

    for path in files {
        let identity = identity_override.clone();
        let Ok(text) = std::fs::read_to_string(&path) else {
            if json {
                emit_json(&identity, "read-error", "");
            } else {
                println!("{identity}: read-error");
            }
            continue;
        };
        if ["reset-assertions", "(reset", "(push", "(pop"]
            .iter()
            .any(|kw| text.contains(kw))
        {
            if json {
                emit_json(&identity, "skipped-scoped", "");
            } else {
                println!("{identity}: skipped-scoped");
            }
            continue;
        }
        // `--confirm`: the front door's answer for THIS file, computed once and
        // stamped on every record below -- including the ones where this tool
        // errors or refuses, because "this tool errored, the front door decided"
        // is 71 of the 193 measured divergences and is the reading that most
        // misleads triage.
        let front_door = confirm.then(|| {
            solve_smtlib(&text, &config)
                .map(|outcome| Bare::of(&outcome.result))
                .map_err(|error| error.to_string())
        });
        let confirmation = |flat: Option<Bare>| -> String {
            front_door
                .as_ref()
                .map_or_else(String::new, |fd| confirm_member(fd, flat))
        };
        let prose_confirmation = |flat: Option<Bare>| -> String {
            front_door.as_ref().map_or_else(String::new, |fd| {
                let diverges = if agrees_with_front_door(fd, flat) {
                    ""
                } else {
                    ", DIVERGES"
                };
                match fd {
                    Ok(result) => format!(" [front door: {}{diverges}]", result.label()),
                    Err(error) => format!(" [front door: error: {error}{diverges}]"),
                }
            })
        };
        let mut script = match parse_script(&text) {
            Ok(script) => script,
            Err(SmtError::Unsupported(detail)) if is_wide_integer_unsupported(&detail) => {
                if json {
                    emit_json(
                        &identity,
                        "ingest-unsupported",
                        &format!(
                            ",\"verdict\":\"{NOT_ATTEMPTED}\",\"route\":\"smtlib-ingest\",\
                             \"reason\":\"unsupported\",\"kind\":\"wide-integer-literal\"{}",
                            detail_member(&detail) + &confirmation(None)
                        ),
                    );
                } else {
                    println!(
                        "{identity}: {NOT_ATTEMPTED} (unsupported during ingest: {detail}){}",
                        prose_confirmation(None)
                    );
                }
                continue;
            }
            Err(SmtError::ResourceLimit(detail)) => {
                if json {
                    emit_json(
                        &identity,
                        "ingest-resource-limit",
                        &format!(
                            ",\"verdict\":\"{NOT_ATTEMPTED}\"{}{}",
                            detail_member(&detail),
                            confirmation(None)
                        ),
                    );
                } else {
                    println!(
                        "{identity}: {NOT_ATTEMPTED} (ingest resource limit: {detail}){}",
                        prose_confirmation(None)
                    );
                }
                continue;
            }
            Err(error) => {
                if json {
                    emit_json(
                        &identity,
                        "parse-error",
                        &(detail_member(&error.to_string()) + &confirmation(None)),
                    );
                } else {
                    println!(
                        "{identity}: parse-error: {error}{}",
                        prose_confirmation(None)
                    );
                }
                continue;
            }
        };
        if let Some(refusal) = pre_solve_refusal(script.check_sats) {
            if json {
                emit_json(
                    &identity,
                    refusal.status(),
                    &(refusal_member(refusal) + &confirmation(None)),
                );
            } else {
                println!(
                    "{identity}: {} ({}){}",
                    refusal.status(),
                    refusal.reason(),
                    prose_confirmation(None)
                );
            }
            continue;
        }
        // A word-first-fallback parse has an EMPTY flat view whose content lives in
        // the parser side channels; solving that view directly is a vacuous `sat`
        // (the P0 `instance1079-re-loop-cong` hole). Route it through the text front
        // door, which consults the word / online / membership routes soundly.
        let Some(assertions) = script.solvable_flat_view() else {
            match solve_smtlib(&text, &config) {
                Ok(outcome) => {
                    // This branch really is `solve_smtlib`, so the verdict is the
                    // front door's. Marked as such rather than left bare: one
                    // field carrying two provenances with no marking is how a
                    // diagnostic gets quoted as an answer.
                    let outcome_bare = Bare::of(&outcome.result);
                    let token = front_door_token(outcome_bare);
                    if json {
                        emit_json(
                            &identity,
                            "word-first-fallback",
                            &format!(
                                ",\"verdict\":\"{token}\"{}",
                                confirmation(Some(outcome_bare))
                            ),
                        );
                    } else {
                        println!(
                            "{identity}: {token} (word-first fallback){}",
                            prose_confirmation(Some(outcome_bare))
                        );
                    }
                }
                Err(error) => {
                    if json {
                        emit_json(
                            &identity,
                            "error",
                            &(detail_member(&error.to_string()) + &confirmation(None)),
                        );
                    } else {
                        println!(
                            "{identity}: error: {error} (word-first fallback){}",
                            prose_confirmation(None)
                        );
                    }
                }
            }
            continue;
        };
        let assertions = assertions.to_vec();
        let uses_bounded_strings = script.uses_bounded_strings;
        match check_auto_explained(&mut script.arena, &assertions, &config) {
            Ok((result, trace)) => {
                // `verdict` and the status are fixed literals and `to_json` is
                // already valid JSON, so none of them needs escaping here.
                let result = Bare::of(&result);
                let refusal = post_solve_refusal(result, uses_bounded_strings);
                // `unsat-UNCONFIRMED` used to be printed here. A verdict with a
                // caveat is still a verdict: 46 files printed it in the
                // 2026-08-21 census and the front door decides three of them
                // `sat`.
                let status = refusal.map_or("decided", Refusal::status);
                let verdict_member = refusal.map_or_else(
                    || format!(",\"verdict\":\"{}\"", flat_token(result)),
                    refusal_member,
                );
                if json {
                    let trace_json = if timed_trace {
                        trace.to_json_with_timing()
                    } else {
                        trace.to_json()
                    };
                    emit_json(
                        &identity,
                        status,
                        &format!(
                            "{verdict_member}{},\"trace\":{}",
                            confirmation(refusal.is_none().then_some(result)),
                            trace_json
                        ),
                    );
                } else {
                    let note = prose_confirmation(refusal.is_none().then_some(result));
                    match refusal {
                        Some(refusal) => {
                            println!("{identity}: {NOT_ATTEMPTED} ({}){note}", refusal.reason());
                        }
                        None => println!("{identity}: {}{note}", flat_token(result)),
                    }
                    if timed_trace {
                        for (attempt, elapsed) in trace.attempts().iter().zip(trace.elapsed()) {
                            println!("  {attempt} ({elapsed:?})");
                        }
                    } else {
                        for attempt in trace.attempts() {
                            println!("  {attempt}");
                        }
                    }
                }
            }
            Err(error) => {
                if json {
                    emit_json(
                        &identity,
                        "error",
                        &(detail_member(&error.to_string()) + &confirmation(None)),
                    );
                } else {
                    println!("{identity}: error: {error}{}", prose_confirmation(None));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Bare, NOT_ATTEMPTED, Refusal, agrees_with_front_door, confirm_member, flat_token,
        front_door_token, is_wide_integer_unsupported, post_solve_refusal, pre_solve_refusal,
        read_exact_list, validate_worker_output,
    };

    // --- the 2026-08-21 divergence census, pinned -----------------------
    //
    // Measured over 397 committed benchmarks against `smtcomp_cli` (which IS
    // `solve_smtlib`), both built from the same commit: 193 disagreed. The
    // classes and what this tool now does about each are in `flat_token`'s doc
    // comment. These tests hold the two structural refusals and the token
    // discipline in place. Each guard was deleted in turn; the mutation results
    // are in the commit that added them.

    /// Every token this tool can print as a verdict. If a new one is added
    /// without joining this list, `no_emitted_token_can_be_mistaken_for_an_smt_verdict`
    /// stops testing it -- so the list is the test's coverage, and it is stated
    /// once here rather than three times below.
    fn every_emitted_token() -> Vec<&'static str> {
        let mut tokens = vec![NOT_ATTEMPTED];
        for result in [Bare::Sat, Bare::Unsat, Bare::Unknown] {
            tokens.push(flat_token(result));
            tokens.push(front_door_token(result));
        }
        tokens
    }

    #[test]
    fn no_emitted_token_can_be_mistaken_for_an_smt_verdict() {
        // The point of the whole change: `grep -x unsat` over this tool's
        // output must find nothing, because a wrong verdict from here has
        // already become the foundation of a lever once (CLAUDE.md).
        for token in every_emitted_token() {
            assert!(
                !matches!(token, "sat" | "unsat" | "unknown"),
                "{token} is a bare SMT-LIB verdict"
            );
        }
        // POSITIVE CONTROL: the assertion above is capable of failing. The
        // front-door verdict rendered under `--confirm` IS bare, deliberately,
        // and it is the one authoritative thing in the stream.
        assert_eq!(Bare::Unsat.label(), "unsat");
    }

    #[test]
    fn every_emitted_token_is_distinct() {
        // A collision would let two provenances print the same string, which is
        // the confusion the prefixes exist to remove.
        let tokens = every_emitted_token();
        let mut sorted = tokens.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), tokens.len(), "duplicate token in {tokens:?}");
    }

    #[test]
    fn a_flat_token_names_its_route() {
        assert_eq!(flat_token(Bare::Unsat), "flat-unsat");
        assert_eq!(flat_token(Bare::Sat), "flat-sat");
        assert_eq!(flat_token(Bare::Unknown), "flat-unknown");
    }

    #[test]
    fn a_front_door_token_names_its_route() {
        // The word-first fallback really does call `solve_smtlib`, so its
        // verdict is authoritative -- and still marked, because one field with
        // two provenances and no marking is how a diagnostic gets quoted.
        assert_eq!(front_door_token(Bare::Unsat), "front-door-unsat");
        assert_eq!(front_door_token(Bare::Sat), "front-door-sat");
    }

    #[test]
    fn a_multi_check_sat_script_is_refused_before_any_route_runs() {
        // MEASURED CLASS: `(assert (> x 0)) (check-sat) (assert (< x 0))
        // (check-sat)` -- the front door refuses the script outright
        // (`solve_smtlib` is single-query) and this tool used to flatten it to
        // one conjunction and print `unsat`, which is the answer to neither
        // query in the file.
        assert_eq!(pre_solve_refusal(2), Some(Refusal::MultiCheckSat));
        assert_eq!(pre_solve_refusal(7), Some(Refusal::MultiCheckSat));
    }

    #[test]
    fn a_single_check_sat_script_is_not_refused() {
        // POSITIVE CONTROL for the refusal above: without it, `pre_solve_refusal`
        // returning `Some` unconditionally would still pass.
        assert_eq!(pre_solve_refusal(1), None);
        assert_eq!(pre_solve_refusal(0), None);
    }

    #[test]
    fn a_bounded_string_unsat_is_refused_rather_than_qualified() {
        // MEASURED CLASS: 46 files printed `unsat-UNCONFIRMED` in the census
        // and the front door decides THREE of them `sat`. A verdict with a
        // caveat is still a verdict.
        assert_eq!(
            post_solve_refusal(Bare::Unsat, true),
            Some(Refusal::StringGateUnconfirmed)
        );
    }

    #[test]
    fn a_bounded_string_sat_is_not_refused() {
        // `StringGate::confirm` downgrades a bounded `unsat`; it never promotes
        // a `sat`. Refusing both would throw away the half that agrees.
        assert_eq!(post_solve_refusal(Bare::Sat, true), None);
        assert_eq!(post_solve_refusal(Bare::Unknown, true), None);
    }

    #[test]
    fn an_unbounded_unsat_is_not_refused() {
        // The gate only applies to bounded-string scripts. Without this, a
        // refusal keyed on the verdict alone would refuse every unsat.
        assert_eq!(post_solve_refusal(Bare::Unsat, false), None);
    }

    #[test]
    fn agreement_requires_the_same_verdict() {
        assert!(agrees_with_front_door(&Ok(Bare::Unsat), Some(Bare::Unsat)));
        assert!(!agrees_with_front_door(&Ok(Bare::Unsat), Some(Bare::Sat)));
    }

    #[test]
    fn both_declining_is_agreement_not_divergence() {
        // A multi-check-sat script: this tool refuses, `solve_smtlib` errors.
        // Scoring that as a divergence would bury the 71 real ones -- where
        // this tool errors and the front door DECIDES -- under noise the fix
        // itself created.
        assert!(agrees_with_front_door(&Err("unsupported".to_owned()), None));
    }

    #[test]
    fn one_side_answering_and_the_other_not_is_a_divergence() {
        // MEASURED CLASS: 71 of 397. This is the shape that reads as "axeyum
        // cannot do quantifiers" when the shipped front door decides them.
        assert!(!agrees_with_front_door(&Ok(Bare::Unsat), None));
        assert!(!agrees_with_front_door(
            &Err("boom".to_owned()),
            Some(Bare::Unsat)
        ));
    }

    #[test]
    fn a_confirm_record_states_the_disagreement_in_the_line_itself() {
        let member = confirm_member(&Ok(Bare::Unsat), Some(Bare::Sat));
        assert!(
            member.contains("\"front_door_verdict\":\"unsat\""),
            "{member}"
        );
        assert!(member.contains("\"agrees\":false"), "{member}");
    }

    #[test]
    fn a_confirm_record_marks_agreement_too() {
        let member = confirm_member(&Ok(Bare::Unsat), Some(Bare::Unsat));
        assert!(member.contains("\"agrees\":true"), "{member}");
    }

    #[test]
    fn a_refusal_carries_a_reason_and_a_distinct_status() {
        // The status is what a reader greps and the reason is what tells them
        // why; a refusal with neither is just a hole in the output.
        assert_eq!(Refusal::MultiCheckSat.status(), "refused-multi-check-sat");
        assert_eq!(
            Refusal::StringGateUnconfirmed.status(),
            "refused-string-gate-unconfirmed"
        );
        assert_ne!(
            Refusal::MultiCheckSat.reason(),
            Refusal::StringGateUnconfirmed.reason()
        );
        assert!(!Refusal::MultiCheckSat.reason().is_empty());
    }

    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn fixture() -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "axeyum-explain-corpus-{}-{nonce}",
            std::process::id()
        ));
        std::fs::create_dir(&root).expect("create fixture");
        root
    }

    #[test]
    fn exact_list_preserves_paths_and_order() {
        let root = fixture();
        let first = root.join("first.smt2");
        let second = root.join("second.smt2");
        std::fs::write(&first, "(set-logic QF_NIA)\n").expect("first");
        std::fs::write(&second, "(set-logic QF_NIA)\n").expect("second");
        let list = root.join("list.txt");
        std::fs::write(
            &list,
            format!("{}\n\n{}\n", second.display(), first.display()),
        )
        .expect("list");

        assert_eq!(read_exact_list(&list).expect("valid list"), [second, first]);
        std::fs::remove_dir_all(root).expect("remove fixture");
    }

    #[test]
    fn exact_list_rejects_duplicates_before_solving() {
        let root = fixture();
        let benchmark = root.join("case.smt2");
        std::fs::write(&benchmark, "(set-logic QF_NIA)\n").expect("benchmark");
        let list = root.join("list.txt");
        std::fs::write(
            &list,
            format!("{}\n{}\n", benchmark.display(), benchmark.display()),
        )
        .expect("list");

        let error = read_exact_list(&list).expect_err("duplicate must fail");
        assert!(error.contains("duplicates an earlier path"), "{error}");
        std::fs::remove_dir_all(root).expect("remove fixture");
    }

    #[test]
    fn exact_list_rejects_missing_or_non_smt2_inputs() {
        let root = fixture();
        let wrong_extension = root.join("case.txt");
        std::fs::write(&wrong_extension, "not smtlib").expect("wrong extension");
        let list = root.join("list.txt");
        std::fs::write(&list, format!("{}\n", wrong_extension.display())).expect("list");
        assert!(
            read_exact_list(&list)
                .expect_err("extension")
                .contains("not an .smt2")
        );

        std::fs::write(&list, format!("{}\n", root.join("missing.smt2").display())).expect("list");
        assert!(
            read_exact_list(&list)
                .expect_err("missing")
                .contains("does not name a file")
        );
        std::fs::remove_dir_all(root).expect("remove fixture");
    }

    #[test]
    fn wide_integer_unsupported_match_is_exact() {
        assert!(is_wide_integer_unsupported(
            "integer literal `170141183460469231731687303715884105728` exceeds the modeled `Int` range"
        ));
        assert!(!is_wide_integer_unsupported(
            "integer literal `` exceeds the modeled `Int` range"
        ));
        assert!(!is_wide_integer_unsupported(
            "integer literal `12x` exceeds the modeled `Int` range"
        ));
        assert!(!is_wide_integer_unsupported(
            "operator `unsupported` is outside the modeled `Int` range"
        ));
    }

    #[test]
    fn isolated_json_worker_requires_one_matching_record() {
        let record =
            br#"{"file":"/tmp/case.smt2","status":"decided","verdict":"unknown","trace":{}}
"#;
        validate_worker_output(record, b"", "/tmp/case.smt2", true).expect("valid worker");

        let mismatch = br#"{"file":"/tmp/other.smt2","status":"decided"}
"#;
        assert!(
            validate_worker_output(mismatch, b"", "/tmp/case.smt2", true)
                .expect_err("identity mismatch")
                .contains("different file identity")
        );
        assert!(
            validate_worker_output(b"{}\n{}\n", b"", "/tmp/case.smt2", true)
                .expect_err("two records")
                .contains("more than one JSON record")
        );
    }

    #[test]
    fn isolated_worker_fails_closed_on_stderr_or_empty_output() {
        assert!(
            validate_worker_output(b"record\n", b"panic", "case.smt2", false)
                .expect_err("stderr")
                .contains("stderr bytes")
        );
        assert!(
            validate_worker_output(b"", b"", "case.smt2", false)
                .expect_err("empty")
                .contains("no output")
        );
    }
}
