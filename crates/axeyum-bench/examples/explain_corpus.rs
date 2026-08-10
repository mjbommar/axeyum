//! Per-file `check_auto_explained` probe for a corpus directory or exact list.
//!
//! This complements `measure_corpus`: the measured aggregate is the scoreboard,
//! while this probe shows which files moved and which route declined.
//!
//! ```text
//! cargo run -p axeyum-bench --example explain_corpus -- <dir> [timeout_ms] [--json]
//! cargo run -p axeyum-bench --example explain_corpus -- --list <file> [timeout_ms] [--json]
//! ```
//!
//! With `--json` the probe emits one JSON object per line (JSONL) instead of
//! prose, embedding the route trace via
//! [`RouteTrace::to_json`](axeyum_solver::route_trace::RouteTrace::to_json).
//! That is the persistable form the bridge-catalogue replay validator consumes:
//! it needs the observed dispatch order as data, not as `Display` text.
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

fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
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
    line.push_str(extra);
    line.push('}');
    println!("{line}");
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
    let args: Vec<String> = raw.into_iter().filter(|arg| arg != "--json").collect();
    let usage = "usage: explain_corpus <dir> [timeout_ms] [--json]\n       explain_corpus --list <file> [timeout_ms] [--json]";
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
            let output =
                run_isolated_file(path, &identity, timeout_ms, json).unwrap_or_else(|error| {
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
        let mut script = match parse_script(&text) {
            Ok(script) => script,
            Err(SmtError::Unsupported(detail)) if is_wide_integer_unsupported(&detail) => {
                if json {
                    emit_json(
                        &identity,
                        "ingest-unsupported",
                        &format!(
                            ",\"verdict\":\"unknown\",\"route\":\"smtlib-ingest\",\
                             \"reason\":\"unsupported\",\"kind\":\"wide-integer-literal\"{}",
                            detail_member(&detail)
                        ),
                    );
                } else {
                    println!("{identity}: unknown (unsupported during ingest: {detail})");
                }
                continue;
            }
            Err(SmtError::ResourceLimit(detail)) => {
                if json {
                    emit_json(
                        &identity,
                        "ingest-resource-limit",
                        &format!(",\"verdict\":\"unknown\"{}", detail_member(&detail)),
                    );
                } else {
                    println!("{identity}: unknown (ingest resource limit: {detail})");
                }
                continue;
            }
            Err(error) => {
                if json {
                    emit_json(&identity, "parse-error", &detail_member(&error.to_string()));
                } else {
                    println!("{identity}: parse-error: {error}");
                }
                continue;
            }
        };
        // A word-first-fallback parse has an EMPTY flat view whose content lives in
        // the parser side channels; solving that view directly is a vacuous `sat`
        // (the P0 `instance1079-re-loop-cong` hole). Route it through the text front
        // door, which consults the word / online / membership routes soundly.
        let Some(assertions) = script.solvable_flat_view() else {
            match solve_smtlib(&text, &config) {
                Ok(outcome) => {
                    let verdict = verdict(&outcome.result);
                    if json {
                        emit_json(
                            &identity,
                            "word-first-fallback",
                            &format!(",\"verdict\":\"{verdict}\""),
                        );
                    } else {
                        println!("{identity}: {verdict} (word-first fallback)");
                    }
                }
                Err(error) => {
                    if json {
                        emit_json(&identity, "error", &detail_member(&error.to_string()));
                    } else {
                        println!("{identity}: error: {error} (word-first fallback)");
                    }
                }
            }
            continue;
        };
        let assertions = assertions.to_vec();
        // Whether a verdict from the FLAT view can be trusted for this script.
        //
        // `check_auto_explained` decides the flat assertion view, which bypasses
        // the ADR-0052 `StringGate` the shipped front door applies. On a bounded
        // string script that gate is what downgrades a bounded-encoding `unsat`
        // to `unknown` when bound-independence is not confirmed — so without it
        // this tool printed `unsat` for `regex-032-…-fuzz`, a file that is
        // genuinely `sat` (cvc5 agrees, and `solve_smtlib` returns `sat`).
        //
        // The solver was never wrong; only this diagnostic was. That matters
        // because agents are routinely pointed here for string triage, and a
        // fabricated `unsat` is a foundation someone builds a whole lever on.
        // A diagnostic that declines to confirm is useful; one that states a
        // wrong verdict is worse than silence.
        let flat_verdict_is_trustworthy = !script.uses_bounded_strings;
        match check_auto_explained(&mut script.arena, &assertions, &config) {
            Ok((result, trace)) => {
                let verdict = match (&result, flat_verdict_is_trustworthy) {
                    // Only the `unsat` direction is at risk: the gate downgrades
                    // a bounded `unsat`, it never promotes a `sat`.
                    (CheckResult::Unsat, false) => "unsat-UNCONFIRMED",
                    _ => verdict(&result),
                };
                if json {
                    // `verdict` is a fixed literal and `to_json` is already
                    // valid JSON, so neither needs escaping here.
                    emit_json(
                        &identity,
                        "decided",
                        &format!(",\"verdict\":\"{verdict}\",\"trace\":{}", trace.to_json()),
                    );
                } else {
                    println!("{identity}: {verdict}");
                    for attempt in trace.attempts() {
                        println!("  {attempt}");
                    }
                }
            }
            Err(error) => {
                if json {
                    emit_json(&identity, "error", &detail_member(&error.to_string()));
                } else {
                    println!("{identity}: error: {error}");
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{is_wide_integer_unsupported, read_exact_list, validate_worker_output};
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
