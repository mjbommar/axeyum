//! Per-file `check_auto_explained` probe for a corpus directory.
//!
//! This complements `measure_corpus`: the measured aggregate is the scoreboard,
//! while this probe shows which files moved and which route declined.
//!
//! ```text
//! cargo run -p axeyum-bench --example explain_corpus -- <dir> [timeout_ms] [--json]
//! ```
//!
//! With `--json` the probe emits one JSON object per line (JSONL) instead of
//! prose, embedding the route trace via
//! [`RouteTrace::to_json`](axeyum_solver::route_trace::RouteTrace::to_json).
//! That is the persistable form the bridge-catalogue replay validator consumes:
//! it needs the observed dispatch order as data, not as `Display` text.
//!
//! Every line has `file` and `status`; `status` is one of `decided`,
//! `word-first-fallback`, `skipped-scoped`, `read-error`, `parse-error`, or
//! `error`. `verdict` is present on the two decided statuses, `trace` only on
//! `decided`, and `detail` only on `error`.

use std::path::{Path, PathBuf};
use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::route_trace::push_json_string;
use axeyum_solver::{CheckResult, SolverConfig, check_auto_explained, solve_smtlib};

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

#[allow(clippy::too_many_lines)] // linear CLI driver: arg parsing + per-file loop + summary
fn main() {
    let raw: Vec<String> = std::env::args().collect();
    // `--json` may appear anywhere; strip it before positional parsing so the
    // existing `<dir> [timeout_ms]` call sites keep working unchanged.
    let json = raw.iter().any(|arg| arg == "--json");
    let args: Vec<String> = raw.into_iter().filter(|arg| arg != "--json").collect();
    let dir = args
        .get(1)
        .cloned()
        .unwrap_or_else(|| {
            eprintln!("usage: explain_corpus <dir> [timeout_ms] [--json]");
            std::process::exit(2);
        })
        .into();
    let dir: PathBuf = dir;
    let timeout_ms: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10_000);
    let config = SolverConfig::default().with_timeout(Duration::from_millis(timeout_ms));
    let mut files = Vec::new();
    collect_smt2(&dir, &mut files);
    assert!(!files.is_empty(), "no .smt2 under {}", dir.display());

    for path in files {
        let short = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("<non-utf8>");
        let Ok(text) = std::fs::read_to_string(&path) else {
            if json {
                emit_json(short, "read-error", "");
            } else {
                println!("{short}: read-error");
            }
            continue;
        };
        if ["reset-assertions", "(reset", "(push", "(pop"]
            .iter()
            .any(|kw| text.contains(kw))
        {
            if json {
                emit_json(short, "skipped-scoped", "");
            } else {
                println!("{short}: skipped-scoped");
            }
            continue;
        }
        let Ok(mut script) = parse_script(&text) else {
            if json {
                emit_json(short, "parse-error", "");
            } else {
                println!("{short}: parse-error");
            }
            continue;
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
                            short,
                            "word-first-fallback",
                            &format!(",\"verdict\":\"{verdict}\""),
                        );
                    } else {
                        println!("{short}: {verdict} (word-first fallback)");
                    }
                }
                Err(error) => {
                    if json {
                        emit_json(short, "error", &detail_member(&error.to_string()));
                    } else {
                        println!("{short}: error: {error} (word-first fallback)");
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
                        short,
                        "decided",
                        &format!(",\"verdict\":\"{verdict}\",\"trace\":{}", trace.to_json()),
                    );
                } else {
                    println!("{short}: {verdict}");
                    for attempt in trace.attempts() {
                        println!("  {attempt}");
                    }
                }
            }
            Err(error) => {
                if json {
                    emit_json(short, "error", &detail_member(&error.to_string()));
                } else {
                    println!("{short}: error: {error}");
                }
            }
        }
    }
}
