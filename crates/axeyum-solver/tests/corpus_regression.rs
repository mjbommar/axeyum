//! Corpus regression gate — soundness over status-annotated SMT-LIB corpora.
//!
//! Walks every `*.smt2` under `corpus/regression/<logic>/`, parses it with the
//! `axeyum-smtlib` front end, runs [`check_auto`], and compares the verdict
//! against the benchmark's `(set-info :status ...)` ground truth.
//!
//! The contract is **soundness, not completeness**: a file that fails to parse
//! (a front-end gap) or that axeyum returns `Unknown` for is *skipped* — those
//! are coverage gaps, not bugs. The test **fails only on a wrong verdict**
//! (`sat` declared but axeyum says `unsat`, or vice versa) — the one thing that
//! must never happen. This makes any status-annotated corpus (hand-authored,
//! cvc5/Z3-curated, or generated) a permanent, oracle-free regression gate.
//!
//! Each solve runs on a worker thread under a wall-clock cap so a pathological
//! instance degrades to a skip instead of hanging the suite.

use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto, solve_smtlib};

/// Per-file wall-clock cap. The committed corpora are tiny; the cap only guards
/// against a future heavy instance hanging the suite.
const SOLVE_CAP: Duration = Duration::from_secs(2);

#[derive(Debug, Default)]
struct Summary {
    total: usize,
    agree: usize,
    unknown: usize,
    parse_skipped: usize,
    no_status: usize,
    /// (file, expected, got) — the soundness failures.
    disagreements: Vec<(String, String, String)>,
}

/// Recursively collect `*.smt2` files under `dir`, sorted for determinism.
fn collect_smt2(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    paths.sort();
    for p in paths {
        if p.is_dir() {
            collect_smt2(&p, out);
        } else if p.extension().is_some_and(|e| e == "smt2") {
            out.push(p);
        }
    }
}

/// Decide a parsed script on a worker thread, `None` if it overruns [`SOLVE_CAP`].
///
/// Scope-free scripts with a populated flat `assertions` view go through
/// [`check_auto`] (the auto-dispatch this gate targets). A script whose flat view
/// is **empty** — a **word-first-fallback** parse (an over-`STRING_MAX_LEN` literal
/// or a bounded-unsupported regex like `re.loop`), whose real content lives only in
/// the parser side channels (`word_skeleton` / `membership_problem`) — is decided
/// through the sound text front door [`solve_smtlib`] instead. Solving the empty
/// flat view directly is a **vacuous `sat`** (the empty conjunction), which would
/// be a wrong verdict for a genuinely-unsat fallback script (the P0 this closes:
/// `instance1079-re-loop-cong`, unsat, was reported `sat`).
fn solve_capped(text: String, script: axeyum_smtlib::Script) -> Option<CheckResult> {
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            // A solver error is `unknown`-equivalent for this gate (never a wrong
            // verdict), so both routes collapse to `Option<CheckResult>`.
            let res: Option<CheckResult> = if script.assertions.is_empty() {
                // Side-channel-only (fallback) script: decide via the full front
                // door, which consults the word / online / membership routes.
                solve_smtlib(&text, &SolverConfig::default())
                    .ok()
                    .map(|o| o.result)
            } else {
                let mut script = script;
                check_auto(
                    &mut script.arena,
                    &script.assertions,
                    &SolverConfig::default(),
                )
                .ok()
            };
            let _ = tx.send(res);
        })
        .expect("spawn solver thread");
    match rx.recv_timeout(SOLVE_CAP) {
        Ok(result) => result,
        // Overran the wall-clock cap — an `unknown`-equivalent skip.
        Err(_) => None,
    }
}

fn corpus_root() -> PathBuf {
    // tests run with CWD = crate dir (crates/axeyum-solver); the corpus lives at
    // the workspace root.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/regression")
}

/// Per-file verdict against the declared `:status`.
enum Eval {
    Agree,
    Unknown,
    /// Front-end gap, scoped script, or unreadable — not a soundness concern.
    Skip,
    /// No usable `sat`/`unsat` ground truth.
    NoStatus,
    /// The one thing that must never happen: verdict contradicts `:status`.
    Disagree {
        expected: String,
        got: String,
    },
}

/// Parse one file and compare `check_auto`'s verdict to its `:status`.
fn evaluate_file(path: &Path, rel: &str) -> Eval {
    let Ok(text) = std::fs::read_to_string(path) else {
        return Eval::Skip;
    };
    // The flat `assertions` view ignores push/pop/reset scoping, so it is only
    // faithful for scope-free scripts. A `:status` on a scoped script refers to
    // the *final* incremental state, not the conjunction of every assertion —
    // comparing against the flat view there is a false alarm. Skip such files.
    if ["reset-assertions", "(reset", "(push", "(pop"]
        .iter()
        .any(|kw| text.contains(kw))
    {
        return Eval::Skip;
    }
    let Ok(script) = parse_script(&text) else {
        return Eval::Skip; // front-end gap — a coverage gap, not a soundness bug
    };
    let Some(expected) = script.status.clone() else {
        return Eval::NoStatus;
    };
    let expected = expected.to_ascii_lowercase();
    if expected != "sat" && expected != "unsat" {
        return Eval::NoStatus; // `unknown`/`unsupported` ground truth
    }

    let t0 = std::time::Instant::now();
    let outcome = solve_capped(text, script);
    let dt = t0.elapsed();
    let label = match &outcome {
        Some(CheckResult::Sat(_)) => "sat",
        Some(CheckResult::Unsat) => "unsat",
        Some(CheckResult::Unknown(_)) => "unknown",
        None => "timeout",
    };
    if dt > Duration::from_millis(1500) || matches!(outcome, Some(CheckResult::Unknown(_)) | None) {
        eprintln!(
            "  [undecided/slow] {rel}: {label} in {} ms (expected {expected})",
            dt.as_millis()
        );
    }
    match outcome {
        Some(CheckResult::Sat(_)) if expected == "unsat" => Eval::Disagree {
            expected,
            got: "sat".to_owned(),
        },
        Some(CheckResult::Unsat) if expected == "sat" => Eval::Disagree {
            expected,
            got: "unsat".to_owned(),
        },
        Some(CheckResult::Sat(_) | CheckResult::Unsat) => Eval::Agree,
        Some(CheckResult::Unknown(_)) | None => Eval::Unknown,
    }
}

#[test]
fn corpus_regression_is_sound() {
    let root = corpus_root();
    assert!(
        root.is_dir(),
        "corpus/regression not found at {}",
        root.display()
    );

    let mut files = Vec::new();
    collect_smt2(&root, &mut files);
    assert!(!files.is_empty(), "no .smt2 files under {}", root.display());

    let mut s = Summary::default();
    for path in &files {
        s.total += 1;
        let rel = path
            .strip_prefix(&root)
            .unwrap_or(path)
            .display()
            .to_string();
        match evaluate_file(path, &rel) {
            Eval::Agree => s.agree += 1,
            Eval::Unknown => s.unknown += 1,
            Eval::Skip => s.parse_skipped += 1,
            Eval::NoStatus => s.no_status += 1,
            Eval::Disagree { expected, got } => s.disagreements.push((rel, expected, got)),
        }
    }

    eprintln!(
        "corpus_regression: {} files | {} agree | {} unknown | {} parse-skipped | {} no-status | {} DISAGREE",
        s.total,
        s.agree,
        s.unknown,
        s.parse_skipped,
        s.no_status,
        s.disagreements.len()
    );

    assert!(
        s.disagreements.is_empty(),
        "SOUNDNESS FAILURE — verdict contradicts benchmark :status:\n{}",
        s.disagreements
            .iter()
            .map(|(f, e, g)| format!("  {f}: expected {e}, got {g}"))
            .collect::<Vec<_>>()
            .join("\n")
    );

    // Sanity: the committed seed corpus must actually exercise the solver — guard
    // against a silent regression where everything starts being skipped.
    assert!(
        s.agree >= 6,
        "expected the seed corpus to decide >= 6 instances correctly, only {} agreed \
         ({} unknown, {} parse-skipped) — front-end or dispatch regression?",
        s.agree,
        s.unknown,
        s.parse_skipped
    );
}
