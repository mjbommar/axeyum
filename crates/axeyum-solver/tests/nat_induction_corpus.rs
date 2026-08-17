//! The ℕ-induction corpus: what the front door decides, what induction decides,
//! and what the benchmark says is true.
//!
//! `docs/mathematics-2026-08/04-reachability.md` R3 ranks `induction-over-nat`
//! first among out-of-fragment requests, and
//! [`prove_by_nat_induction`](axeyum_solver::prove_by_nat_induction) is the
//! route built for it. It is exported at the crate root and deliberately **not**
//! in `check_auto`'s dispatch. This suite is the evidence that would decide
//! whether it should be, and it measures three things per instance rather than
//! one:
//!
//! 1. the declared `(set-info :status …)` — the ground truth,
//! 2. what the shipped front door [`solve_smtlib`] says today,
//! 3. what [`prove_by_nat_induction`] says.
//!
//! Two questions follow from that table. **How many instances does the
//! induction route decide that the front door does not?** — that is the value
//! case. And **does it ever contradict a declared `:status`?** — that is the
//! soundness case, and one contradiction is enough to disqualify the route from
//! dispatch regardless of how good the first number looks.
//!
//! # Status of this suite
//!
//! [`nat_induction_never_contradicts_declared_status`] **was committed red** and
//! is now green. It failed on the three `unguarded_*` instances: the route
//! stripped an `n >= 0` guard when the goal had one
//! (`nat_induction.rs::strip_nonneg_guard`) but proceeded anyway when it did
//! not, discharging base and step over ℕ while the goal quantified over `Int`.
//! On `(assert (not (forall ((n Int)) (>= n 0))))` it answered `unsat` for a set
//! that z3 and axeyum's own front door both answer `sat` for.
//!
//! `a32280b6a` made the guard mandatory. Re-measured after that fix: the three
//! `unguarded_*` rows are declines (`-`), the four unique `unsat` decisions
//! survive, and the contradiction count is `0`. The route is now the last rung
//! of [`axeyum_solver::solve`]'s quantified ladder, so the **front-door** column
//! of this table is no longer independent of the induction column — where it
//! reads `unsat` on a guarded row, this rung is why. The adversarial shapes that
//! justified wiring it live in `tests/nat_induction_adversarial.rs`.
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, prove_by_nat_induction, solve_smtlib};

/// Per-route wall-clock cap. The instances are tiny; this only stops a
/// nonlinear step obligation from hanging the suite.
const CAP: Duration = Duration::from_secs(10);

/// The corpus lives at the workspace root; tests run with CWD = crate dir.
fn corpus_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/regression/uflia_induction")
}

fn collect_smt2(dir: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("corpus unreadable at {}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|e| e == "smt2"))
        .collect();
    out.sort();
    out
}

fn label(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

/// Run `f` on a worker thread with a big stack, `None` on overrun.
fn capped<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> Option<T> {
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let _ = tx.send(f());
        })
        .expect("spawn worker");
    rx.recv_timeout(CAP).ok()
}

/// What the shipped front door says today.
fn front_door_verdict(text: &str) -> String {
    let owned = text.to_owned();
    match capped(move || solve_smtlib(&owned, &SolverConfig::default()).map(|o| o.result)) {
        Some(Ok(r)) => label(&r).to_owned(),
        // A front-end gap or backend error is "does not decide", never a verdict.
        Some(Err(_)) => "error".to_owned(),
        None => "timeout".to_owned(),
    }
}

/// What the induction route says. `None` (declined) renders as `-`.
fn induction_verdict(text: &str) -> String {
    let owned = text.to_owned();
    let run = move || {
        let mut parsed = parse_script(&owned).ok()?;
        let assertions = parsed.assertions.clone();
        prove_by_nat_induction(&mut parsed.arena, &assertions, &SolverConfig::default())
            .ok()
            .flatten()
            .map(|r| label(&r).to_owned())
    };
    match capped(run) {
        Some(Some(v)) => v,
        Some(None) => "-".to_owned(),
        None => "timeout".to_owned(),
    }
}

struct Row {
    name: String,
    declared: String,
    front: String,
    induction: String,
}

/// Measure every instance three ways. Shared by both tests below.
fn measure() -> Vec<Row> {
    let root = corpus_root();
    assert!(root.is_dir(), "corpus missing at {}", root.display());
    let files = collect_smt2(&root);

    // The failure mode this repository keeps hitting: a corpus sweep that walks
    // zero files, decides nothing, and exits 0. The count is asserted, not
    // assumed, and the floor is the committed instance count.
    assert!(
        files.len() >= 12,
        "corpus sweep found {} instances under {}; expected at least 12 — a sweep \
         that walks (nearly) nothing passes vacuously",
        files.len(),
        root.display()
    );

    let mut rows = Vec::new();
    for path in &files {
        let text = std::fs::read_to_string(path).expect("instance readable");
        let declared = parse_script(&text)
            .ok()
            .and_then(|s| s.status.clone())
            .map_or_else(|| "none".to_owned(), |s| s.to_ascii_lowercase());
        assert!(
            declared == "sat" || declared == "unsat",
            "{}: every corpus instance must declare (set-info :status sat|unsat), got {declared}",
            path.display()
        );
        rows.push(Row {
            name: path.file_stem().unwrap().to_string_lossy().into_owned(),
            declared,
            front: front_door_verdict(&text),
            induction: induction_verdict(&text),
        });
    }
    rows
}

/// Print the three-way table and count what the induction route adds.
#[test]
fn nat_induction_corpus_table() {
    let rows = measure();

    eprintln!(
        "\n| {:<38} | {:<8} | {:<10} | {:<9} |",
        "instance", "declared", "front door", "induction"
    );
    eprintln!("|{:-<40}|{:-<10}|{:-<12}|{:-<11}|", "", "", "", "");
    for r in &rows {
        eprintln!(
            "| {:<38} | {:<8} | {:<10} | {:<9} |",
            r.name, r.declared, r.front, r.induction
        );
    }

    let decided = |v: &str| v == "sat" || v == "unsat";
    let uniquely = rows
        .iter()
        .filter(|r| decided(&r.induction) && !decided(&r.front))
        .count();
    let front_decides = rows.iter().filter(|r| decided(&r.front)).count();
    let contradictions: Vec<&Row> = rows
        .iter()
        .filter(|r| decided(&r.induction) && r.induction != r.declared)
        .collect();

    eprintln!(
        "\nnat_induction_corpus: {} instances | front door decides {} | induction uniquely decides {} | {} STATUS CONTRADICTIONS",
        rows.len(),
        front_decides,
        uniquely,
        contradictions.len()
    );
    for r in &contradictions {
        eprintln!(
            "  CONTRADICTION {}: declared {}, induction said {}",
            r.name, r.declared, r.induction
        );
    }
}

/// The soundness gate: neither the induction route **nor the front door** may
/// contradict a declared `:status`.
///
/// Declining (`-`), `unknown`, and `timeout` are always fine — this route is
/// allowed to be incomplete and says so. Answering `unsat` for a `sat`
/// benchmark is not.
///
/// **This test was committed red**, failing on the three `unguarded_*`
/// instances: the route proved the goal over ℕ while the SMT-LIB quantifier
/// ranged over `Int`, so any goal without an `n >= 0` guard that happens to be
/// false below zero was refuted anyway. `a32280b6a` made the guard mandatory and
/// it went green — which is the point of having committed it red rather than
/// writing a version that passed over the bug.
///
/// It now checks **both** verdict columns. While the route sat outside dispatch,
/// only its own column could be wrong; now that it is the last rung of
/// [`axeyum_solver::solve`], a wrong `unsat` it produces is a wrong `unsat` the
/// front door ships, and a gate that watched only the isolated route would not
/// see it.
#[test]
fn nat_induction_never_contradicts_declared_status() {
    let rows = measure();
    let decided = |v: &str| v == "sat" || v == "unsat";
    let mut contradictions: Vec<String> = Vec::new();
    for r in &rows {
        if decided(&r.induction) && r.induction != r.declared {
            contradictions.push(format!(
                "  {}: declared {}, induction route said {}",
                r.name, r.declared, r.induction
            ));
        }
        if decided(&r.front) && r.front != r.declared {
            contradictions.push(format!(
                "  {}: declared {}, FRONT DOOR said {}",
                r.name, r.declared, r.front
            ));
        }
    }

    assert!(
        contradictions.is_empty(),
        "SOUNDNESS FAILURE — a declared :status is contradicted on {} of {} instances:\n{}\n\n\
         ℕ-induction discharges base and step over ℕ; if the goal quantifies over Int without \
         a recognised `n >= 0` guard, refuting it is a wrong unsat. The route is wired into \
         `solve`, so this is a shipped verdict.",
        contradictions.len(),
        rows.len(),
        contradictions.join("\n")
    );
}
