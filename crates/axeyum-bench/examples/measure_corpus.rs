//! Measured per-division head-to-head: axeyum vs the Z3 binary on a corpus dir.
//!
//! This is the missing measurement piece called for by the `PLAN.md` course
//! correction: the existing bench harness only measures `QF_BV` (and its z3-crate
//! oracle cannot lower reals), so no other division has a *measured* number. This
//! shells the system `z3` binary (any logic, native) against every flat `.smt2`
//! under a directory and times axeyum's `check_auto` on the same files, reporting
//! decided counts, agreement, soundness disagreements, and **PAR-2** for both.
//!
//! Usage:
//! ```text
//! cargo run --release -p axeyum-bench --example measure_corpus -- <dir> [timeout_ms] [out.json]
//! ```
//!
//! PAR-2 (SMT-COMP convention): a decided instance scores its solve seconds; an
//! undecided one (timeout / `unknown`) scores `2 × timeout`. Lower is better.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

impl Verdict {
    fn decided(self) -> bool {
        matches!(self, Verdict::Sat | Verdict::Unsat)
    }
    fn label(self) -> &'static str {
        match self {
            Verdict::Sat => "sat",
            Verdict::Unsat => "unsat",
            Verdict::Unknown => "unknown",
        }
    }
}

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

/// Time axeyum's `check_auto` on a parsed script, capped on a worker thread.
fn run_axeyum(text: &str, cap: Duration) -> (Verdict, f64) {
    let Ok(mut script) = parse_script(text) else {
        return (Verdict::Unknown, cap.as_secs_f64());
    };
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let start = Instant::now();
            let config = SolverConfig::default().with_timeout(cap);
            let verdict = match check_auto(&mut script.arena, &script.assertions, &config) {
                Ok(CheckResult::Sat(_)) => Verdict::Sat,
                Ok(CheckResult::Unsat) => Verdict::Unsat,
                Ok(CheckResult::Unknown(_)) | Err(_) => Verdict::Unknown,
            };
            let _ = tx.send((verdict, start.elapsed().as_secs_f64()));
        })
        .expect("spawn solver thread");
    rx.recv_timeout(cap)
        .unwrap_or((Verdict::Unknown, cap.as_secs_f64()))
}

/// Shell the system `z3` binary on a file with a wall-clock timeout.
///
/// Returns `None` when z3 **rejects the file at parse** (an `(error …)` — e.g. a
/// cvc5-specific `set-option`, or a logic z3 does not accept). Such a file is not
/// a fair head-to-head instance (z3 never reached the solver), so the caller
/// excludes it from the comparison rather than scoring it as a z3 miss — without
/// this, a permissive-parser advantage masquerades as a solving win.
fn run_z3(path: &Path, cap: Duration) -> Option<(Verdict, f64)> {
    let secs = cap.as_secs().max(1);
    let start = Instant::now();
    let output = Command::new("z3")
        .arg(format!("-T:{secs}"))
        .arg(path)
        .output()
        .ok()?;
    let elapsed = start.elapsed().as_secs_f64();
    let stdout = String::from_utf8_lossy(&output.stdout);
    // z3 prints `(error ...)` to stdout on a rejected file; treat as not-comparable.
    if stdout.contains("(error") {
        return None;
    }
    let first = stdout
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("");
    let verdict = match first {
        "sat" => Verdict::Sat,
        "unsat" => Verdict::Unsat,
        _ => Verdict::Unknown,
    };
    Some((verdict, elapsed))
}

/// PAR-2 contribution: solve seconds if decided, else `2 × timeout`.
fn par2(verdict: Verdict, secs: f64, cap: Duration) -> f64 {
    if verdict.decided() {
        secs
    } else {
        2.0 * cap.as_secs_f64()
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = PathBuf::from(args.get(1).cloned().unwrap_or_else(|| {
        eprintln!("usage: measure_corpus <dir> [timeout_ms] [out.json]");
        std::process::exit(2);
    }));
    let timeout_ms: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10_000);
    let cap = Duration::from_millis(timeout_ms);
    let out_json = args.get(3).cloned();

    let mut files = Vec::new();
    collect_smt2(&dir, &mut files);
    assert!(!files.is_empty(), "no .smt2 under {}", dir.display());

    let (mut ax_decided, mut z3_decided, mut agree, mut disagree, mut considered) =
        (0u32, 0u32, 0u32, 0u32, 0u32);
    let mut z3_rejected = 0u32;
    let (mut ax_par2_sum, mut z3_par2_sum) = (0.0f64, 0.0f64);

    for path in &files {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        // Flat-view only: scoped scripts aren't a single query.
        if ["reset-assertions", "(reset", "(push", "(pop"]
            .iter()
            .any(|kw| text.contains(kw))
        {
            continue;
        }
        // Skip files axeyum's front end cannot parse (not comparable).
        if parse_script(&text).is_err() {
            continue;
        }
        // Exclude files z3 rejects at parse (cvc5-specific options/logics): not a
        // fair head-to-head instance. Keeps the comparison on the common set.
        let Some((zv, zsecs)) = run_z3(path, cap) else {
            z3_rejected += 1;
            continue;
        };
        considered += 1;

        let (av, asecs) = run_axeyum(&text, cap);

        if av.decided() {
            ax_decided += 1;
        }
        if zv.decided() {
            z3_decided += 1;
        }
        if av.decided() && zv.decided() {
            if av == zv {
                agree += 1;
            } else {
                disagree += 1;
                eprintln!(
                    "  *** SOUNDNESS DISAGREEMENT: {} — axeyum {}, z3 {}",
                    path.display(),
                    av.label(),
                    zv.label()
                );
            }
        }
        ax_par2_sum += par2(av, asecs, cap);
        z3_par2_sum += par2(zv, zsecs, cap);
    }

    let n = f64::from(considered.max(1));
    let ax_par2 = ax_par2_sum / n;
    let z3_par2 = z3_par2_sum / n;

    println!("division dir: {}", dir.display());
    println!(
        "timeout: {timeout_ms} ms | considered (both parse, flat): {considered} | z3-rejected (cvc5-specific): {z3_rejected}"
    );
    println!("axeyum decided: {ax_decided}/{considered} | PAR-2 {ax_par2:.3}s");
    println!("z3     decided: {z3_decided}/{considered} | PAR-2 {z3_par2:.3}s");
    println!("agree: {agree} | DISAGREE: {disagree}");

    if let Some(out) = out_json {
        let json = format!(
            "{{\n  \"dir\": \"{}\",\n  \"timeout_ms\": {timeout_ms},\n  \"considered\": {considered},\n  \"z3_rejected_unfair\": {z3_rejected},\n  \"axeyum_decided\": {ax_decided},\n  \"z3_decided\": {z3_decided},\n  \"agree\": {agree},\n  \"disagree\": {disagree},\n  \"axeyum_par2_s\": {ax_par2:.4},\n  \"z3_par2_s\": {z3_par2:.4}\n}}\n",
            dir.display()
        );
        std::fs::write(&out, json).expect("write out json");
        println!("wrote {out}");
    }

    assert_eq!(disagree, 0, "soundness disagreement(s) vs z3 — see above");
}
