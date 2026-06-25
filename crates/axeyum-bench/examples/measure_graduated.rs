//! Measured head-to-head on a GRADUATED synthetic corpus: axeyum vs the Z3
//! binary, with per-family DECIDE-FRONTIER and `:status` agreement.
//!
//! This complements [`measure_corpus`] for the neutral, graduated `QF_NRA` /
//! `QF_NIA` corpus produced by `scripts/gen-graduated-nra-nia.py`. Every instance
//! carries a `(set-info :status …)` established **by construction** (a checkable
//! witness for sat; an independent infeasibility argument for unsat), so the
//! ground truth does not depend on Z3.
//!
//! For each file it records:
//! - axeyum's verdict (sat/unsat/unknown) and solve seconds (timeout-capped on a
//!   big-stack worker thread; matches `measure_corpus`),
//! - Z3's verdict and seconds (shelling the system `z3` binary),
//! - agreement against **both** the `:status` annotation and Z3,
//! - any DISAGREE (axeyum decides ≠ Z3 OR ≠ `:status`) — a soundness alarm,
//! - PAR-2 for both engines,
//! - a per-family DECIDE-FRONTIER: the largest difficulty knob (the trailing
//!   zero-padded integer in the file stem, e.g. `…-k07` → 7) on which axeyum
//!   returns a decided verdict.
//!
//! Usage:
//! ```text
//! cargo run --release -p axeyum-bench --example measure_graduated -- <dir> [timeout_ms] [out.json]
//! ```
//!
//! The committed baselines are produced with `timeout_ms = 30000`.

use std::collections::BTreeMap;
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
    fn from_status(s: &str) -> Verdict {
        match s {
            "sat" => Verdict::Sat,
            "unsat" => Verdict::Unsat,
            _ => Verdict::Unknown,
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

/// Time axeyum's `check_auto` on a parsed script, capped on a big-stack worker.
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
fn run_z3(path: &Path, cap: Duration) -> (Verdict, f64) {
    let secs = cap.as_secs().max(1);
    let start = Instant::now();
    let output = Command::new("z3")
        .arg(format!("-T:{secs}"))
        .arg(path)
        .output();
    let elapsed = start.elapsed().as_secs_f64();
    let Ok(output) = output else {
        return (Verdict::Unknown, elapsed);
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
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
    (verdict, elapsed)
}

/// PAR-2 contribution: solve seconds if decided, else `2 × timeout`.
fn par2(verdict: Verdict, secs: f64, cap: Duration) -> f64 {
    if verdict.decided() {
        secs
    } else {
        2.0 * cap.as_secs_f64()
    }
}

/// Read the `(set-info :status …)` annotation from the source text.
fn status_of(text: &str) -> Verdict {
    for line in text.lines() {
        if let Some(rest) = line.trim().strip_prefix("(set-info :status ") {
            let tok = rest.trim_end_matches(')').trim();
            return Verdict::from_status(tok);
        }
    }
    Verdict::Unknown
}

/// Family + knob from a file stem like `nra-sat-witness-k07` → ("nra-sat-witness", 7).
fn family_knob(stem: &str) -> (String, u32) {
    if let Some(pos) = stem.rfind('-') {
        let (fam, tail) = stem.split_at(pos);
        let digits: String = tail.chars().filter(char::is_ascii_digit).collect();
        if let Ok(k) = digits.parse::<u32>() {
            return (fam.to_string(), k);
        }
    }
    (stem.to_string(), 0)
}

/// Accumulated measurement totals, populated in `main` and rendered by `report`.
#[derive(Default)]
struct Totals {
    considered: u32,
    ax_decided: u32,
    z3_decided: u32,
    agree: u32,
    disagree: u32,
    ax_sat: u32,
    ax_unsat: u32,
    ax_unknown: u32,
    ax_par2_sum: f64,
    z3_par2_sum: f64,
    /// family -> (largest knob decided, largest knob present)
    frontier: BTreeMap<String, (u32, u32)>,
    disagreements: Vec<String>,
}

/// Print the human-readable summary and (optionally) write the JSON baseline.
fn report(dir: &Path, timeout_ms: u64, t: &Totals, out_json: Option<&str>) {
    let n = f64::from(t.considered.max(1));
    let ax_par2 = t.ax_par2_sum / n;
    let z3_par2 = t.z3_par2_sum / n;
    let (considered, ax_decided, z3_decided, agree, disagree) = (
        t.considered,
        t.ax_decided,
        t.z3_decided,
        t.agree,
        t.disagree,
    );
    let (ax_sat, ax_unsat, ax_unknown) = (t.ax_sat, t.ax_unsat, t.ax_unknown);

    println!("division dir: {}", dir.display());
    println!("timeout: {timeout_ms} ms | considered (axeyum parses): {considered}");
    println!(
        "axeyum decided: {ax_decided}/{considered} (sat {ax_sat}, unsat {ax_unsat}, unknown {ax_unknown}) | PAR-2 {ax_par2:.3}s"
    );
    println!("z3     decided: {z3_decided}/{considered} | PAR-2 {z3_par2:.3}s");
    println!("agree (decided, both): {agree} | DISAGREE: {disagree}");
    println!("DECIDE-FRONTIER (family: largest-knob-decided / largest-knob-present):");
    for (fam, (dec, max)) in &t.frontier {
        println!("  {fam}: {dec}/{max}");
    }
    for d in &t.disagreements {
        println!("  DISAGREE> {d}");
    }

    if let Some(out) = out_json {
        let fr = t
            .frontier
            .iter()
            .map(|(fam, (dec, max))| {
                format!(
                    "    {{ \"family\": \"{fam}\", \"frontier_decided\": {dec}, \"max_knob\": {max} }}"
                )
            })
            .collect::<Vec<_>>()
            .join(",\n");
        let da = t
            .disagreements
            .iter()
            .map(|d| format!("\"{}\"", d.replace('"', "'")))
            .collect::<Vec<_>>()
            .join(", ");
        let json = format!(
            "{{\n  \"dir\": \"{}\",\n  \"timeout_ms\": {timeout_ms},\n  \"considered\": {considered},\n  \"axeyum_decided\": {ax_decided},\n  \"axeyum_sat\": {ax_sat},\n  \"axeyum_unsat\": {ax_unsat},\n  \"axeyum_unknown\": {ax_unknown},\n  \"z3_decided\": {z3_decided},\n  \"agree\": {agree},\n  \"disagree\": {disagree},\n  \"axeyum_par2_s\": {ax_par2:.4},\n  \"z3_par2_s\": {z3_par2:.4},\n  \"decide_frontier\": [\n{fr}\n  ],\n  \"disagreements\": [{da}]\n}}\n",
            dir.display()
        );
        std::fs::write(out, json).expect("write out json");
        println!("wrote {out}");
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = PathBuf::from(args.get(1).cloned().unwrap_or_else(|| {
        eprintln!("usage: measure_graduated <dir> [timeout_ms] [out.json]");
        std::process::exit(2);
    }));
    let timeout_ms: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(30_000);
    let cap = Duration::from_millis(timeout_ms);
    let out_json = args.get(3).cloned();

    let mut files = Vec::new();
    collect_smt2(&dir, &mut files);
    assert!(!files.is_empty(), "no .smt2 under {}", dir.display());

    let mut t = Totals::default();

    for path in &files {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        if parse_script(&text).is_err() {
            eprintln!("  (skip, axeyum parse error) {}", path.display());
            continue;
        }
        t.considered += 1;
        let status = status_of(&text);
        let (av, asecs) = run_axeyum(&text, cap);
        let (zv, zsecs) = run_z3(path, cap);

        let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
        let (fam, knob) = family_knob(stem);
        let entry = t.frontier.entry(fam).or_insert((0, 0));
        entry.1 = entry.1.max(knob);

        match av {
            Verdict::Sat => t.ax_sat += 1,
            Verdict::Unsat => t.ax_unsat += 1,
            Verdict::Unknown => t.ax_unknown += 1,
        }
        if av.decided() {
            t.ax_decided += 1;
            entry.0 = entry.0.max(knob);
        }
        if zv.decided() {
            t.z3_decided += 1;
        }

        // DISAGREE = a DECIDED axeyum verdict that contradicts Z3 or the
        // by-construction :status. (axeyum unknown is never a disagreement.)
        let mut bad = false;
        if av.decided() {
            if zv.decided() && av != zv {
                bad = true;
                t.disagreements.push(format!(
                    "{}: axeyum {} vs z3 {}",
                    path.display(),
                    av.label(),
                    zv.label()
                ));
            }
            if status.decided() && av != status {
                bad = true;
                t.disagreements.push(format!(
                    "{}: axeyum {} vs :status {}",
                    path.display(),
                    av.label(),
                    status.label()
                ));
            }
        }
        if bad {
            t.disagree += 1;
            eprintln!(
                "  *** SOUNDNESS DISAGREEMENT: {} — axeyum {}, z3 {}, status {}",
                path.display(),
                av.label(),
                zv.label(),
                status.label()
            );
        } else if av.decided() && zv.decided() && av == zv {
            t.agree += 1;
        }

        t.ax_par2_sum += par2(av, asecs, cap);
        t.z3_par2_sum += par2(zv, zsecs, cap);
    }

    report(&dir, timeout_ms, &t, out_json.as_deref());

    assert_eq!(t.disagree, 0, "soundness disagreement(s) — see above");
}
