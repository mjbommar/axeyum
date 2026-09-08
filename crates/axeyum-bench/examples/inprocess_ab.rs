//! End-to-end A/B driver for CNF inprocessing on the **shipping SMT front door**.
//!
//! ```sh
//! cargo run --release -p axeyum-bench --example inprocess_ab -- \
//!     <file.smt2> <timeout_ms> <off|inproc|inproc-vivify>
//! ```
//!
//! # Why this exists rather than `smtcomp_cli --trace`
//!
//! `smtcomp_cli` can turn inprocessing on (`AXEYUM_CNF_INPROCESSING=1`) and can
//! print a `; bv-layer …` trace line, but that line is a **projection**: it
//! renders the fixed [`axeyum_solver::BvLayerStats`] schema, so a counter added
//! for a measurement is invisible through it. The whole point of this lane is
//! counters that did not exist yesterday — per-pass spend, the budget slice each
//! pass was granted, and whether the deadline had expired when it returned — so
//! the driver reads the raw backend key/value pairs
//! ([`axeyum_solver::last_bv_backend_counters`]) and prints all of them.
//!
//! Everything else is deliberately the same as `smtcomp_cli`: the same
//! [`axeyum_solver::solve_smtlib`] front door, the same `SolverConfig` levers, the
//! same 512 MiB worker stack, and the same watchdog-plus-grace wall clock. A
//! number measured here is a number about the shipped path.
//!
//! # What one line means
//!
//! One JSON object per run on stdout. `verdict` is `sat`/`unsat`/`unknown`, and
//! `unknown` covers everything that is not a decision — the watchdog firing, a
//! resource refusal, a parse failure. `wall_ms` is measured around the whole
//! solve including SMT-LIB ingest, because that is what a competition budget
//! pays for.
//!
//! `counters` carries the backend's raw keys. Two of them are the reason this
//! binary exists:
//!
//! * `inprocess_budget_ms` — the slice inprocessing was *granted* (half the
//!   remaining solve budget). Absent when the run had no deadline.
//! * `<pass>_deadline_expired` — whether that deadline had already passed when
//!   the pass returned.
//!
//! A pass whose `<pass>_ms` is a small fraction of `inprocess_budget_ms` and
//! whose `_deadline_expired` is 0 ran to its own fixpoint: its cost is what the
//! pass costs. A pass that spent the slice and returns with the deadline expired
//! was cut off, having already paid its setup. Those two call for opposite work
//! and no aggregate ratio distinguishes them.
//!
//! A counter that is ABSENT is not a zero — it means this run did not record it
//! (the stage did not run, or there was no deadline to expire). The JSON omits
//! absent keys rather than defaulting them, so the reader cannot lose that.

use std::time::{Duration, Instant};

use axeyum_solver::{
    BvLayerStatsGuard, CheckResult, SolverConfig, last_bv_backend_counters, solve_smtlib,
};

/// Same stack the competition CLI gives its worker: a deeply nested input must
/// not turn a timeout into a stack-overflow abort.
const WORKER_STACK_BYTES: usize = 512 * 1024 * 1024;
/// Same grace the competition CLI allows between the solver's soft internal stop
/// and the external watchdog.
const WATCHDOG_GRACE: Duration = Duration::from_secs(1);

/// The three arms, expressed in the shipping `SolverConfig` levers.
///
/// `inproc` is subsumption + BVE (what `AXEYUM_CNF_INPROCESSING=1` turns on);
/// `inproc-vivify` adds the vivification pass between them. There is
/// deliberately no "bve only" arm here: `SolverConfig` has no per-pass toggle,
/// so isolating a single pass end-to-end would mean inventing a configuration
/// the solver cannot actually ship. Per-pass isolation is measured at the CNF
/// level instead, where `InprocessOptions` has the fields.
fn arm_config(arm: &str, timeout_ms: u64) -> SolverConfig {
    let base = SolverConfig::new().with_timeout(Duration::from_millis(timeout_ms));
    match arm {
        "off" => base,
        "inproc" => base.with_cnf_inprocessing(true),
        "inproc-vivify" => base.with_cnf_inprocessing(true).with_cnf_vivify(true),
        other => panic!("unknown arm `{other}`: expected off, inproc or inproc-vivify"),
    }
}

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: inprocess_ab <file.smt2> <timeout_ms> <off|inproc|inproc-vivify>");
    let timeout_ms: u64 = args
        .next()
        .expect("timeout_ms required")
        .parse()
        .expect("timeout_ms must be a number");
    let arm = args.next().unwrap_or_else(|| "off".to_owned());
    let config = arm_config(&arm, timeout_ms);

    let input = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            // A read failure is reported, not guessed at: it must never be
            // scored as an honest `unknown` from the solver.
            println!(
                "{{\"file\":\"{}\",\"arm\":\"{}\",\"budget_ms\":{timeout_ms},\
                 \"verdict\":\"read_error\",\"detail\":\"{}\",\"wall_ms\":0,\"counters\":{{}}}}",
                json_escape(&path),
                json_escape(&arm),
                json_escape(&e.to_string())
            );
            std::process::exit(0);
        }
    };

    let solve = move || -> (&'static str, u128, Vec<(String, f64)>) {
        // The guard is what makes `last_bv_backend_counters` non-empty; it is
        // thread-local, so it must be armed on the worker thread that solves.
        let _bv_guard = BvLayerStatsGuard::enable();
        let started = Instant::now();
        let verdict = match solve_smtlib(&input, &config) {
            Ok(outcome) => match outcome.result {
                CheckResult::Sat(_) => "sat",
                CheckResult::Unsat => "unsat",
                CheckResult::Unknown(_) => "unknown",
            },
            Err(_) => "unknown",
        };
        let wall_ms = started.elapsed().as_millis();
        (verdict, wall_ms, last_bv_backend_counters())
    };

    let (tx, rx) = std::sync::mpsc::channel();
    let worker = std::thread::Builder::new()
        .stack_size(WORKER_STACK_BYTES)
        .spawn(move || {
            let _ = tx.send(solve());
        });
    let (verdict, wall_ms, counters) = match worker {
        Ok(_) => match rx.recv_timeout(Duration::from_millis(timeout_ms) + WATCHDOG_GRACE) {
            Ok(outcome) => outcome,
            // The watchdog fired: the worker is still inside the solve, so its
            // thread-local counters are unreadable from here. Reporting an empty
            // counter set is correct — inventing zeros would make a run that
            // never finished inprocessing look like one that spent nothing on it.
            Err(_) => (
                "unknown",
                u128::from(timeout_ms) + WATCHDOG_GRACE.as_millis(),
                Vec::new(),
            ),
        },
        Err(_) => ("unknown", 0, Vec::new()),
    };

    let counter_json = counters
        .iter()
        .map(|(k, v)| format!("\"{}\":{v}", json_escape(k)))
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "{{\"file\":\"{}\",\"arm\":\"{}\",\"budget_ms\":{timeout_ms},\
         \"verdict\":\"{verdict}\",\"wall_ms\":{wall_ms},\"counters\":{{{counter_json}}}}}",
        json_escape(&path),
        json_escape(&arm)
    );
    std::io::Write::flush(&mut std::io::stdout()).ok();
    // The worker may still be inside ingest; the line is already printed and
    // correct, so exit rather than block on a thread that has no deadline.
    std::process::exit(0);
}
