//! Diagnostic: run the pure-Rust word-level local-search engine (PBLS, P1.7) on a
//! QF_BV `.smt2` query, to test whether it cracks the **SAT-search-bound** Timeout
//! instances (all satisfiable) that CDCL — batsat and the in-tree xor_cdcl — miss.
//! Local search excels on satisfiable structural instances, so it is a candidate
//! *pure-Rust* lever for the search-bound band (ADR-0037). Usage:
//!
//! ```sh
//! cargo run --release -p axeyum-bench --example pbls_probe -- <file.smt2> [timeout_s]
//! ```
#![allow(clippy::doc_markdown)]

use std::time::{Duration, Instant};

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, solve_local_search};

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: pbls_probe <file.smt2> [timeout_s]");
    let timeout_s: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(20);

    let text = std::fs::read_to_string(&path).expect("read smt2");
    let script = parse_script(&text).expect("parse");
    let config = SolverConfig::default().with_timeout(Duration::from_secs(timeout_s));

    let t = Instant::now();
    let outcome =
        solve_local_search(&script.arena, &script.assertions, &config).expect("local search runs");
    let verdict = match &outcome.result {
        CheckResult::Sat(_) => "SAT",
        CheckResult::Unsat => "UNSAT (unexpected — PBLS is one-sided)",
        CheckResult::Unknown(r) => {
            return eprintln!(
                "{path}: pbls UNKNOWN ({}) in {:.2?} [flips={}, restarts={}]",
                r.detail,
                t.elapsed(),
                outcome.flips,
                outcome.restarts
            );
        }
    };
    eprintln!(
        "{path}: pbls {verdict} in {:.2?} [flips={}, restarts={}]",
        t.elapsed(),
        outcome.flips,
        outcome.restarts
    );
}
