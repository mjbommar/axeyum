//! Diagnostic (roadmap item 3.9): attribute where a hard **satisfiable** `QF_BV`
//! instance spends its budget — parsing, word-level preprocessing, bit-vector
//! lowering, CNF construction, or SAT search.
//!
//! One file per process on purpose. These instances are exactly the ones that
//! blow a memory ceiling or never return, so the bound has to come from outside
//! the process (`timeout`, `ulimit -v`), not from a `recv_timeout` on a thread
//! that keeps allocating. See
//! `docs/research/03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md`.
//!
//! ```sh
//! cargo build --release -p axeyum-bench --example qfbv_sat_attribution
//! target/release/examples/qfbv_sat_attribution <file.smt2> <budget_ms> <arm>
//! ```
//!
//! An optional fourth argument sets `SolverConfig::resource_limit`, which
//! `solve_with_native_cdcl` passes straight through as the CDCL core's
//! `max_conflicts`. Timing a run at `max_conflicts = N` therefore measures the
//! wall clock the search needs to reach N conflicts — which is what says
//! whether the deadline cadence in `proof_sat.rs` (every
//! `DEADLINE_CHECK_INTERVAL = 1_024` CONFLICTS, not seconds) can fire at all.
//!
//! `arm` is `auto` (the shipping front door, `check_auto`) or `backend` (the
//! cold pure-Rust `SatBvBackend` alone, which is the stage that carries the
//! `bit_blast_ms` / `cnf_encode_ms` attribution), or `backend-sliced` (the same
//! backend with `BitLoweringMode::DemandSliced`, ADR-0157, which is defaulted
//! off at `crates/axeyum-solver/src/backend.rs:395`).
//!
//! Output is one tab-separated row on stdout, so a caller that kills the process
//! sees no row at all and must record that as its own outcome — never as a
//! measured zero.
#![allow(clippy::doc_markdown)]

use std::time::{Duration, Instant};

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    BitLoweringMode, CheckResult, SatBvBackend, SolverBackend, SolverConfig, check_auto,
};

fn stat(stats: &[(String, f64)], key: &str) -> String {
    stats
        .iter()
        .find(|(name, _)| name == key)
        .map_or_else(|| "-".to_owned(), |(_, value)| format!("{value:.0}"))
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: qfbv_sat_attribution <file.smt2> [budget_ms] [arm]");
    let budget_ms: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(10_000);
    let arm = args.next().unwrap_or_else(|| "auto".to_owned());
    let resource_limit: Option<u64> = args.next().and_then(|s| s.parse().ok());
    // Raises `ABSOLUTE_CLAUSE_CEILING` (64,000,000, `sat_bv_backend.rs`) for one
    // run, so a query the pre-lowering ESTIMATE refuses can be lowered and its
    // real clause count compared against that estimate.
    let clause_budget: Option<u64> = args.next().and_then(|s| s.parse().ok());

    let size = std::fs::metadata(&path).map_or(0, |m| m.len());
    let read_start = Instant::now();
    let text = std::fs::read_to_string(&path).expect("read smt2");
    let parse_start = Instant::now();
    let mut script = match parse_script(&text) {
        Ok(script) => script,
        Err(error) => {
            println!("{path}\t{size}\t-\t-\t-\tPARSE_ERROR\t-\t-\t-\t-\t-\t-\t-\t{error}");
            return;
        }
    };
    let parse_ms = parse_start.elapsed().as_millis();
    let read_ms = (parse_start - read_start).as_millis();
    let dag_nodes = script.arena.len();

    let mut config = SolverConfig::default().with_timeout(Duration::from_millis(budget_ms));
    config.resource_limit = resource_limit;
    config.cnf_clause_budget = clause_budget;
    let start = Instant::now();
    let (verdict, detail, backend_stats) = match arm.as_str() {
        "auto" => {
            let outcome = check_auto(&mut script.arena, &script.assertions, &config);
            match outcome {
                Ok(CheckResult::Sat(_)) => ("sat".to_owned(), String::new(), Vec::new()),
                Ok(CheckResult::Unsat) => ("unsat".to_owned(), String::new(), Vec::new()),
                Ok(CheckResult::Unknown(reason)) => {
                    ("unknown".to_owned(), reason.detail, Vec::new())
                }
                Err(error) => ("error".to_owned(), error.to_string(), Vec::new()),
            }
        }
        "backend" | "backend-sliced" => {
            let config = if arm == "backend-sliced" {
                let mut config = config;
                config.bit_lowering_mode = BitLoweringMode::DemandSliced;
                config
            } else {
                config
            };
            let mut backend = SatBvBackend::new();
            let outcome = backend.check(&script.arena, &script.assertions, &config);
            let stats = backend
                .last_stats()
                .map(|s| {
                    let mut rows = s.backend.clone();
                    rows.push(("solve_ms".to_owned(), s.solve.as_secs_f64() * 1000.0));
                    rows
                })
                .unwrap_or_default();
            match outcome {
                Ok(CheckResult::Sat(_)) => ("sat".to_owned(), String::new(), stats),
                Ok(CheckResult::Unsat) => ("unsat".to_owned(), String::new(), stats),
                Ok(CheckResult::Unknown(reason)) => ("unknown".to_owned(), reason.detail, stats),
                Err(error) => ("error".to_owned(), error.to_string(), stats),
            }
        }
        other => panic!("unknown arm {other}"),
    };
    let total_ms = start.elapsed().as_millis();

    println!(
        "{path}\t{size}\t{read_ms}\t{parse_ms}\t{dag_nodes}\t{verdict}\t{total_ms}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        stat(&backend_stats, "bit_blast_ms"),
        stat(&backend_stats, "cnf_encode_ms"),
        stat(&backend_stats, "solve_ms"),
        stat(&backend_stats, "aig_nodes"),
        stat(&backend_stats, "cnf_variables"),
        stat(&backend_stats, "cnf_clauses"),
        detail.replace(['\t', '\n'], " "),
    );
}
