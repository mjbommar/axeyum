//! Diagnostic: solve one DIMACS CNF with the native proof-producing CDCL core
//! and print the search statistics the core actually exposes, as one JSON
//! line, so they can be compared against a reference solver's `-v` output
//! (Kissat/CaDiCaL) on the same file.
//!
//! ```sh
//! cargo run --release -p axeyum-bench --example native_core_stats -- <file.cnf> [budget_secs]
//! ```
//!
//! # What this can and cannot report
//!
//! [`axeyum_cnf::ProofSearchProgress`] (`crates/axeyum-cnf/src/proof_sat.rs`)
//! is a *cumulative* snapshot carrying `conflicts`, `learned_clauses`,
//! `proof_steps`, `proof_bytes`, and `elapsed` — read directly from that
//! struct's doc comment before writing this file. It does **not** carry a
//! decision counter, a propagation counter, or a restart counter: the `Cdcl`
//! struct tracks `restart_count` internally (`crates/axeyum-cnf/src/proof_sat.rs`)
//! but never exposes it through `ProofSearchProgress`, and no decision or
//! propagation counter exists anywhere in the struct. Adding one would be a
//! production-code change to `axeyum-cnf`, which this measurement lane is not
//! permitted to make. So this tool prints `null` for `decisions`,
//! `propagations`, and `restarts` rather than fabricating a number — the
//! absence is itself a measured finding, not a gap to paper over.
//!
//! Not part of the solve path — a one-shot measurement tool.
#![allow(clippy::doc_markdown)]

use std::fs;
use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfFormula, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, ProofSearchProgress, ProofSolveOutcome,
    parse_dimacs, solve_with_drat_proof_with_limits_and_progress,
};

fn opt_num<T: std::fmt::Display>(v: Option<T>) -> String {
    match v {
        Some(x) => x.to_string(),
        None => "null".to_string(),
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let cnf_path = args
        .next()
        .expect("usage: native_core_stats <file.cnf> [budget_secs]");
    let budget_secs: u64 = args
        .next()
        .map_or(60, |s| s.parse().expect("budget_secs must be an integer"));

    let text = fs::read_to_string(&cnf_path).expect("read dimacs");
    let formula: CnfFormula = parse_dimacs(&text).expect("parse dimacs");

    let deadline = Instant::now() + Duration::from_secs(budget_secs);
    let start = Instant::now();

    let mut last_progress: Option<ProofSearchProgress> = None;
    let mut progress_cb = |p: &ProofSearchProgress| {
        last_progress = Some(*p);
    };

    let outcome = solve_with_drat_proof_with_limits_and_progress(
        &formula,
        Some(deadline),
        DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
        // Poll every 1000 conflicts (and once more at the end) — cheap enough
        // not to perturb the search, frequent enough that the final snapshot
        // reflects the search at (or very near) the point it stopped.
        1000,
        &mut progress_cb,
    );
    let wall_ms = start.elapsed().as_secs_f64() * 1000.0;

    let (verdict, model_checked) = match &outcome {
        ProofSolveOutcome::Sat(assignment) => {
            let ok = formula.evaluate(assignment.values()).unwrap_or(false);
            ("sat", Some(ok))
        }
        ProofSolveOutcome::Unsat(_) => ("unsat", None),
        ProofSolveOutcome::ResourceOut => ("resource_out", None),
        ProofSolveOutcome::Interrupted => ("interrupted", None),
    };

    let conflicts = last_progress.map(|p| p.conflicts);
    let learned_clauses = last_progress.map(|p| p.learned_clauses);
    let proof_steps = last_progress.map(|p| p.proof_steps);
    let proof_bytes = last_progress.map(|p| p.proof_bytes);

    println!(
        "{{\"file\":\"{}\",\"verdict\":\"{}\",\"model_checked\":{},\"wall_ms\":{:.3},\
         \"conflicts\":{},\"decisions\":null,\"propagations\":null,\
         \"learned_clauses\":{},\"restarts\":null,\
         \"proof_steps\":{},\"proof_bytes\":{}}}",
        cnf_path,
        verdict,
        match model_checked {
            Some(true) => "true",
            Some(false) => "false",
            None => "null",
        },
        wall_ms,
        opt_num(conflicts),
        opt_num(learned_clauses),
        opt_num(proof_steps),
        opt_num(proof_bytes),
    );

    if model_checked == Some(false) {
        eprintln!("!!! INVALID MODEL for {cnf_path} — P0, reported sat but model fails evaluate");
        std::process::exit(1);
    }
}
