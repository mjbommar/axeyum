//! Runs the native proof-producing CDCL core ([`solve_with_drat_proof_within`])
//! over a list of DIMACS files under a per-file wall-clock budget and prints one
//! TSV row per file: `file<TAB>variables<TAB>clauses<TAB>verdict<TAB>wall_ms`.
//!
//! This is the ADR-1701 slice-2 spike's gate-(b)-style arm. It exists because
//! `crates/axeyum-bench/examples/gate_b_sweep.rs` — the tool that produced
//! `bench-results/sat-core-gate-b-20260905/` — used to carry
//! `required-features = ["batsat-reference"]` and run `BatSat` alongside the
//! native core, doubling the wall time of a before/after sweep on a corpus that
//! mostly exhausts its budget. ADR-1910 removed that arm and the gate with it,
//! so the two now differ mainly in crate: this one drives the native core out of
//! `axeyum-cnf` itself, so both arms of a before/after comparison build in
//! seconds and the measured difference is the CNF layer and nothing else.
//!
//! A `sat` verdict is checked against the formula with [`CnfFormula::evaluate`]
//! before it is recorded; an invalid model is a hard error, not a quiet `sat`.
//!
//! ```sh
//! cargo run --release -p axeyum-cnf --example native_core_sweep -- <budget_secs> <file.cnf>...
//! ```
//!
//! Not part of the solve path — a measurement tool.

use std::path::Path;
use std::time::{Duration, Instant};

use axeyum_cnf::{ProofSolveOutcome, parse_dimacs, solve_with_drat_proof_within};

fn main() {
    let mut args = std::env::args().skip(1);
    let budget_secs: u64 = args
        .next()
        .expect("usage: native_core_sweep <budget_secs> <file.cnf>...")
        .parse()
        .expect("budget_secs must be an integer");
    let budget = Duration::from_secs(budget_secs);
    let files: Vec<String> = args.collect();
    assert!(!files.is_empty(), "at least one .cnf file is required");

    println!("file\tvariables\tclauses\tverdict\twall_ms");
    let mut failed = false;
    for path in &files {
        let path = Path::new(path);
        let name = path.file_name().map_or_else(
            || path.display().to_string(),
            |n| n.to_string_lossy().into(),
        );
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(error) => {
                eprintln!("read {}: {error}", path.display());
                failed = true;
                continue;
            }
        };
        let formula = match parse_dimacs(&text) {
            Ok(formula) => formula,
            Err(error) => {
                eprintln!("parse {}: {error}", path.display());
                failed = true;
                continue;
            }
        };
        let started = Instant::now();
        let outcome = solve_with_drat_proof_within(&formula, Some(started + budget));
        let wall_ms = started.elapsed().as_secs_f64() * 1000.0;
        let verdict = match &outcome {
            ProofSolveOutcome::Sat(model) => {
                // A `sat` answer is only reported after the model is checked
                // against the formula through the same evaluator every other
                // sweep in this tree uses. An unchecked `sat` is a P0, not a row.
                if formula.evaluate(model.values()) == Ok(true) {
                    "sat"
                } else {
                    eprintln!("INVALID MODEL: {}", path.display());
                    failed = true;
                    "invalid-model"
                }
            }
            ProofSolveOutcome::Unsat(_) => "unsat",
            ProofSolveOutcome::ResourceOut => "resource-out",
            ProofSolveOutcome::Interrupted => "unknown",
        };
        println!(
            "{name}\t{}\t{}\t{verdict}\t{wall_ms:.3}",
            formula.variable_count(),
            formula.clauses().len()
        );
    }
    // The exit status depends on the finding: a read failure, a parse failure or
    // an invalid model must not be reportable as a completed sweep.
    assert!(!failed, "sweep had failures; see stderr");
}
