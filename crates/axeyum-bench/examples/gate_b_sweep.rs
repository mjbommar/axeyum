//! Gate (b) measurement: does the best pure-Rust SAT adapter (BatSat) or the
//! native proof-producing CDCL core (`solve_with_drat_proof`) show a
//! consistent material gap to CaDiCaL/Kissat on Axeyum-generated CNF?
//!
//! Two subcommands, deliberately narrow:
//!
//! - `sweep <cnf_dir> <out.json> <budget_secs>` runs BatSat
//!   ([`solve_with_rustsat_batsat_timeout`]) and the native core
//!   ([`solve_with_drat_proof_within`]) over every `*.cnf` file in `cnf_dir`,
//!   each under the same per-file wall-clock budget. A `sat` verdict is
//!   checked against the formula with [`CnfFormula::evaluate`] before being
//!   recorded — an invalid model is a hard error, not a silent `sat`. The two
//!   engines' verdicts are cross-checked against each other; a disagreement
//!   (one says `sat`, the other `unsat`) is reported as `"disagreement"` in
//!   the row and printed to stderr, since that is a P0 soundness finding, not
//!   a performance number.
//! - `verify <cnf_file> <assignment_file>` evaluates a DIMACS solution line
//!   (`v <lit> <lit> ... 0`, possibly spread across multiple `v` lines, as
//!   CaDiCaL/Kissat emit it) captured from an external solver's stdout
//!   against the same formula, through the same evaluator, so external `sat`
//!   answers are checked by the identical trusted code path as the internal
//!   engines. Prints `OK` (exit 0) or `FAIL: <reason>` (exit 1).
//!
//! Not part of the solve path — a one-shot measurement tool for the SAT-core
//! priority gate (b) in
//! `docs/research/08-planning/benchmarking-and-performance-methodology.md`.
#![allow(clippy::doc_markdown)]

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfAssignment, CnfFormula, ProofSolveOutcome, SatResult, parse_dimacs,
    solve_with_drat_proof_within, solve_with_rustsat_batsat_timeout,
};
use serde_json::json;

fn read_cnf(path: &Path) -> Result<CnfFormula, String> {
    let text =
        fs::read_to_string(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    parse_dimacs(&text).map_err(|error| format!("parse {}: {error}", path.display()))
}

/// One engine's outcome on one instance: verdict, wall time, whether the
/// budget was exhausted, and (for `sat`) whether the model was checked valid.
struct EngineRow {
    verdict: &'static str,
    wall_ms: f64,
    timed_out: bool,
    model_valid: Option<bool>,
}

fn run_batsat(formula: &CnfFormula, budget: Duration) -> EngineRow {
    let started = Instant::now();
    let result = solve_with_rustsat_batsat_timeout(formula, Some(budget));
    let wall_ms = started.elapsed().as_secs_f64() * 1000.0;
    match result {
        Ok(SatResult::Sat(model)) => EngineRow {
            verdict: "sat",
            wall_ms,
            timed_out: false,
            model_valid: Some(model.satisfies(formula).unwrap_or(false)),
        },
        Ok(SatResult::Unsat(_)) => EngineRow {
            verdict: "unsat",
            wall_ms,
            timed_out: false,
            model_valid: None,
        },
        Ok(SatResult::Unknown(_)) => EngineRow {
            verdict: "unknown",
            wall_ms,
            timed_out: true,
            model_valid: None,
        },
        Err(error) => {
            eprintln!("batsat error: {error}");
            EngineRow {
                verdict: "error",
                wall_ms,
                timed_out: false,
                model_valid: None,
            }
        }
    }
}

fn run_native(formula: &CnfFormula, budget: Duration) -> EngineRow {
    let started = Instant::now();
    let deadline = Instant::now().checked_add(budget);
    let outcome = solve_with_drat_proof_within(formula, deadline);
    let wall_ms = started.elapsed().as_secs_f64() * 1000.0;
    match outcome {
        ProofSolveOutcome::Sat(model) => EngineRow {
            verdict: "sat",
            wall_ms,
            timed_out: false,
            model_valid: Some(model.satisfies(formula).unwrap_or(false)),
        },
        ProofSolveOutcome::Unsat(_) => EngineRow {
            verdict: "unsat",
            wall_ms,
            timed_out: false,
            model_valid: None,
        },
        ProofSolveOutcome::ResourceOut => EngineRow {
            verdict: "unknown",
            wall_ms,
            timed_out: false,
            model_valid: None,
        },
        ProofSolveOutcome::Interrupted => EngineRow {
            verdict: "unknown",
            wall_ms,
            timed_out: true,
            model_valid: None,
        },
    }
}

fn cmd_sweep(args: &[String]) -> Result<(), String> {
    let [dir, out, budget_secs] = args else {
        return Err("usage: gate_b_sweep sweep <cnf_dir> <out.json> <budget_secs>".to_string());
    };
    let dir = PathBuf::from(dir);
    let budget_secs: f64 = budget_secs
        .parse()
        .map_err(|error| format!("invalid budget_secs: {error}"))?;
    let budget = Duration::from_secs_f64(budget_secs);

    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .map_err(|error| format!("read {}: {error}", dir.display()))?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "cnf"))
        .collect();
    paths.sort();
    if paths.is_empty() {
        return Err(format!("no .cnf files in {}", dir.display()));
    }

    let mut rows = Vec::with_capacity(paths.len());
    let mut disagreements = Vec::new();
    for (i, path) in paths.iter().enumerate() {
        eprintln!("[{}/{}] {}", i + 1, paths.len(), path.display());
        let formula = match read_cnf(path) {
            Ok(f) => f,
            Err(error) => {
                eprintln!("  SKIP: {error}");
                rows.push(json!({
                    "path": path.file_name().map(|n| n.to_string_lossy().into_owned()),
                    "error": error,
                }));
                continue;
            }
        };
        let batsat = run_batsat(&formula, budget);
        let native = run_native(&formula, budget);

        if matches!(
            (batsat.verdict, native.verdict),
            ("sat", "unsat") | ("unsat", "sat")
        ) {
            let msg = format!(
                "DISAGREEMENT on {}: batsat={} native={}",
                path.display(),
                batsat.verdict,
                native.verdict
            );
            eprintln!("  !!! {msg}");
            disagreements.push(msg);
        }
        for (engine, row) in [("batsat", &batsat), ("native", &native)] {
            if row.verdict == "sat" && row.model_valid != Some(true) {
                eprintln!(
                    "  !!! {engine} returned sat on {} with an INVALID model",
                    path.display()
                );
                disagreements.push(format!(
                    "{engine} sat with invalid model on {}",
                    path.display()
                ));
            }
        }

        rows.push(json!({
            "path": path.file_name().map(|n| n.to_string_lossy().into_owned()),
            "variables": formula.variable_count(),
            "clauses": formula.clauses().len(),
            "batsat": {
                "verdict": batsat.verdict,
                "wall_ms": batsat.wall_ms,
                "timed_out": batsat.timed_out,
                "model_valid": batsat.model_valid,
            },
            "native": {
                "verdict": native.verdict,
                "wall_ms": native.wall_ms,
                "timed_out": native.timed_out,
                "model_valid": native.model_valid,
            },
        }));
    }

    let report = json!({
        "schema": "axeyum-gate-b-sweep-v1",
        "dir": dir,
        "budget_secs": budget_secs,
        "disagreements": disagreements,
        "instances": rows,
    });
    fs::write(
        out,
        serde_json::to_vec_pretty(&report).map_err(|error| error.to_string())?,
    )
    .map_err(|error| format!("write {out}: {error}"))?;
    if !disagreements.is_empty() {
        eprintln!(
            "\n*** {} DISAGREEMENT(S)/INVALID MODEL(S) — see {out} ***",
            disagreements.len()
        );
    }
    Ok(())
}

/// Parses `v <lit> <lit> ... 0` solution lines (possibly several `v` lines,
/// as CaDiCaL/Kissat emit for wide formulas) out of a captured stdout file
/// and turns them into a zero-based [`CnfAssignment`] covering
/// `variable_count` variables. Missing variables default to `false` (DIMACS
/// solution lines are permitted to omit polarity-irrelevant variables, and
/// [`CnfFormula::evaluate`] requires a value for every variable it declared).
fn parse_dimacs_solution(text: &str, variable_count: usize) -> Result<CnfAssignment, String> {
    let mut values = vec![false; variable_count];
    let mut seen_any = false;
    for line in text.lines() {
        let line = line.trim();
        let Some(rest) = line.strip_prefix('v') else {
            continue;
        };
        for token in rest.split_whitespace() {
            let lit: i64 = token
                .parse()
                .map_err(|error| format!("bad literal {token:?}: {error}"))?;
            if lit == 0 {
                continue;
            }
            seen_any = true;
            let var_index = usize::try_from(lit.unsigned_abs())
                .map_err(|error| error.to_string())?
                .checked_sub(1)
                .ok_or("literal 0 inside v line is not a variable")?;
            if var_index >= variable_count {
                return Err(format!(
                    "literal {lit} names variable {} but formula has {variable_count} variables",
                    var_index + 1
                ));
            }
            values[var_index] = lit > 0;
        }
    }
    if !seen_any {
        return Err("no 'v' solution line found in assignment file".to_string());
    }
    Ok(CnfAssignment::new(values))
}

fn cmd_verify(args: &[String]) -> Result<(), String> {
    let [cnf_path, assignment_path] = args else {
        return Err("usage: gate_b_sweep verify <cnf_file> <assignment_file>".to_string());
    };
    let formula = read_cnf(Path::new(cnf_path))?;
    let text = fs::read_to_string(assignment_path)
        .map_err(|error| format!("read {assignment_path}: {error}"))?;
    let assignment = parse_dimacs_solution(&text, formula.variable_count())?;
    match assignment.satisfies(&formula) {
        Ok(true) => Ok(()),
        Ok(false) => Err("model does not satisfy the formula".to_string()),
        Err(error) => Err(format!("evaluate failed: {error}")),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let result = match args.get(1).map(String::as_str) {
        Some("sweep") => cmd_sweep(&args[2..]),
        Some("verify") => cmd_verify(&args[2..]),
        _ => Err(
            "usage: gate_b_sweep sweep <cnf_dir> <out.json> <budget_secs>\n       gate_b_sweep verify <cnf_file> <assignment_file>"
                .to_string(),
        ),
    };
    match result {
        Ok(()) => {
            if args.get(1).map(String::as_str) == Some("verify") {
                println!("OK");
            }
        }
        Err(error) => {
            eprintln!("FAIL: {error}");
            std::process::exit(1);
        }
    }
}
