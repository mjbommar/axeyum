//! Gate (b) measurement: does the best pure-Rust SAT adapter (BatSat) or the
//! native proof-producing CDCL core (`solve_with_drat_proof`) show a
//! consistent material gap to CaDiCaL/Kissat on Axeyum-generated CNF?
//!
//! Two subcommands, deliberately narrow:
//!
//! - `sweep <cnf_dir> <out.tsv> <budget_secs> [max_files]` runs BatSat
//!   ([`solve_with_rustsat_batsat_timeout`]) and the native core
//!   ([`solve_with_drat_proof_within`]) over `*.cnf` files in `cnf_dir`, each
//!   under the same per-file wall-clock budget, and **appends** one row per
//!   file to `out.tsv`. A file whose name already appears in `out.tsv` is
//!   skipped, so the same command can be re-run in bounded batches
//!   (`max_files` caps how many new files this invocation processes) until
//!   the directory is fully covered — a long sweep becomes a sequence of
//!   short, resumable, foreground tool calls instead of one process that
//!   outruns any single call's timeout. A `sat` verdict is checked against
//!   the formula with [`CnfFormula::evaluate`] before being recorded — an
//!   invalid model is a hard error, not a silent `sat`. The two engines'
//!   verdicts are cross-checked against each other; a disagreement (one says
//!   `sat`, the other `unsat`) is printed to stderr and turns the process
//!   exit into a failure, since that is a P0 soundness finding, not a
//!   performance number.
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
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfAssignment, CnfFormula, ProofSolveOutcome, SatResult, parse_dimacs,
    solve_with_drat_proof_within, solve_with_rustsat_batsat_timeout,
};

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

/// Reads the file names already present in column 1 of an existing sweep TSV
/// (empty set if the file does not exist yet), so a resumed batch skips work
/// a prior invocation already committed to disk.
fn read_done_set(tsv_path: &Path) -> std::collections::HashSet<String> {
    let mut done = std::collections::HashSet::new();
    if let Ok(text) = fs::read_to_string(tsv_path) {
        for (i, line) in text.lines().enumerate() {
            if i == 0 {
                continue; // header
            }
            if let Some(name) = line.split('\t').next()
                && !name.is_empty()
            {
                done.insert(name.to_string());
            }
        }
    }
    done
}

fn parse_sweep_args(
    args: &[String],
) -> Result<(PathBuf, PathBuf, Duration, Option<usize>), String> {
    let (dir, out, budget_secs, max_files) = match args {
        [dir, out, budget_secs] => (dir, out, budget_secs, None),
        [dir, out, budget_secs, max_files] => (
            dir,
            out,
            budget_secs,
            Some(
                max_files
                    .parse::<usize>()
                    .map_err(|error| format!("invalid max_files: {error}"))?,
            ),
        ),
        _ => {
            return Err(
                "usage: gate_b_sweep sweep <cnf_dir> <out.tsv> <budget_secs> [max_files]"
                    .to_string(),
            );
        }
    };
    let budget_secs: f64 = budget_secs
        .parse()
        .map_err(|error| format!("invalid budget_secs: {error}"))?;
    Ok((
        PathBuf::from(dir),
        PathBuf::from(out),
        Duration::from_secs_f64(budget_secs),
        max_files,
    ))
}

/// Runs both engines on one CNF file, appends its row to `file`, and returns
/// any disagreement/invalid-model messages found for this file.
fn process_one_file(
    path: &Path,
    name: &str,
    budget: Duration,
    file: &mut fs::File,
) -> Result<Vec<String>, String> {
    let mut findings = Vec::new();
    let formula = match read_cnf(path) {
        Ok(f) => f,
        Err(error) => {
            eprintln!("  SKIP: {error}");
            return Ok(findings);
        }
    };
    let batsat = run_batsat(&formula, budget);
    let native = run_native(&formula, budget);

    if matches!(
        (batsat.verdict, native.verdict),
        ("sat", "unsat") | ("unsat", "sat")
    ) {
        let msg = format!(
            "DISAGREEMENT on {name}: batsat={} native={}",
            batsat.verdict, native.verdict
        );
        eprintln!("  !!! {msg}");
        findings.push(msg);
    }
    for (engine, row) in [("batsat", &batsat), ("native", &native)] {
        if row.verdict == "sat" && row.model_valid != Some(true) {
            let msg = format!("{engine} sat with invalid model on {name}");
            eprintln!("  !!! {msg}");
            findings.push(msg);
        }
    }

    writeln!(
        file,
        "{name}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        formula.variable_count(),
        formula.clauses().len(),
        batsat.verdict,
        batsat.wall_ms,
        batsat.timed_out,
        batsat
            .model_valid
            .map(|v| v.to_string())
            .unwrap_or_default(),
        native.verdict,
        native.wall_ms,
        native.timed_out,
        native
            .model_valid
            .map(|v| v.to_string())
            .unwrap_or_default(),
    )
    .map_err(|error| format!("write row: {error}"))?;
    file.flush().map_err(|error| error.to_string())?;
    Ok(findings)
}

fn cmd_sweep(args: &[String]) -> Result<(), String> {
    let (dir, out_path, budget, max_files) = parse_sweep_args(args)?;
    let out = out_path.display().to_string();

    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .map_err(|error| format!("read {}: {error}", dir.display()))?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "cnf"))
        .collect();
    paths.sort();
    if paths.is_empty() {
        return Err(format!("no .cnf files in {}", dir.display()));
    }

    let header_needed = !out_path.exists();
    let done = read_done_set(&out_path);
    let mut remaining: Vec<PathBuf> = paths
        .into_iter()
        .filter(|path| {
            let name = path
                .file_name()
                .map(|n| n.to_string_lossy().into_owned())
                .unwrap_or_default();
            !done.contains(&name)
        })
        .collect();
    if let Some(max_files) = max_files {
        remaining.truncate(max_files);
    }
    if remaining.is_empty() {
        eprintln!("nothing to do: all files already present in {out}");
        return Ok(());
    }

    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&out_path)
        .map_err(|error| format!("open {out}: {error}"))?;
    if header_needed {
        writeln!(
            file,
            "file\tvariables\tclauses\tbatsat_verdict\tbatsat_ms\tbatsat_timed_out\tbatsat_model_valid\tnative_verdict\tnative_ms\tnative_timed_out\tnative_model_valid"
        )
        .map_err(|error| format!("write header {out}: {error}"))?;
        file.flush().map_err(|error| error.to_string())?;
    }

    let total = remaining.len();
    let mut disagreements = Vec::new();
    for (i, path) in remaining.iter().enumerate() {
        let name = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        eprintln!("[{}/{total}] {name}", i + 1);
        disagreements.extend(process_one_file(path, &name, budget, &mut file)?);
    }

    if !disagreements.is_empty() {
        eprintln!(
            "\n*** {} DISAGREEMENT(S)/INVALID MODEL(S) in this batch — see stderr above ***",
            disagreements.len()
        );
        return Err(format!(
            "{} disagreement(s)/invalid model(s), see stderr",
            disagreements.len()
        ));
    }
    eprintln!("batch done: {total} file(s) processed, appended to {out}");
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
            "usage: gate_b_sweep sweep <cnf_dir> <out.tsv> <budget_secs> [max_files]\n       gate_b_sweep verify <cnf_file> <assignment_file>"
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
