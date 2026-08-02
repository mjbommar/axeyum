//! SMT-COMP competition interface for axeyum — the exact CLI a Single-Query /
//! Model-Validation / Unsat-Core entrant must expose (SMT-COMP 2026 rules §5).
//!
//! Invocation: the benchmark file is the **first command-line argument**; the
//! solver prints exactly one of `sat` / `unsat` / `unknown` on stdout and
//! nothing verdict-shaped on stderr (the rules treat any stray `sat`/`unsat`
//! text as a reported result — §7.1.2). This wraps the existing
//! [`axeyum_solver::solve_smtlib`]; it adds no solver logic.
//!
//! An optional internal wall-clock timeout can be set with `--timeout-ms N` or
//! the `AXEYUM_TIMEOUT_MS` env var (the competition enforces the real limit
//! externally via `BenchExec`; this is a courtesy soft-stop so the binary yields
//! `unknown` instead of running unbounded when driven by the local harness).
//!
//! Run:
//! ```sh
//! cargo run -q -p axeyum-bench --example smtcomp_cli -- path/to/bench.smt2
//! ```

use std::process::ExitCode;
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let mut path: Option<String> = None;
    let mut timeout_ms: Option<u64> = std::env::var("AXEYUM_TIMEOUT_MS")
        .ok()
        .and_then(|v| v.parse().ok());

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--timeout-ms" => {
                timeout_ms = args.next().and_then(|v| v.parse().ok());
            }
            other if other.starts_with("--") => {
                // Ignore unknown flags: the competition passes only the file.
            }
            other => {
                if path.is_none() {
                    path = Some(other.to_string());
                }
            }
        }
    }

    let Some(path) = path else {
        eprintln!("usage: smtcomp_cli <benchmark.smt2> [--timeout-ms N]");
        return ExitCode::from(2);
    };

    let input = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("read error: {e}");
            return ExitCode::from(2);
        }
    };

    let mut config = SolverConfig::new();
    if let Some(ms) = timeout_ms {
        config = config.with_timeout(Duration::from_millis(ms));
    }

    // A/B levers for head-to-head probing, OFF unless explicitly asked for, so
    // the default invocation `scripts/parity-run.sh` uses stays exactly the
    // shipped configuration and recorded baselines keep their meaning.
    //
    // `cnf_inprocessing` (subsumption + BVE) and `cnf_vivify` already exist in
    // `axeyum-cnf` and are sound (model-preserving / equisatisfiable with a
    // reconstruction stack, and every `sat` is still replay-checked against the
    // original terms) — but they default to `false`, and this binary had no way
    // to turn them on, so EVERY parity measurement to date ran with them off.
    // The 2026-07-07 gap analysis puts ~9 of the residual QF_BV files in the
    // "search-bound" bucket, which is exactly what these passes target, and it
    // says the first step there is a MEASUREMENT, not a build. This makes that
    // measurement a one-line env change instead of a code edit.
    let enabled = |name: &str| std::env::var(name).is_ok_and(|v| v == "1");
    if enabled("AXEYUM_CNF_INPROCESSING") {
        config = config.with_cnf_inprocessing(true);
    }
    if enabled("AXEYUM_CNF_VIVIFY") {
        // A no-op unless inprocessing is also on; turn both on together so the
        // flag cannot silently do nothing.
        config = config.with_cnf_inprocessing(true).with_cnf_vivify(true);
    }

    // A parse or solver error is reported as `unknown` — never a wrong verdict,
    // and never a crash that the harness would read as an abort.
    let verdict = match solve_smtlib(&input, &config) {
        Ok(outcome) => match outcome.result {
            CheckResult::Sat(_) => "sat",
            CheckResult::Unsat => "unsat",
            CheckResult::Unknown(_) => "unknown",
        },
        Err(_) => "unknown",
    };

    println!("{verdict}");
    ExitCode::SUCCESS
}
