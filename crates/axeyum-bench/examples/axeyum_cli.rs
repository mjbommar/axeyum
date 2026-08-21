//! A general-purpose SMT-LIB 2 driver — the way a stranger expects to run a solver.
//!
//! # Why this exists beside `smtcomp_cli`
//!
//! `smtcomp_cli` is the **competition** interface and must stay single-query:
//! SMT-COMP 2026 §7.1.2 treats any stray `sat`/`unsat` text as a reported
//! result, so a binary that prints one verdict per `check-sat` cannot also be a
//! Single-Query entrant. That is a real constraint, not a preference.
//!
//! The consequence, measured 2026-08-21 and recorded as gap #3 of
//! [`docs/plan/gap-analysis-smt-solvers-2026-08-21.md`]: on a perfectly ordinary
//! script the shipped CLI answered **`unknown`** where `z3` answered three
//! verdicts.
//!
//! ```text
//! (assert (> x 5)) (check-sat) (push 1) (assert (< x 3)) (check-sat) (pop 1) (check-sat)
//!
//!   z3:      sat / unsat / sat
//!   axeyum:  unknown
//! ```
//!
//! Nothing was missing from the solver. [`solve_smtlib_incremental`] already
//! decides exactly this — `push`/`pop` scoping, `check-sat-assuming`, one result
//! per query, documented under ADR-0009 and ADR-0018 — and **nothing
//! user-facing reached it.** The capability existed and the front door did not.
//!
//! # Interface
//!
//! ```sh
//! cargo run -q -p axeyum-bench --example axeyum_cli -- script.smt2
//! cargo run -q -p axeyum-bench --example axeyum_cli -- --timeout-ms 5000 script.smt2
//! cat script.smt2 | cargo run -q -p axeyum-bench --example axeyum_cli -- -
//! ```
//!
//! One line per `check-sat`, in order, on stdout: `sat`, `unsat` or `unknown`.
//! Diagnostics go to stderr. Exit status is `0` when every query was answered
//! (including `unknown` — that is a first-class result here, not an error), `2`
//! for a usage or read error, `3` when the script could not be parsed or a query
//! failed.
//!
//! # What this does NOT do yet, said plainly
//!
//! `get-model`, `get-value`, `get-unsat-core` and `get-proof` are **not**
//! answered here. Library entry points exist for each
//! ([`axeyum_solver::solve_smtlib_get_model`] and siblings), but each decides a
//! whole script rather than a command in the middle of one, so wiring them into
//! a per-command interpreter is a separate change and not a wrapper. Until then
//! they are silently ignored by the script walk, exactly as they were before —
//! this file does not make that better and does not pretend to.
//!
//! `set-option` is likewise still inert.

use std::process::ExitCode;
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib_incremental};

fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let mut path: Option<String> = None;
    let mut timeout_ms: Option<u64> = std::env::var("AXEYUM_TIMEOUT_MS")
        .ok()
        .and_then(|v| v.parse().ok());

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--timeout-ms" => timeout_ms = args.next().and_then(|v| v.parse().ok()),
            "--help" | "-h" => {
                eprintln!(
                    "usage: axeyum_cli <script.smt2 | -> [--timeout-ms N]\n\
                     prints one verdict per (check-sat), in order"
                );
                return ExitCode::SUCCESS;
            }
            other if other.starts_with("--") => {
                eprintln!("unknown flag {other}");
                return ExitCode::from(2);
            }
            other => {
                if path.is_none() {
                    path = Some(other.to_owned());
                }
            }
        }
    }

    let Some(path) = path else {
        eprintln!("usage: axeyum_cli <script.smt2 | -> [--timeout-ms N]");
        return ExitCode::from(2);
    };

    let input = if path == "-" {
        std::io::read_to_string(std::io::stdin())
    } else {
        std::fs::read_to_string(&path)
    };
    let input = match input {
        Ok(text) => text,
        Err(error) => {
            eprintln!("read error: {error}");
            return ExitCode::from(2);
        }
    };

    let mut config = SolverConfig::new();
    if let Some(ms) = timeout_ms {
        config = config.with_timeout(Duration::from_millis(ms));
    }

    match solve_smtlib_incremental(&input, &config) {
        Ok(results) => {
            // A script with no `check-sat` is well-formed and asks nothing; it
            // prints nothing and succeeds, which is what z3 does.
            for result in &results {
                println!("{}", verdict(result));
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(3)
        }
    }
}
