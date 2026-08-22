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
//! decided exactly this, and nothing user-facing reached it.
//!
//! # Interface
//!
//! ```sh
//! cargo run -q -p axeyum-bench --example axeyum_cli -- script.smt2
//! cargo run -q -p axeyum-bench --example axeyum_cli -- --timeout-ms 5000 script.smt2
//! cat script.smt2 | cargo run -q -p axeyum-bench --example axeyum_cli -- -
//! ```
//!
//! One line per *output* command, in script order, on stdout. Diagnostics go to
//! stderr. Exit status is `0` when every command was answered (including
//! `unknown` — that is a first-class result here, not an error), `2` for a usage
//! or read error, and `3` when the script could not be parsed, a query failed,
//! or any command produced an SMT-LIB `(error …)` response (matching `z3`,
//! which also exits nonzero on an in-script error).
//!
//! # What is answered
//!
//! | command | answer |
//! |---|---|
//! | `check-sat`, `check-sat-assuming` | `sat` / `unsat` / `unknown` |
//! | `get-model` | `( (define-fun x () Int 6) … )` after a `sat` |
//! | `get-value (t …)` | `((t v) …)` after a `sat`, each term echoed as written |
//! | `get-unsat-core` | `(a1 a2)` after an `unsat`, needs `:produce-unsat-cores` |
//! | `get-proof` | a textual Alethe proof after an `unsat`, needs `:produce-proofs` |
//! | `echo` | its argument, verbatim |
//! | `get-assertions` | `(t1 t2 …)`, the active stack at that point |
//! | `set-logic` | nothing for a real logic name, `unsupported` otherwise |
//! | `set-option` | nothing for an honored option, `unsupported` otherwise |
//! | `get-info`, `get-option`, `get-assignment`, `get-objectives`, `get-unsat-assumptions` | `unsupported` |
//!
//! The honored options are `:produce-models`, `:produce-unsat-cores`,
//! `:produce-proofs`, `:print-success` and `:timeout`. **Every other option
//! draws `unsupported`**, which is the point of this table: before ADR-0541 an
//! unknown `set-option` was accepted and ignored, and a consumer could not tell
//! an option that worked from one that did nothing. cvc5 1.3.4 answers
//! `unsupported` here too; Z3 4.13.3 raises an error instead, and SMT-LIB §4.1.7
//! prescribes `unsupported`.
//!
//! `--timeout-ms` is a **ceiling** on the script's `(set-option :timeout …)`,
//! not a default it overrides: a script cannot ask for more budget than the
//! operator granted.
//!
//! # What this still does NOT do, said plainly
//!
//! - **`(exit)` does not stop the walk.** The parser reads the whole script
//!   before anything is decided, so honoring `exit` would drop trailing
//!   commands and change the verdict stream of every corpus file that ends in
//!   one. Commands after an `(exit)` are executed here and are not by `z3`.
//! - **`set-logic` is recognized, not enforced.** A name that is not an SMT-LIB
//!   logic draws `unsupported` (as in `z3`); a query that violates its declared
//!   logic is still decided. The measurement behind that choice is
//!   `logic_conformance_would_reject_committed_corpus_files` in
//!   `crates/axeyum-solver/tests/smtlib_session.rs`.
//! - **`get-model` and `get-value` decline rather than guess.** A value whose
//!   sort has no re-parseable SMT-LIB spelling here — an uninterpreted carrier
//!   token, a datatype, an array, an algebraic real — makes the whole command
//!   `unsupported`. In particular a **`QF_UF` model is refused**, because z3's
//!   `U!val!0` tokens are model artifacts rather than terms and inventing our
//!   own spelling would hand a consumer something that looks like a model and
//!   is not one.
//! - **`define-fun-rec`, `define-funs-rec`, `reset`, and `declare-sort` with
//!   arity ≥ 1** are parse errors, not silent no-ops (they always were).

use std::process::ExitCode;
use std::time::Duration;

use axeyum_solver::{CheckResult, SmtLibResponse, SolverConfig, solve_smtlib_session};

fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

/// Prints one response and reports whether it was an SMT-LIB `(error …)`.
///
/// The return value is what makes the exit status depend on what the run
/// *found* rather than on the run completing — the standing rule that a checker
/// whose status cannot fail is worse than none.
fn emit(response: &SmtLibResponse) -> bool {
    match response {
        SmtLibResponse::CheckSat(result) => {
            println!("{}", verdict(result));
            false
        }
        // One arm, three commands: a model block, an Alethe proof and an echo
        // are each already the exact text SMT-LIB says to print.
        SmtLibResponse::Model(text) | SmtLibResponse::Proof(text) | SmtLibResponse::Echo(text) => {
            println!("{text}");
            false
        }
        SmtLibResponse::Values(pairs) => {
            let body: Vec<String> = pairs
                .iter()
                .map(|(term, value)| format!("({term} {value})"))
                .collect();
            println!("({})", body.join(" "));
            false
        }
        // One arm, two commands: SMT-LIB prints both an unsat core and an
        // assertion stack as a bare parenthesised list.
        SmtLibResponse::UnsatCore(items) | SmtLibResponse::Assertions(items) => {
            println!("({})", items.join(" "));
            false
        }
        SmtLibResponse::Success => {
            println!("success");
            false
        }
        SmtLibResponse::Unsupported { command, detail } => {
            println!("unsupported");
            eprintln!("; {command}: {detail}");
            false
        }
        SmtLibResponse::Error { command, message } => {
            println!("(error \"{command}: {message}\")");
            true
        }
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
                     prints one SMT-LIB response per output command, in order"
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

    match solve_smtlib_session(&input, &config) {
        Ok(responses) => {
            // A script with no output command is well-formed and asks nothing; it
            // prints nothing and succeeds, which is what z3 does.
            let mut errored = false;
            for response in &responses {
                errored |= emit(response);
            }
            if errored {
                ExitCode::from(3)
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::from(3)
        }
    }
}
