//! Emit the rendered Lean refutation module for an SMT-LIB query, so an
//! **independent** checker can re-derive the binding from the module's
//! hypothesis axioms back to the query's `(assert …)` lines.
//!
//! # Why this exists
//!
//! `docs/prover-track/research/13-residual-trust-surface.md` ranks the four
//! things a third party must believe. Item 3 — *"the transcription from SMT-LIB
//! into the rendered statement"* — is the one with no mechanical check:
//!
//! > we can prove the rendered proposition, and we cannot yet mechanically show
//! > the rendered proposition is what the input file said.
//!
//! A module rendered from a mis-transcribed constraint still typechecks, still
//! reports a clean axiom footprint, and is still worthless. `scripts/`'s
//! `check-lra-hypothesis-binding.py` closes that by parsing **this** output and
//! the **original `.smt2` text** with two implementations that share no code
//! with each other or with this crate, and requiring every rendered
//! `axeyum.reconstruct.lra.hyp._N` axiom to be a faithful translation of one of
//! the query's assertions.
//!
//! This binary is deliberately dumb: it must not do any comparing, because a
//! checker that reuses the renderer's own notion of "the same constraint"
//! cannot catch the renderer being wrong. It parses, solves, renders, and
//! prints. All judgement lives in the Python side.
//!
//! # Usage
//!
//! ```sh
//! cargo run --release -q -p axeyum-solver --features full \
//!     --example lean_hypothesis_binding_dump -- <query.smt2> [--core]
//! ```
//!
//! Prints the rendered module on stdout and one `BINDING_DUMP|…` provenance
//! line on stderr. `--core` reconstructs a minimized unsat core instead of the
//! full assertion list (a subset refutation is still a refutation of the whole
//! query, and some routes only reconstruct the core); the stderr line always
//! records which spine was used and, for `--core`, the **assertion indices** the
//! core selected, so the checker can restrict its source side to exactly those.

use std::process::ExitCode;

use axeyum_smtlib::parse_script;
use axeyum_solver::{SolverConfig, prove_unsat_to_lean_theory_module, unsat_core};

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("lean_hypothesis_binding_dump: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let mut path: Option<String> = None;
    let mut want_core = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--core" => want_core = true,
            other if other.starts_with("--") => {
                return Err(format!("unknown flag `{other}`"));
            }
            other => path = Some(other.to_owned()),
        }
    }
    let path = path.ok_or("usage: lean_hypothesis_binding_dump <query.smt2> [--core]")?;
    let text = std::fs::read_to_string(&path).map_err(|e| format!("read {path}: {e}"))?;
    let mut script = parse_script(&text).map_err(|e| format!("parse {path}: {e}"))?;

    // Which assertion indices the refutation is allowed to rest on. Printed, so
    // the checker's source side is exactly this subset and an unmatched
    // hypothesis cannot be excused by "it must have come from some other row".
    let indices: Vec<usize> = if want_core {
        let config = SolverConfig::default();
        unsat_core(&mut script.arena, &script.assertions, &config)
            .map_err(|e| format!("unsat_core: {e}"))?
            .ok_or("unsat_core: the query is not unsat (no core)")?
    } else {
        (0..script.assertions.len()).collect()
    };
    let spine: Vec<_> = indices.iter().map(|&i| script.assertions[i]).collect();

    let (fragment, module) = prove_unsat_to_lean_theory_module(&mut script.arena, &spine)
        .map_err(|e| format!("prove_unsat_to_lean_theory_module: {e}"))?;

    let joined = indices
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(",");
    eprintln!(
        "BINDING_DUMP|instance={path}|spine={}|fragment={fragment:?}|assertions={}|indices={joined}",
        if want_core { "core" } else { "all" },
        indices.len()
    );
    print!("{module}");
    Ok(())
}
