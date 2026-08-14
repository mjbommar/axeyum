//! agent-h H2 differential: inlined vs compact clausal reconstruction.
//!
//! For one DIMACS instance, runs the pipeline twice — through
//! `reconstruct_resolution_proof` (inlined) and through
//! `reconstruct_resolution_proof_compact` (backward-sliced + CPS + theorem
//! aliases) — and compares, in this order of severity:
//!
//! 1. Both must reach a kernel-checked `False`.
//! 2. **Every hypothesis axiom of each route must be an actual clause of the
//!    input CNF.** A `False` proved from axioms that are not the input clauses
//!    is the dangerous failure; `infer` cannot see it.
//! 3. The compact footprint must be a subset of the inlined one (slicing may
//!    drop unused input clauses; it must never invent one).
//! 4. Neither footprint may be empty.

#![allow(clippy::too_many_lines)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_precision_loss)]
// Measurement harness for the reconstruction ceiling; wide `main` and lossy
// ratio casts are reporting concerns, not correctness ones.

use std::collections::BTreeSet;
use std::time::Instant;

use axeyum_cnf::{
    AletheCommand, CnfFormula, DratStep, ProofSolveOutcome, elaborate_drat_to_lrat_backward,
    lrat_to_alethe, parse_dimacs, solve_with_drat_proof,
};
use axeyum_solver::{
    ReconstructCtx, declared_assumption_clauses, reconstruct_resolution_proof,
    reconstruct_resolution_proof_compact,
};

fn vm_hwm_kb() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .and_then(|l| l.split_whitespace().nth(1).and_then(|v| v.parse().ok()))
        })
        .unwrap_or(0)
}

fn vm_rss_kb() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmRSS:"))
                .and_then(|l| l.split_whitespace().nth(1).and_then(|v| v.parse().ok()))
        })
        .unwrap_or(0)
}

fn arena_len(ctx: &mut ReconstructCtx, tag: u32) -> usize {
    ctx.kernel_mut().bvar(u32::MAX - tag).index()
}

/// The source formula's clauses in exactly the `±v<k>` key shape
/// `declared_assumption_clauses` produces, so footprint membership is an exact
/// set test rather than a resemblance.
fn formula_clause_keys(formula: &CnfFormula) -> BTreeSet<String> {
    formula
        .clauses()
        .iter()
        .map(|clause| {
            let mut lits: Vec<String> = clause
                .lits()
                .iter()
                .map(|lit| {
                    format!(
                        "{}v{}",
                        if lit.is_negated() { '-' } else { '+' },
                        lit.var().index()
                    )
                })
                .collect();
            lits.sort();
            lits.dedup();
            lits.join(",")
        })
        .collect()
}

struct RouteReport {
    ok: bool,
    detail: String,
    arena: usize,
    rss_delta_kb: i64,
    seconds: f64,
    footprint: Vec<String>,
}

fn run_route(commands: &[AletheCommand], compact: bool) -> RouteReport {
    let mut ctx = ReconstructCtx::new();
    let arena_before = arena_len(&mut ctx, 1);
    let rss_before = vm_rss_kb() as i64;
    let start = Instant::now();
    let result = if compact {
        reconstruct_resolution_proof_compact(&mut ctx, commands)
    } else {
        reconstruct_resolution_proof(&mut ctx, commands)
    };
    let seconds = start.elapsed().as_secs_f64();
    let arena_after = arena_len(&mut ctx, 2);
    let rss_after = vm_rss_kb() as i64;
    RouteReport {
        ok: result.is_ok(),
        detail: match &result {
            Ok(_) => "False".to_owned(),
            Err(e) => e.to_string(),
        },
        arena: arena_after - arena_before,
        rss_delta_kb: rss_after - rss_before,
        seconds,
        footprint: declared_assumption_clauses(&ctx),
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: reconstruct_differential_probe <cnf> [--compact-only]");
    let compact_only = args.any(|a| a == "--compact-only");

    let text = std::fs::read_to_string(&path).expect("read cnf");
    let formula = parse_dimacs(&text).expect("parse dimacs");
    let source_clauses = formula_clause_keys(&formula);

    let drat: Vec<DratStep> = match solve_with_drat_proof(&formula) {
        ProofSolveOutcome::Unsat(p) => p,
        other => {
            println!("{path}\tsolve\tNOT-UNSAT\t{other:?}");
            return;
        }
    };
    let lrat = match elaborate_drat_to_lrat_backward(&formula, &drat) {
        Ok(l) => l,
        Err(e) => {
            println!("{path}\tlrat\tFAILED\t{e:?}");
            return;
        }
    };
    let hint_total: usize = lrat
        .iter()
        .map(|s| match s {
            axeyum_cnf::LratStep::Add { hints, .. } => hints.len(),
            axeyum_cnf::LratStep::Delete { .. } => 0,
        })
        .sum();
    let commands = lrat_to_alethe(&formula, &lrat);
    let res_steps = commands
        .iter()
        .filter(|c| matches!(c, AletheCommand::Step { rule, .. } if rule == "resolution"))
        .count();
    drop(drat);
    drop(lrat);

    println!(
        "{path}\tinput\tclauses\t{}\tres_steps\t{res_steps}\thints\t{hint_total}",
        formula.clauses().len()
    );

    let compact = run_route(&commands, true);
    println!(
        "{path}\tcompact\tok\t{}\tarena\t{}\trss_kb\t{}\ts\t{:.3}\tassumes\t{}\t{}",
        compact.ok,
        compact.arena,
        compact.rss_delta_kb,
        compact.seconds,
        compact.footprint.len(),
        compact.detail
    );

    // Audit 2, on the compact route regardless of whether the inlined one runs.
    let compact_set: BTreeSet<String> = compact.footprint.iter().cloned().collect();
    let alien: Vec<&String> = compact_set
        .iter()
        .filter(|k| !source_clauses.contains(*k))
        .collect();
    println!(
        "{path}\taudit\tcompact_alien_axioms\t{}\tcompact_footprint\t{}\tsource_clauses\t{}",
        alien.len(),
        compact_set.len(),
        source_clauses.len()
    );
    for k in alien.iter().take(5) {
        println!("{path}\taudit\tALIEN\t{k}");
    }
    if compact.ok && compact_set.is_empty() {
        println!("{path}\taudit\tFAIL\tcompact proved False from an empty hypothesis set");
    }

    if compact_only {
        println!("{path}\thwm_kb\t{}", vm_hwm_kb());
        return;
    }

    let inlined = run_route(&commands, false);
    println!(
        "{path}\tinlined\tok\t{}\tarena\t{}\trss_kb\t{}\ts\t{:.3}\tassumes\t{}\t{}",
        inlined.ok,
        inlined.arena,
        inlined.rss_delta_kb,
        inlined.seconds,
        inlined.footprint.len(),
        inlined.detail
    );
    let inlined_set: BTreeSet<String> = inlined.footprint.iter().cloned().collect();
    let inlined_alien: Vec<&String> = inlined_set
        .iter()
        .filter(|k| !source_clauses.contains(*k))
        .collect();
    println!(
        "{path}\taudit\tinlined_alien_axioms\t{}\tinlined_footprint\t{}",
        inlined_alien.len(),
        inlined_set.len()
    );

    if inlined.ok && compact.ok {
        let escaped: Vec<&String> = compact_set.difference(&inlined_set).collect();
        let dropped = inlined_set.difference(&compact_set).count();
        println!(
            "{path}\tdifferential\tcompact_not_in_inlined\t{}\tinlined_not_in_compact\t{}\tverdict\t{}",
            escaped.len(),
            dropped,
            if escaped.is_empty() {
                "SUBSET-OK"
            } else {
                "STATEMENT-MISMATCH"
            }
        );
        for k in escaped.iter().take(5) {
            println!("{path}\tdifferential\tESCAPED\t{k}");
        }
        if inlined.arena > 0 {
            println!(
                "{path}\tspeedup\tarena\t{:.2}x\ttime\t{:.2}x",
                inlined.arena as f64 / compact.arena.max(1) as f64,
                inlined.seconds / compact.seconds.max(1e-9)
            );
        }
    }
    println!("{path}\thwm_kb\t{}", vm_hwm_kb());
}
