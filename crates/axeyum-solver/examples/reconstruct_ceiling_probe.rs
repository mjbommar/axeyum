//! agent-h H1: characterise the ceiling of inlined resolution reconstruction.
//!
//! Pipeline: DIMACS -> `solve_with_drat_proof` -> `elaborate_drat_to_lrat_backward`
//! -> `lrat_to_alethe` -> `reconstruct_resolution_proof` (kernel-checked `False`).
//!
//! Reports, per stage: step counts, kernel expression-arena growth, peak RSS,
//! wall time, and the exact failure text when reconstruction declines.

#![allow(clippy::too_many_lines)]
// Measurement harness for the reconstruction ceiling; wide `main` and lossy
// ratio casts are reporting concerns, not correctness ones.

use std::time::Instant;

use axeyum_cnf::{
    AletheCommand, DratStep, ProofSolveOutcome, elaborate_drat_to_lrat,
    elaborate_drat_to_lrat_backward, lrat_to_alethe, parse_dimacs, solve_with_drat_proof,
};
use axeyum_solver::{ReconstructCtx, reconstruct_resolution_proof};

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

/// Monotone probe of the kernel expression arena: allocate one never-seen node
/// and read back its dense index. `ExprId`s are assigned in insertion order, so
/// this is the arena length at the moment of the call.
fn arena_len(ctx: &mut ReconstructCtx, tag: u32) -> usize {
    ctx.kernel_mut().bvar(u32::MAX - tag).index()
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: reconstruct_ceiling_probe <cnf> [--forward-lrat]");
    let forward = args.any(|a| a == "--forward-lrat");

    let text = std::fs::read_to_string(&path).expect("read cnf");
    let formula = parse_dimacs(&text).expect("parse dimacs");
    println!(
        "instance\t{}\tvars\t{}\tclauses\t{}",
        path,
        formula.variable_count(),
        formula.clauses().len()
    );

    let t0 = Instant::now();
    let drat: Vec<DratStep> = match solve_with_drat_proof(&formula) {
        ProofSolveOutcome::Unsat(p) => p,
        other => {
            println!("solve\tNOT-UNSAT\t{other:?}");
            return;
        }
    };
    let solve_s = t0.elapsed().as_secs_f64();
    let adds = drat
        .iter()
        .filter(|s| matches!(s, DratStep::Add(_)))
        .count();
    println!(
        "drat\tsteps\t{}\tadds\t{}\tsolve_s\t{:.3}\trss_kb\t{}",
        drat.len(),
        adds,
        solve_s,
        vm_rss_kb()
    );

    let t1 = Instant::now();
    let lrat = if forward {
        elaborate_drat_to_lrat(&formula, &drat)
    } else {
        elaborate_drat_to_lrat_backward(&formula, &drat)
    };
    let lrat = match lrat {
        Ok(l) => l,
        Err(e) => {
            println!("lrat\tFAILED\t{e:?}");
            return;
        }
    };
    let lrat_adds = lrat
        .iter()
        .filter(|s| matches!(s, axeyum_cnf::LratStep::Add { .. }))
        .count();
    let hint_total: usize = lrat
        .iter()
        .map(|s| match s {
            axeyum_cnf::LratStep::Add { hints, .. } => hints.len(),
            axeyum_cnf::LratStep::Delete { .. } => 0,
        })
        .sum();
    println!(
        "lrat\tsteps\t{}\tadds\t{}\thints\t{}\telab_s\t{:.3}\trss_kb\t{}",
        lrat.len(),
        lrat_adds,
        hint_total,
        t1.elapsed().as_secs_f64(),
        vm_rss_kb()
    );

    let t2 = Instant::now();
    let commands = lrat_to_alethe(&formula, &lrat);
    let assumes = commands
        .iter()
        .filter(|c| matches!(c, AletheCommand::Assume { .. }))
        .count();
    let res_steps = commands
        .iter()
        .filter(|c| matches!(c, AletheCommand::Step { rule, .. } if rule == "resolution"))
        .count();
    println!(
        "alethe\tcommands\t{}\tassumes\t{}\tresolution\t{}\tbuild_s\t{:.3}\trss_kb\t{}",
        commands.len(),
        assumes,
        res_steps,
        t2.elapsed().as_secs_f64(),
        vm_rss_kb()
    );

    // Free the DRAT before reconstruction so the reported peak attributes to the
    // reconstruction rather than to the producer.
    drop(drat);
    drop(lrat);

    let mut ctx = ReconstructCtx::new();
    let arena_before = arena_len(&mut ctx, 1);
    let rss_before = vm_rss_kb();
    let t3 = Instant::now();
    let result = reconstruct_resolution_proof(&mut ctx, &commands);
    let recon_s = t3.elapsed().as_secs_f64();
    let arena_after = arena_len(&mut ctx, 2);
    println!(
        "reconstruct\tok\t{}\tarena_before\t{}\tarena_after\t{}\tarena_delta\t{}\trss_before_kb\t{}\trss_after_kb\t{}\thwm_kb\t{}\trecon_s\t{:.3}",
        result.is_ok(),
        arena_before,
        arena_after,
        arena_after - arena_before,
        rss_before,
        vm_rss_kb(),
        vm_hwm_kb(),
        recon_s
    );
    match result {
        Ok(term) => println!("reconstruct\tterm\t{}", term.index()),
        Err(e) => println!("reconstruct\tERROR\t{e}"),
    }
}
