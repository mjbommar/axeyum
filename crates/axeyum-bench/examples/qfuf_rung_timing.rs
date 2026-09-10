//! Times each rung of the `QF_UF` ladder on one file, in isolation.
//!
//! `axeyum_cli` reports one verdict for a ladder of four rungs, so a 24 s
//! `unknown` says nothing about WHICH rung spent the budget. This calls the
//! rungs directly, each with its own fresh arena and its own full budget, and
//! prints what each one does on its own.
//!
//! Usage: `qfuf_rung_timing <file.smt2> [budget_ms]`

use std::time::{Duration, Instant};

use axeyum_solver::theories::cdclt_diagnostics::{TheoryLayerStatsGuard, last_theory_layer_stats};
use axeyum_solver::theories::uninterpreted_functions::{
    check_qf_uf_online_cdclt, check_qf_uf_with_config, last_euf_online_atom_stats,
};
use axeyum_solver::{CheckResult, SolverConfig};

fn verdict(r: &CheckResult) -> String {
    match r {
        CheckResult::Sat(_) => "sat".to_owned(),
        CheckResult::Unsat => "unsat".to_owned(),
        CheckResult::Unknown(reason) => format!("unknown[{}]", reason.detail),
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: qfuf_rung_timing <file.smt2> [budget_ms]");
    let budget_ms: u64 = args
        .next()
        .map_or(24_000, |a| a.parse().expect("budget_ms"));
    let text = std::fs::read_to_string(&path).expect("read");

    let script = axeyum_smtlib::parse_script(&text).expect("parse");
    let config = SolverConfig::default().with_timeout(Duration::from_millis(budget_ms));

    println!("file      : {path}");
    println!("assertions: {}", script.assertions.len());
    println!("budget    : {budget_ms} ms\n");

    {
        let mut a = script.arena.clone();
        let asserts = script.assertions.clone();
        let _atoms =
            axeyum_solver::theories::uninterpreted_functions::EufOnlineAtomStatsGuard::enable();
        let _layers = TheoryLayerStatsGuard::enable();
        let t = Instant::now();
        let r = check_qf_uf_online_cdclt(&mut a, &asserts, &config);
        let secs = t.elapsed().as_secs_f64();
        println!("euf-online  {secs:>8.2}s  {}", verdict(&r));
        println!("  atoms: {:?}", last_euf_online_atom_stats());
        if let Some(s) = last_theory_layer_stats() {
            println!(
                "  decisions={} theory_conflicts={} theory_props={} restarts={} learned={} lits={} final_checks={}",
                s.decisions,
                s.theory_conflicts,
                s.theory_propagations,
                s.restarts,
                s.learned_clauses,
                s.learned_literals,
                s.final_checks
            );
            println!(
                "  bool_prop={:?} t_assert={:?} t_prop={:?} pushpop={:?} analysis={:?} final={:?} explain={:?}",
                s.boolean_propagate,
                s.theory_assert,
                s.theory_propagate,
                s.theory_push_pop,
                s.conflict_analysis,
                s.theory_final_check,
                s.theory_explain
            );
        } else {
            println!("  (no theory layer stats)");
        }
    }
    {
        let mut a = script.arena.clone();
        let asserts = script.assertions.clone();
        let t = Instant::now();
        let r = check_qf_uf_with_config(&mut a, &asserts, &config);
        println!(
            "euf-offline {:>8.2}s  {}",
            t.elapsed().as_secs_f64(),
            verdict(&r)
        );
    }
}
