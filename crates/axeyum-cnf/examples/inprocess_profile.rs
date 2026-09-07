//! Does inprocessing move **propagations per conflict**? The A/B driver.
//!
//! ```sh
//! cargo run --release -p axeyum-cnf --example inprocess_profile -- \
//!     <file.cnf> [max_conflicts] [off|subsume|vivify|bve|preprocess|preprocess-full]
//! ```
//!
//! Deliberately a **separate binary** from `boolean_core_profile`, not an extra
//! argument to it: that example is the reproduction recipe for
//! `docs/research/12-performance/bench-boolean-core-2026-09-07.md`, and a tool
//! whose recipe still runs but no longer produces the numbers the diary quotes
//! is worse than a second file.
//!
//! # What it reports and why
//!
//! The hypothesis under test is about propagation **volume**, not wall time:
//! `conflicts/s = propagations/s ÷ propagations/conflict`, and the measured
//! deficit against Kissat is entirely in the second factor. So
//! `propagations_per_conflict` is the headline and every timing figure is
//! secondary.
//!
//! `inprocess_seconds` is reported apart from `search_seconds` because they
//! answer different questions. A reduction that halves propagations per conflict
//! and costs more than the search it saved is a real result about the pass's
//! *cost*, and folding the two together would hide it.
//!
//! The search runs at a **fixed conflict budget**, so both arms analyse the same
//! number of conflicts and the per-conflict figures are not confounded by one
//! arm simply searching further. Note what that does *not* control: the two arms
//! search different formulas, so unlike a trajectory-preserving A/B the
//! conflicts themselves are not the same conflicts. That is inherent to the
//! change — reducing the formula is the point — and it is why the decided
//! verdict is reported alongside, so an arm that decides an instance the other
//! could not is visible rather than averaged in.
//!
//! Output is one JSON object on stdout, so a driver can collect runs without
//! parsing prose.

use std::time::Instant;

use axeyum_cnf::{
    CnfFormula, InprocessOptions, InprocessStats, SearchCounters, StreamingProofOutcome,
    VecProofSink, inprocess_into, parse_dimacs, solve_with_drat_proof_counted,
};

fn arm_options(name: &str) -> InprocessOptions {
    match name {
        "off" => InprocessOptions::OFF,
        "subsume" => InprocessOptions {
            subsume: true,
            ..InprocessOptions::OFF
        },
        "vivify" => InprocessOptions {
            vivify: true,
            ..InprocessOptions::OFF
        },
        "bve" => InprocessOptions {
            bve: true,
            ..InprocessOptions::OFF
        },
        "preprocess" => InprocessOptions::preprocess(),
        "preprocess-full" => InprocessOptions::preprocess_full(),
        other => panic!(
            "unknown arm `{other}`: expected off, subsume, vivify, bve, preprocess or \
             preprocess-full"
        ),
    }
}

fn verdict(outcome: &StreamingProofOutcome) -> &'static str {
    match outcome {
        StreamingProofOutcome::Sat(_) => "sat",
        StreamingProofOutcome::Unsat => "unsat",
        StreamingProofOutcome::ResourceOut => "resource_out",
        StreamingProofOutcome::Interrupted => "interrupted",
        StreamingProofOutcome::SinkFailed(_) => "sink_failed",
    }
}

#[allow(clippy::cast_precision_loss, clippy::too_many_arguments)]
fn emit(
    path: &str,
    arm: &str,
    original: &CnfFormula,
    reduced: &CnfFormula,
    stats: InprocessStats,
    max_conflicts: usize,
    outcome: &StreamingProofOutcome,
    counters: SearchCounters,
    inprocess_seconds: f64,
    search_seconds: f64,
    proof_steps: u64,
) {
    let conflicts = counters.conflicts.max(1) as f64;
    println!(
        "{{\"file\":\"{path}\",\"arm\":\"{arm}\",\"max_conflicts\":{max_conflicts},\
         \"verdict\":\"{}\",\"variables\":{},\"clauses_before\":{},\"clauses_after\":{},\
         \"literals_before\":{},\"literals_after\":{},\"variables_eliminated\":{},\
         \"clauses_subsumed\":{},\"literals_strengthened\":{},\"vivify_strengthened\":{},\
         \"prefix_steps\":{},\"skipped_size\":{},\
         \"inprocess_seconds\":{inprocess_seconds:.6},\"search_seconds\":{search_seconds:.6},\
         \"total_seconds\":{:.6},\"conflicts\":{},\"decisions\":{},\"propagations\":{},\
         \"restarts\":{},\"reductions\":{},\"watch_visits\":{},\"clause_visits\":{},\
         \"resolutions\":{},\"proof_steps\":{proof_steps},\
         \"propagations_per_conflict\":{:.2},\"conflicts_per_second\":{:.2},\
         \"propagations_per_second\":{:.1},\"watch_visits_per_conflict\":{:.2},\
         \"clause_deref_rate\":{:.4}}}",
        verdict(outcome),
        original.variable_count(),
        stats.clauses_before,
        reduced.clauses().len(),
        stats.literals_before,
        stats.literals_after,
        stats.bve.variables_eliminated,
        stats.subsume.clauses_subsumed,
        stats.subsume.literals_strengthened,
        stats.vivify.clauses_strengthened,
        stats.proof_steps,
        stats.skipped_size,
        inprocess_seconds + search_seconds,
        counters.conflicts,
        counters.decisions,
        counters.propagations,
        counters.restarts,
        counters.reductions,
        counters.watch_visits,
        counters.clause_visits,
        counters.resolutions,
        counters.propagations as f64 / conflicts,
        counters.conflicts as f64 / search_seconds.max(1e-9),
        counters.propagations as f64 / search_seconds.max(1e-9),
        counters.watch_visits_per_conflict(),
        counters.clause_deref_rate(),
    );
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().expect(
        "usage: inprocess_profile <file.cnf> [max_conflicts] \
         [off|subsume|vivify|bve|preprocess|preprocess-full]",
    );
    let max_conflicts: usize = args.next().map_or(20_000, |a| {
        a.parse().expect("max_conflicts must be a number")
    });
    let arm = args.next().unwrap_or_else(|| "off".to_owned());
    let options = arm_options(&arm);

    let text = std::fs::read_to_string(&path).expect("read cnf");
    let formula = parse_dimacs(&text).expect("parse dimacs");
    // Parsing is not part of the measurement: the clock starts after it, and the
    // source text is released so it is not resident during the run.
    drop(text);

    // The prefix goes to its own sink so its step count is separable from the
    // search's, and so the search's sink is the same `VecProofSink` the shipping
    // one-shot entry point uses (the boolean-core lane measured that sink's
    // overhead at +0.2%, i.e. inside its own run-to-run spread).
    let mut prefix_sink = VecProofSink::new();
    let inprocess_started = Instant::now();
    let reduced = inprocess_into(&formula, options, None, &mut prefix_sink)
        .expect("VecProofSink never refuses a step");
    let inprocess_seconds = inprocess_started.elapsed().as_secs_f64();
    let prefix_steps = prefix_sink.into_steps().len() as u64;

    let mut sink = VecProofSink::new();
    let search_started = Instant::now();
    let (outcome, counters) =
        solve_with_drat_proof_counted(&reduced.formula, None, max_conflicts, &mut sink);
    let search_seconds = search_started.elapsed().as_secs_f64();
    let search_steps = sink.into_steps().len() as u64;

    emit(
        &path,
        &arm,
        &formula,
        &reduced.formula,
        reduced.stats,
        max_conflicts,
        &outcome,
        counters,
        inprocess_seconds,
        search_seconds,
        prefix_steps + search_steps,
    );
}
