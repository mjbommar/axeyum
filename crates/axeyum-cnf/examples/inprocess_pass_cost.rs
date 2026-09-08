//! Per-pass cost decomposition for the reducing passes, at a **wall-clock**
//! search budget.
//!
//! ```sh
//! cargo run --release -p axeyum-cnf --example inprocess_pass_cost -- \
//!     <file.cnf> <search_budget_ms> [off|subsume|vivify|bve|preprocess|preprocess-full]
//! ```
//!
//! # Why this exists next to `inprocess_profile`
//!
//! `inprocess_profile` answers "does inprocessing move propagations per
//! conflict?" at a **fixed conflict budget**, which is the right control for a
//! per-conflict metric and the wrong one for a cost question: a competition
//! budget is seconds, and a pass that pays for itself in conflicts can still
//! lose every file inside 24 s. That example is also the reproduction recipe for
//! a published measurement, so it is left alone rather than grown a second mode.
//!
//! Three things this adds:
//!
//! * **A wall-clock search budget**, so "solved / not solved at B seconds" is a
//!   direct observation rather than an extrapolation from a conflict rate.
//! * **Setup versus work.** Each pass is run TWICE — the second time on its own
//!   output. The second run rebuilds the same occurrence lists over a formula it
//!   has already reduced, so its time is very nearly pure setup, and
//!   `first - second` is the work. This matters because the two have different
//!   fixes: setup cost is amortisable across a schedule that reduces repeatedly,
//!   work cost is not. The second run's own reduction counters are reported too,
//!   so a reader can see whether it was actually idle rather than assume it.
//! * **Literal occurrences, not just clauses.** BVE removes clauses while adding
//!   literal occurrences; a shrink reported in clauses alone can be a growth in
//!   the quantity propagation walks.
//!
//! # What is NOT controlled here
//!
//! The arms search different formulas, so they do not analyse the same
//! conflicts. That is inherent — reducing the formula is the point — and it is
//! why the verdict and the wall time are reported per arm rather than a ratio.
//!
//! One JSON object per run on stdout.

use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfFormula, CnfLit, DratSink, InprocessOptions, ProofSinkError, SearchCounters,
    StreamingProofOutcome, inprocess_into, parse_dimacs, solve_with_drat_proof_counted,
};

/// A sink that counts steps and keeps none of them.
///
/// `VecProofSink` is not usable here: a BVE prefix on a public-corpus instance
/// reached 37.7 M steps in the previous measurement, which is the shape that
/// OOM-killed a run at 27.6 GiB. The step COUNT is what this measurement needs,
/// and counting does not require retaining. Anything that wants the steps
/// themselves must stream them (ADR-0381).
#[derive(Default)]
struct CountingSink {
    steps: u64,
}

impl DratSink for CountingSink {
    fn add_clause(&mut self, _lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        self.steps += 1;
        Ok(())
    }
    fn delete_clause(&mut self, _lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        self.steps += 1;
        Ok(())
    }
}

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

fn literals(formula: &CnfFormula) -> usize {
    formula.clauses().iter().map(|c| c.lits().len()).sum()
}

/// Live variables: the count a compaction would report, not the declared width.
/// BVE never renumbers, so the reduced formula still declares the original
/// `variable_count` and a "variables after" read off that field is always the
/// number it started with.
fn live_variables(formula: &CnfFormula) -> usize {
    let mut seen = vec![false; formula.variable_count()];
    for clause in formula.clauses() {
        for lit in clause.lits() {
            seen[lit.var().index()] = true;
        }
    }
    seen.iter().filter(|s| **s).count()
}

#[allow(clippy::too_many_lines)]
fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().expect(
        "usage: inprocess_pass_cost <file.cnf> <search_budget_ms> \
         [off|subsume|vivify|bve|preprocess|preprocess-full]",
    );
    let budget_ms: u64 = args
        .next()
        .map_or(24_000, |a| a.parse().expect("budget must be a number"));
    let arm = args.next().unwrap_or_else(|| "off".to_owned());
    let options = arm_options(&arm);

    let text = std::fs::read_to_string(&path).expect("read cnf");
    let formula = parse_dimacs(&text).expect("parse dimacs");
    // Parsing is not part of the measurement: the clock starts after it, and the
    // source text is released so it is not resident during the run.
    drop(text);

    // PASS, RUN 1 — on the caller's formula. No deadline: this run is measuring
    // what the pass COSTS, and a truncated pass measures the clock instead.
    let mut sink = CountingSink::default();
    let started = Instant::now();
    let reduced = inprocess_into(&formula, options, None, &mut sink)
        .expect("CountingSink never refuses a step");
    let pass_seconds = started.elapsed().as_secs_f64();
    let prefix_steps = sink.steps;

    // PASS, RUN 2 — the same pass on its own output. It rebuilds the same
    // occurrence lists and finds (nearly) nothing, so this is the setup floor.
    let mut resink = CountingSink::default();
    let restarted = Instant::now();
    let re = inprocess_into(&reduced.formula, options, None, &mut resink)
        .expect("CountingSink never refuses a step");
    let setup_seconds = restarted.elapsed().as_secs_f64();

    // SEARCH — wall-clock budget, conflict cap effectively off so the clock is
    // the only stop. The budget is the WHOLE budget: this example reports the
    // pass cost separately rather than deducting it, so a caller can price any
    // schedule from the same row.
    let deadline = Instant::now().checked_add(Duration::from_millis(budget_ms));
    let mut search_sink = CountingSink::default();
    let search_started = Instant::now();
    let (outcome, counters): (StreamingProofOutcome, SearchCounters) =
        solve_with_drat_proof_counted(&reduced.formula, deadline, usize::MAX, &mut search_sink);
    let search_seconds = search_started.elapsed().as_secs_f64();

    let conflicts = counters.conflicts.max(1) as f64;
    println!(
        "{{\"file\":\"{path}\",\"arm\":\"{arm}\",\"budget_ms\":{budget_ms},\
         \"verdict\":\"{}\",\
         \"variables_declared\":{},\"variables_live_before\":{},\"variables_live_after\":{},\
         \"clauses_before\":{},\"clauses_after\":{},\
         \"literals_before\":{},\"literals_after\":{},\
         \"variables_eliminated\":{},\"clauses_subsumed\":{},\"literals_strengthened\":{},\
         \"vivify_strengthened\":{},\"vivify_literals_removed\":{},\
         \"skipped_size\":{},\"prefix_steps\":{prefix_steps},\
         \"pass_seconds\":{pass_seconds:.6},\"setup_seconds\":{setup_seconds:.6},\
         \"rerun_clauses_subsumed\":{},\"rerun_variables_eliminated\":{},\
         \"rerun_vivify_strengthened\":{},\
         \"search_seconds\":{search_seconds:.6},\"total_seconds\":{:.6},\
         \"conflicts\":{},\"propagations\":{},\"decisions\":{},\"restarts\":{},\
         \"search_steps\":{},\
         \"propagations_per_conflict\":{:.2},\"conflicts_per_second\":{:.2}}}",
        verdict(&outcome),
        formula.variable_count(),
        live_variables(&formula),
        live_variables(&reduced.formula),
        reduced.stats.clauses_before,
        reduced.stats.clauses_after,
        literals(&formula),
        literals(&reduced.formula),
        reduced.stats.bve.variables_eliminated,
        reduced.stats.subsume.clauses_subsumed,
        reduced.stats.subsume.literals_strengthened,
        reduced.stats.vivify.clauses_strengthened,
        reduced.stats.vivify.literals_removed,
        reduced.stats.skipped_size,
        re.stats.subsume.clauses_subsumed,
        re.stats.bve.variables_eliminated,
        re.stats.vivify.clauses_strengthened,
        pass_seconds + search_seconds,
        counters.conflicts,
        counters.propagations,
        counters.decisions,
        counters.restarts,
        search_sink.steps,
        counters.propagations as f64 / conflicts,
        counters.conflicts as f64 / search_seconds.max(1e-9),
    );
}
