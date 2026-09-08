//! Decompose the native CDCL core's per-conflict cost on a real DIMACS file,
//! and measure what emitting a DRAT certificate costs the search.
//!
//! This is the measurement tool behind
//! `docs/research/12-performance/bench-boolean-core-2026-09-07.md`. It exists
//! because the 2026-09-05 native-core-vs-Kissat search-statistics note
//! (`docs/research/11-design-review/2026-09-05-native-core-vs-kissat-search-stats.md`)
//! could report the native core's conflicts and wall time but had no
//! propagation, decision or restart counter to set against `kissat -s`'s, and
//! therefore could not say where a conflict's time goes.
//!
//! ```sh
//! cargo run --release -p axeyum-cnf --example boolean_core_profile -- \
//!     <file.cnf> [max_conflicts] [null|vec|text|binary]
//! ```
//!
//! `max_conflicts` (default 20000) makes the run **fixed-work**: two builds
//! given the same file and the same budget analyse the same conflicts along the
//! same trajectory, so the wall-time ratio between them is pure per-conflict
//! throughput rather than a difference in how much search each did. That is the
//! only honest way to A/B a change that is meant to be trajectory-preserving.
//!
//! The sink argument selects where the DRAT proof goes, and is how the
//! certificate's cost is measured against a control:
//!
//! - `null` — accept every step and keep nothing. The core still *calls* the
//!   sink at every learned clause and every `reduce_db` deletion (those calls
//!   are structural), so the difference between this arm and the others is
//!   exactly the cost of **recording** the proof, with the cost of deciding to
//!   emit held constant.
//! - `vec` — the in-RAM `VecProofSink` the shipping one-shot entry point
//!   (`solve_with_drat_proof`) uses.
//! - `text` — the standard DRAT text a `TextProofSink` writes, to a sink that
//!   counts bytes and discards them (so disk speed is not in the measurement).
//! - `binary` — the binary DRAT format, same discard-and-count writer.
//!
//! Output is one JSON object on stdout, so a driver can collect runs without
//! parsing prose.

use std::hint::black_box;
use std::io::{self, Write};
use std::time::Instant;

use axeyum_cnf::{
    BinaryProofSink, CnfFormula, CnfLit, DratSink, DratStep, ProofSinkError, SearchCounters,
    StreamingProofOutcome, TextProofSink, VecProofSink, parse_dimacs,
    solve_with_drat_proof_counted,
};

/// A [`Write`] that counts bytes and discards them. Used so the `text` and
/// `binary` arms measure *formatting* cost and not the disk underneath.
#[derive(Default)]
struct CountingSinkWriter {
    bytes: u64,
}

impl Write for CountingSinkWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.bytes += buf.len() as u64;
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// The no-proof control arm: accepts every step, keeps nothing, counts what it
/// was handed.
#[derive(Default)]
struct CountingNullSink {
    steps: u64,
    literals: u64,
}

impl DratSink for CountingNullSink {
    fn add_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        self.steps += 1;
        self.literals += lits.len() as u64;
        Ok(())
    }

    fn delete_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        self.steps += 1;
        self.literals += lits.len() as u64;
        Ok(())
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
    formula: &CnfFormula,
    sink_name: &str,
    max_conflicts: usize,
    outcome: &StreamingProofOutcome,
    counters: &SearchCounters,
    seconds: f64,
    sink_steps: u64,
    sink_bytes: u64,
) {
    let conflicts = counters.conflicts.max(1) as f64;
    println!(
        "{{\"file\":\"{path}\",\"variables\":{},\"clauses\":{},\"sink\":\"{sink_name}\",\
         \"max_conflicts\":{max_conflicts},\"verdict\":\"{}\",\"seconds\":{seconds:.6},\
         \"conflicts\":{},\"decisions\":{},\"propagations\":{},\"restarts\":{},\
         \"reductions\":{},\"watch_visits\":{},\"clause_visits\":{},\
         \"watch_relocations\":{},\"resolutions\":{},\"analyze_mark_bytes\":{},\
         \"redundancy_steps\":{},\"sink_steps\":{sink_steps},\"sink_bytes\":{sink_bytes},\
         \"conflicts_per_second\":{:.2},\"watch_visits_per_conflict\":{:.2},\
         \"clause_deref_rate\":{:.4},\"propagations_per_conflict\":{:.2},\
         \"resolutions_per_conflict\":{:.2},\"mark_bytes_per_conflict\":{:.1}}}",
        formula.variable_count(),
        formula.clauses().len(),
        verdict(outcome),
        counters.conflicts,
        counters.decisions,
        counters.propagations,
        counters.restarts,
        counters.reductions,
        counters.watch_visits,
        counters.clause_visits,
        counters.watch_relocations,
        counters.resolutions,
        counters.analyze_mark_bytes,
        counters.redundancy_steps,
        counters.conflicts as f64 / seconds.max(1e-9),
        counters.watch_visits_per_conflict(),
        counters.clause_deref_rate(),
        counters.propagations as f64 / conflicts,
        counters.resolutions as f64 / conflicts,
        counters.analyze_mark_bytes as f64 / conflicts,
    );
}

fn step_literals(step: &DratStep) -> usize {
    match step {
        DratStep::Add(lits) | DratStep::Delete(lits) => lits.len(),
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: boolean_core_profile <file.cnf> [max_conflicts] [null|vec|text|binary]");
    let max_conflicts: usize = args.next().map_or(20_000, |a| {
        a.parse().expect("max_conflicts must be a number")
    });
    let sink_name = args.next().unwrap_or_else(|| "vec".to_string());

    let text = std::fs::read_to_string(&path).expect("read cnf");
    let formula = parse_dimacs(&text).expect("parse dimacs");
    // Parsing is not part of the measurement: the clock starts after it, and the
    // source text is released so it is not resident during the search.
    drop(text);

    match sink_name.as_str() {
        "null" => {
            let mut sink = CountingNullSink::default();
            let started = Instant::now();
            let (outcome, counters) =
                solve_with_drat_proof_counted(&formula, None, max_conflicts, &mut sink);
            let seconds = started.elapsed().as_secs_f64();
            emit(
                &path,
                &formula,
                "null",
                max_conflicts,
                &outcome,
                &counters,
                seconds,
                sink.steps,
                sink.literals,
            );
        }
        "vec" => {
            let mut sink = VecProofSink::new();
            let started = Instant::now();
            let (outcome, counters) =
                solve_with_drat_proof_counted(&formula, None, max_conflicts, &mut sink);
            let seconds = started.elapsed().as_secs_f64();
            let steps = sink.into_steps();
            let count = steps.len() as u64;
            let lits: u64 = steps.iter().map(|s| step_literals(s) as u64).sum();
            black_box(&steps);
            emit(
                &path,
                &formula,
                "vec",
                max_conflicts,
                &outcome,
                &counters,
                seconds,
                count,
                lits,
            );
        }
        "text" => {
            let mut sink = TextProofSink::new(CountingSinkWriter::default());
            let started = Instant::now();
            let (outcome, counters) =
                solve_with_drat_proof_counted(&formula, None, max_conflicts, &mut sink);
            let seconds = started.elapsed().as_secs_f64();
            let writer = sink.finish().expect("counting writer never fails");
            emit(
                &path,
                &formula,
                "text",
                max_conflicts,
                &outcome,
                &counters,
                seconds,
                0,
                writer.bytes,
            );
        }
        "binary" => {
            let mut sink = BinaryProofSink::new(CountingSinkWriter::default());
            let started = Instant::now();
            let (outcome, counters) =
                solve_with_drat_proof_counted(&formula, None, max_conflicts, &mut sink);
            let seconds = started.elapsed().as_secs_f64();
            let writer = sink.finish().expect("counting writer never fails");
            emit(
                &path,
                &formula,
                "binary",
                max_conflicts,
                &outcome,
                &counters,
                seconds,
                0,
                writer.bytes,
            );
        }
        other => panic!("unknown sink `{other}`: expected null, vec, text or binary"),
    }
}
