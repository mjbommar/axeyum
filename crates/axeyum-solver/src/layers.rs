//! Typed view of the pure-Rust bit-blasting pipeline stages.
//!
//! The backend records per-stage counters in the untyped
//! [`SolveStats::backend`] list so [`SolveStats`] can stay backend-agnostic.
//! [`BvLayerStats`] lifts those counters into a named, typed structure so the
//! lowering/optimization pipeline is a first-class thing callers can measure,
//! compare, and regression-test rather than a bag of strings.

use std::time::Duration;

use crate::backend::SolveStats;

/// The named stages of the `sat-bv` pipeline for one check.
///
/// Durations cover bit-blasting (term → AIG), CNF encoding (AIG → CNF),
/// SAT solving, and model lifting (assignment → Axeyum model). Sizes describe
/// the AIG and CNF the encoder produced.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BvLayerStats {
    /// Time lowering terms to the AIG.
    pub bit_blast: Duration,
    /// Time encoding the AIG to CNF.
    pub cnf_encode: Duration,
    /// Time inside the SAT adapter.
    pub solve: Duration,
    /// Time lifting a satisfying assignment into an Axeyum model.
    pub model_lift: Duration,
    /// Symbolic AIG inputs (bit-level free variables).
    pub aig_inputs: u64,
    /// AIG nodes after lowering.
    pub aig_nodes: u64,
    /// CNF variables submitted to the SAT adapter.
    pub cnf_variables: u64,
    /// CNF clauses submitted to the SAT adapter.
    pub cnf_clauses: u64,
}

impl BvLayerStats {
    /// Extracts the pure-Rust pipeline stages from `stats`.
    ///
    /// Returns `None` when `stats` was not produced by the `sat-bv` backend
    /// (its identifying counters, `aig_nodes` and `cnf_variables`, are absent),
    /// so this never silently fabricates numbers for another backend.
    pub fn from_solve_stats(stats: &SolveStats) -> Option<Self> {
        let aig_nodes = lookup(stats, "aig_nodes")?;
        let cnf_variables = lookup(stats, "cnf_variables")?;
        Some(Self {
            bit_blast: lookup(stats, "bit_blast_ms").map_or(Duration::ZERO, ms_to_duration),
            cnf_encode: lookup(stats, "cnf_encode_ms").map_or(Duration::ZERO, ms_to_duration),
            solve: stats.solve,
            model_lift: stats.model_lift,
            aig_inputs: lookup(stats, "aig_inputs").map_or(0, count_to_u64),
            aig_nodes: count_to_u64(aig_nodes),
            cnf_variables: count_to_u64(cnf_variables),
            cnf_clauses: lookup(stats, "cnf_clauses").map_or(0, count_to_u64),
        })
    }

    /// Total wall-clock time across all pipeline stages.
    pub fn total(&self) -> Duration {
        self.bit_blast + self.cnf_encode + self.solve + self.model_lift
    }

    /// Clauses per CNF variable, a coarse encoding-density indicator
    /// (`0.0` when there are no variables).
    pub fn clause_density(&self) -> f64 {
        if self.cnf_variables == 0 {
            0.0
        } else {
            u64_to_f64(self.cnf_clauses) / u64_to_f64(self.cnf_variables)
        }
    }
}

fn lookup(stats: &SolveStats, key: &str) -> Option<f64> {
    stats
        .backend
        .iter()
        .find(|(name, _)| name == key)
        .map(|(_, value)| *value)
}

fn ms_to_duration(milliseconds: f64) -> Duration {
    Duration::from_secs_f64((milliseconds / 1000.0).max(0.0))
}

// Backend counters are small non-negative integers stored as f64; the round
// recovers the original count exactly within the f64 integer-exact range.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn count_to_u64(value: f64) -> u64 {
    value.round().max(0.0) as u64
}

#[allow(clippy::cast_precision_loss)]
fn u64_to_f64(value: u64) -> f64 {
    value as f64
}
