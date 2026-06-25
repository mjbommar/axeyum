//! The measurement harness: run each construction-known [`Case`] through the
//! [`axeyum_property`] SDK, record the verdict + timing + certificate facts, and
//! aggregate with a hard `DISAGREE = 0` soundness floor.

use std::time::{Duration, Instant};

use crate::corpus::{Case, Status};

/// The decided outcome of one property check, collapsed from
/// [`axeyum_property::Outcome`] for tabulation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The property was proved for all inputs satisfying the precondition.
    Proved,
    /// A concrete counterexample (satisfying the precondition) was found.
    Counterexample,
    /// The query was not decided within the configured budgets.
    Unknown,
}

impl Verdict {
    /// A short, stable label for the scoreboard.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Verdict::Proved => "proved",
            Verdict::Counterexample => "counterexample",
            Verdict::Unknown => "unknown",
        }
    }

    /// Whether this verdict **contradicts** the construction-known `status`.
    ///
    /// `Unknown` never contradicts (it is an honest non-result). A `Proved` for a
    /// `ShouldFindCounterexample` — or a `Counterexample` for a `ShouldProve` — is
    /// a hard soundness failure.
    #[must_use]
    pub fn contradicts(self, status: Status) -> bool {
        matches!(
            (self, status),
            (Verdict::Proved, Status::ShouldFindCounterexample)
                | (Verdict::Counterexample, Status::ShouldProve)
        )
    }

    /// Whether this verdict **matches** the construction-known `status` (the
    /// intended decided outcome). `Unknown` neither matches nor contradicts.
    #[must_use]
    pub fn matches(self, status: Status) -> bool {
        matches!(
            (self, status),
            (Verdict::Proved, Status::ShouldProve)
                | (Verdict::Counterexample, Status::ShouldFindCounterexample)
        )
    }
}

/// One measured row: the case, axeyum's verdict, timing, and certificate facts.
#[derive(Debug, Clone)]
pub struct CaseResult {
    /// Stable case name (corpus order is deterministic).
    pub name: String,
    /// One-line human description of the property.
    pub description: String,
    /// The construction-known true status.
    pub status: Status,
    /// axeyum's decided verdict.
    pub verdict: Verdict,
    /// Wall-clock solve time for this case.
    pub elapsed: Duration,
    /// For a `Proved` result: did [`axeyum_property::Certificate::verify`] re-check?
    /// `None` for non-`Proved` results.
    pub cert_verified: Option<bool>,
    /// For a `Proved` result: did `to_lean_module` yield a standalone Lean module?
    /// `None` for non-`Proved` results.
    pub lean_module: Option<bool>,
}

impl CaseResult {
    /// Whether this row is a hard soundness contradiction.
    #[must_use]
    pub fn is_disagreement(&self) -> bool {
        self.verdict.contradicts(self.status)
    }

    /// Whether this `Proved` row carries a *verified* Lean module — the
    /// differentiator. `false` for non-`Proved` rows.
    #[must_use]
    pub fn lean_certified(&self) -> bool {
        self.cert_verified == Some(true) && self.lean_module == Some(true)
    }
}

/// Aggregate counters over a corpus run.
#[derive(Debug, Clone, Default)]
pub struct Aggregate {
    /// Total cases run.
    pub total: usize,
    /// Cases axeyum proved.
    pub proved: usize,
    /// Cases axeyum found a counterexample for.
    pub counterexample: usize,
    /// Cases axeyum left undecided.
    pub unknown: usize,
    /// Hard soundness contradictions (must be 0).
    pub disagree: usize,
    /// `Proved` cases whose certificate re-verified.
    pub cert_verified: usize,
    /// `Proved` cases carrying a *verified* standalone Lean module.
    pub lean_certified: usize,
    /// Sum of solve times, for the mean.
    total_time: Duration,
}

impl Aggregate {
    /// Fraction of cases axeyum proved.
    #[must_use]
    pub fn proved_rate(&self) -> f64 {
        ratio(self.proved, self.total)
    }

    /// Fraction of cases axeyum found a counterexample for.
    #[must_use]
    pub fn counterexample_rate(&self) -> f64 {
        ratio(self.counterexample, self.total)
    }

    /// Fraction of cases axeyum left undecided.
    #[must_use]
    pub fn unknown_rate(&self) -> f64 {
        ratio(self.unknown, self.total)
    }

    /// Fraction of `Proved` cases carrying a *verified* Lean module — the
    /// headline differentiator. Denominator is `proved` (0 if nothing proved).
    #[must_use]
    pub fn lean_cert_coverage(&self) -> f64 {
        ratio(self.lean_certified, self.proved)
    }

    /// Mean solve time across all cases.
    #[must_use]
    pub fn mean_time(&self) -> Duration {
        if self.total == 0 {
            Duration::ZERO
        } else {
            self.total_time / u32::try_from(self.total).unwrap_or(u32::MAX)
        }
    }
}

fn ratio(num: usize, den: usize) -> f64 {
    if den == 0 {
        0.0
    } else {
        // Counts are tiny (corpus is ~12-20), so `u32` is ample and the
        // `u32 -> f64` cast is exact.
        let num = u32::try_from(num).unwrap_or(u32::MAX);
        let den = u32::try_from(den).unwrap_or(u32::MAX);
        f64::from(num) / f64::from(den)
    }
}

/// Run the whole corpus, returning the per-case rows (in deterministic corpus
/// order) and the aggregate.
///
/// # Panics
///
/// Each [`Case`] closure routes through [`axeyum_property`], which only returns a
/// [`axeyum_property::SolverError`] on an internal self-check failure (a soundness
/// alarm). The harness treats such an error as a hard failure and panics, rather
/// than silently downgrading it to `Unknown` — a self-check failure must never be
/// swept under the rug.
#[must_use]
pub fn run_corpus(cases: &[Case]) -> (Vec<CaseResult>, Aggregate) {
    let mut rows = Vec::with_capacity(cases.len());
    let mut agg = Aggregate::default();

    for case in cases {
        let start = Instant::now();
        let outcome = (case.run)();
        let elapsed = start.elapsed();

        let row = CaseResult {
            name: case.name.to_string(),
            description: case.description.to_string(),
            status: case.status,
            verdict: outcome.verdict,
            elapsed,
            cert_verified: outcome.cert_verified,
            lean_module: outcome.lean_module,
        };

        agg.total += 1;
        agg.total_time += elapsed;
        match row.verdict {
            Verdict::Proved => agg.proved += 1,
            Verdict::Counterexample => agg.counterexample += 1,
            Verdict::Unknown => agg.unknown += 1,
        }
        if row.is_disagreement() {
            agg.disagree += 1;
        }
        if row.cert_verified == Some(true) {
            agg.cert_verified += 1;
        }
        if row.lean_certified() {
            agg.lean_certified += 1;
        }
        rows.push(row);
    }

    (rows, agg)
}

/// The raw result of running one property closure: the collapsed verdict plus the
/// certificate facts (only meaningful for `Proved`).
#[derive(Debug, Clone, Copy)]
pub struct RunOutcome {
    /// The collapsed verdict.
    pub verdict: Verdict,
    /// `Some(verified)` for a `Proved` result, else `None`.
    pub cert_verified: Option<bool>,
    /// `Some(present)` for a `Proved` result, else `None`.
    pub lean_module: Option<bool>,
}
