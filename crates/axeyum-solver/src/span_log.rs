//! The span log: one solve rendered as a flat, append-only event log.
//!
//! # Why this is not a call tree
//!
//! A solve is three shapes at once, and a flame graph alone draws two of them
//! wrong:
//!
//! 1. **A ladder of alternatives.** Route A declines, B declines, C decides.
//!    Those attempts are *sequential*, not nested — a flame graph that puts the
//!    declined routes under the winner has the causality backwards, because the
//!    decliners ran BEFORE the winner and are the reason it was reached.
//! 2. **Real nesting inside one route**: theory check contains simplex contains
//!    pivots. Here a flame graph is right.
//! 3. **Refinement loops.** One `QF_NRA` file measured 2026-09-08 ran 513 CEGAR
//!    rounds. Nobody can read 513 boxes, and whether it was 4 huge rounds or
//!    40,000 tiny ones has opposite fixes.
//!
//! So the emitted form is a flat list of spans, each naming its parent and the
//! **kind of edge** that joins them ([`EdgeType`]). Every view — a ladder
//! timeline, an icicle of the deciding route, a division-level Sankey — is
//! derived downstream from the same rows. Nothing here decides how the data is
//! drawn.
//!
//! # Four properties this format is built to preserve
//!
//! Each of these is a defect this repository has already shipped, not a
//! hypothetical.
//!
//! * **A span is recorded on OPEN, not only on close.** Every blind file we had
//!   was blind because an instrument published on return and the route never
//!   returned. A span with `closed_at_ns: null` is the answer to "who held the
//!   budget when we died" — see [`SpanLog::open_segment_span`], which is the
//!   only span that can carry [`Outcome::Killed`].
//! * **Deterministic work travels beside wall time.** Wall time is not
//!   comparable between runs on a shared box; a counter that does not read a
//!   clock is. Every span carries an optional `(work_unit, work)` pair, and a
//!   span with no deterministic counter says `null` rather than `0`.
//! * **`declined`, `exhausted` and `killed` are different outcomes.** A route
//!   that does not handle the fragment and a route that ran out of nodes report
//!   the same `unknown` to a caller and demand opposite fixes. A
//!   [`crate::route_trace::DeclineReason::Budget`] becomes
//!   [`Outcome::Exhausted`] and carries the **bound that bit** in `bound`.
//! * **A loop is one span per LOOP, with a count and a distribution.**
//!   [`SpanKind::RefinementLoop`] carries `loop_count` and `loop_hist`, the
//!   per-round wall clock in log2 millisecond buckets. A loop whose rounds were
//!   never timed still carries `loop_hist: null` beside
//!   `loop_hist_available: false`, and a renderer must say "distribution not
//!   recorded" rather than draw a flat bar. There is one span per lazy-SMT loop
//!   *entered* (`lazy-smt:lra`, `lazy-smt:nra`, `lazy-smt:nia`), because two
//!   deciders behind one count is how a 2026-09-08 `QF_NIA` sweep came to read
//!   the real-relaxation refuter's rounds as the nonlinear-integer route's.
//!
//! # What the timestamps are, and are not
//!
//! [`crate::RouteTrace`] stores a *duration per attempt*, not an absolute
//! instant. Route-span offsets are therefore a **prefix sum** over those
//! durations (`time_basis: "prefix-sum"`), which is exact for the ladder
//! because the attempts are strictly sequential. Stage spans derived from an
//! instrument snapshot have a duration and no position at all, so they are
//! emitted at their parent's offset with `time_basis: "duration-only"`, and a
//! renderer must not read their left edge as an observed time.
//!
//! # Known gaps, stated in the data
//!
//! * **The three loop stage children are query-wide.** `skeleton_solve`,
//!   `theory_check` and `core_extraction` are totals across every lazy-SMT
//!   loop, so they are emitted ONCE, under the first loop span, and a reader
//!   must not attribute them to that loop alone. The per-loop quantity that IS
//!   attributed is `loop_hist` and the span's own `wall_ns`, both derived from
//!   that loop's histogram.
//! * **A round in flight is not in the histogram.** It is filed when the next
//!   round opens or the guard drops, so a watchdog kill leaves the round that
//!   spent the budget in `pending_round_ms` on the span's `detail` rather than
//!   in a bucket.
//! * **No ticks.** `axeyum_cnf::ticks` derives a machine-independent tick count
//!   from `axeyum_cnf::SearchCounters`, but those counters are only filled by
//!   the `count_search` search variants, which the shipping path does not use.
//!   The deterministic counters that ARE reachable (decisions, propagations,
//!   conflicts, simplex pivots, refinement rounds, CNF clauses) are emitted
//!   instead, each naming its own unit.
//! * **Instruments are per-query, not per-route-attempt.** A `BvLayerStats`
//!   snapshot says what the `sat-bv` stages cost on this query; it does not say
//!   which of the twelve routes in the trail ran them. Stage spans therefore
//!   carry `parent_basis`, which is `"route-label-match"`, `"sole-route"` or
//!   `"unattributed"` — never a guess presented as attribution.

use core::fmt::Write as _;
use std::time::Duration;

use crate::layers::{BvLayerStats, TheoryLayerStats};
use crate::lazy_smt_counters::{LazySmtCounters, LazySmtLoop};
use crate::lia_counters::LiaCounters;
use crate::live_instruments::Sampled;
use crate::route_trace::{DeclineReason, RouteOutcome, RouteTrace, Verdict};

/// The span-log schema version. Bump on any change a consumer could misread;
/// additive fields do not require one, removed or re-meaning fields do.
pub const SPAN_LOG_SCHEMA_VERSION: u32 = 1;

/// How a run ended, as distinct from what it answered.
///
/// A `unknown` verdict says nothing about whether the solver returned it or a
/// watchdog invented it, and those two runs need opposite readings: the first
/// has a complete trail, the second has an open span holding the budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Termination {
    /// The solve returned on its own, in budget or with its own `unknown`.
    #[default]
    Returned,
    /// A wall-clock watchdog gave up on a worker that had not returned.
    WatchdogKill,
    /// The worker thread could not be spawned; nothing ran.
    WorkerSpawnFailed,
}

impl Termination {
    /// The token emitted in the run header.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Termination::Returned => "returned",
            Termination::WatchdogKill => "watchdog-kill",
            Termination::WorkerSpawnFailed => "worker-spawn-failed",
        }
    }
}

/// The kind of edge joining a span to its parent — the field that keeps a
/// ladder from being drawn as a tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeType {
    /// Genuine containment: the parent was running while this span ran.
    Nested,
    /// This span ran because the previous sibling declined. Sequential, not
    /// contained — the alternative the ladder moved on to.
    FellThrough,
    /// One collapsed abstraction/refinement loop under its route.
    RefinementRound,
}

impl EdgeType {
    /// The token emitted for this edge.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            EdgeType::Nested => "nested",
            EdgeType::FellThrough => "fell_through",
            EdgeType::RefinementRound => "refinement_round",
        }
    }
}

/// What became of a span.
///
/// [`Outcome::Declined`] and [`Outcome::Exhausted`] are deliberately separate:
/// the first is "this route does not do this", the second is "this route ran
/// out of a named budget". Both surface as `unknown` to a caller and they have
/// opposite fixes, and a printed reason has twice been the wrong one of the two
/// — a capacity limit reporting itself as a modelling gap.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// The classification preamble, not a route.
    Probe,
    /// The span produced the verdict.
    Decided,
    /// The span declined for a non-budget reason and the ladder moved on.
    Declined,
    /// A named budget ran out. `bound` carries which one.
    Exhausted,
    /// The span was still open when the run was killed. Only the open segment
    /// can carry this.
    Killed,
    /// A stage that ran; it has a cost but no verdict of its own.
    Ran,
}

impl Outcome {
    /// The token emitted for this outcome.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Outcome::Probe => "probe",
            Outcome::Decided => "decided",
            Outcome::Declined => "declined",
            Outcome::Exhausted => "exhausted",
            Outcome::Killed => "killed",
            Outcome::Ran => "ran",
        }
    }
}

/// What a span is, so a renderer can pick a view without parsing route names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanKind {
    /// The whole run. Exactly one per log, id 0, no parent.
    Run,
    /// One recorded dispatch attempt from the route ladder.
    RouteAttempt,
    /// A measured stage inside a route (bit-blasting, simplex, parsing).
    Stage,
    /// A collapsed refinement loop: one span standing for N rounds.
    RefinementLoop,
    /// The segment after the last recorded attempt, still open when the run
    /// died. This is the span that answers "who held the budget".
    OpenSegment,
}

impl SpanKind {
    /// The token emitted for this kind.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            SpanKind::Run => "run",
            SpanKind::RouteAttempt => "route_attempt",
            SpanKind::Stage => "stage",
            SpanKind::RefinementLoop => "refinement_loop",
            SpanKind::OpenSegment => "open_segment",
        }
    }
}

/// One instrument reading with the provenance that has to travel with it.
///
/// The completed path reads a thread-local snapshot and the watchdog path
/// samples the shared board; both produce a value and a [`Sampled`], and a
/// consumer must not have to know which path it came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reading<T> {
    /// The reading.
    pub value: T,
    /// Whether the stage had returned when it was taken. An `InFlight` reading
    /// makes every counter on the span a lower bound, and the span is emitted
    /// with `complete: false`.
    pub sampled: Sampled,
}

impl<T> Reading<T> {
    /// A reading taken when the stage returned.
    pub const fn complete(value: T) -> Self {
        Self {
            value,
            sampled: Sampled::Complete,
        }
    }
}

/// Everything one solve can contribute to a span log.
///
/// Every instrument is optional and absence is meaningful: a `None` is "this
/// instrument never published", which is not the same as a reading of zero and
/// must never be rendered as one.
#[derive(Debug, Default)]
pub struct SpanLogInputs<'a> {
    /// The benchmark path as given on the command line.
    pub file: &'a str,
    /// The SMT-LIB division, when it can be read off the path. `None` rather
    /// than a guess.
    pub division: Option<&'a str>,
    /// The verdict printed on stdout: `sat`, `unsat` or `unknown`.
    pub verdict: &'a str,
    /// Total wall clock for the process's solve, in nanoseconds.
    pub wall_ns: u64,
    /// The configured wall budget, when one was set.
    pub budget_ns: Option<u64>,
    /// Peak resident set for the process, in bytes
    /// (`axeyum_solver::peak_resident_bytes`), or `None` where the target has no
    /// mechanism.
    ///
    /// The third axis, beside wall time and deterministic work, and the one
    /// that was missing when it was needed most: on 2026-09-08 three `QF_LRA`
    /// files reached **26.6 GB under `--memory-limit-mb 8192`** and the only
    /// record of it was `dmesg`. A run's memory cost belongs in the run's own
    /// artifact.
    ///
    /// It is the kernel's `VmHWM`, so it is a true peak and not a sample — it
    /// cannot miss a spike between two watchdog samples — and it is monotone
    /// per process, so it is this query's peak only on a one-query-per-process
    /// harness. `None` is "not observable here", never zero.
    pub peak_rss_bytes: Option<u64>,
    /// How the run ended.
    pub termination: Termination,
    /// Host the run happened on, for a reader comparing two sweeps.
    pub host: Option<&'a str>,
    /// The solver commit the binary was built from.
    pub solver_commit: Option<&'a str>,
    /// The `; config …` line, verbatim, so a stage timing can be read against
    /// the admission policy that produced it.
    pub config_line: Option<Reading<String>>,
    /// The dispatch trail.
    pub route: Option<Reading<RouteTrace>>,
    /// Time since the last recorded attempt, measured when the run was killed.
    /// Present only on a killed run; this is the open span's duration.
    pub open_segment_ns: Option<u64>,
    /// Cumulative front-door parse time.
    pub front_door_parse: Option<Reading<Duration>>,
    /// Cumulative `dl_online` time and call count.
    pub dl_online: Option<Reading<(Duration, u64)>>,
    /// `sat-bv` stage timings.
    pub bv: Option<Reading<BvLayerStats>>,
    /// The `sat-bv` stage the check was inside when it was sampled, and the
    /// stages it had not reached. Only a killed check has these.
    pub bv_stage: Option<(&'static str, Vec<&'static str>)>,
    /// CDCL(T) stage timings.
    pub theory: Option<Reading<TheoryLayerStats>>,
    /// Abstraction/refinement loop counters.
    pub lazy: Option<Reading<LazySmtCounters>>,
    /// Integer-route counters.
    ///
    /// These produce NO stage span, and that absence is a measurement rather
    /// than an omission: `LiaCounters` carries counts and not one duration, so
    /// the integer routes — which is what the `QF_LIA` and `QF_UFLIA` losses
    /// are made of — have no stage timings for an icicle to draw. They do carry
    /// `simplex_pivots`, which is deterministic, so they can still put a file
    /// on the work axis.
    pub lia: Option<Reading<LiaCounters>>,
}

/// One emitted row. Built by [`SpanLog::build`]; rendered by
/// [`SpanLog::to_jsonl`].
#[derive(Debug, Clone)]
struct Span {
    id: u64,
    parent: Option<u64>,
    kind: SpanKind,
    route: Option<String>,
    phase: &'static str,
    opened_ns: u64,
    /// `None` is the whole point: an unclosed span is the answer to "who held
    /// the budget when we died".
    closed_ns: Option<u64>,
    edge: Option<EdgeType>,
    outcome: Outcome,
    verdict: Option<&'static str>,
    reason: Option<String>,
    detail: Option<String>,
    /// The budget that ran out, on an [`Outcome::Exhausted`] span.
    bound: Option<String>,
    wall_ns: Option<u64>,
    work_unit: Option<&'static str>,
    work: Option<u64>,
    loop_count: Option<u64>,
    /// The per-round wall-clock distribution of a [`SpanKind::RefinementLoop`],
    /// as log2 millisecond buckets — bucket `0` is `<1 ms`, bucket `k` is
    /// `[2^(k-1), 2^k)` ms, the last is the tail. `None` on every other span
    /// kind, and on a loop whose rounds were never timed.
    loop_hist: Option<Vec<u32>>,
    /// Whether per-round timings exist for a [`SpanKind::RefinementLoop`].
    /// True exactly when `loop_hist` is `Some`; kept as its own field because a
    /// consumer must be able to tell "no distribution recorded" from "a
    /// distribution that happens to be empty".
    loop_hist_available: bool,
    /// `false` when the reading behind this span was taken mid-flight, so every
    /// counter on it is a lower bound.
    complete: bool,
    /// `"prefix-sum"` when `opened_ns` is an observed position in the ladder,
    /// `"duration-only"` when the span has a length and no known position.
    time_basis: &'static str,
    /// How the span was attached to its parent, for stage spans whose
    /// instrument is per-query rather than per-route.
    parent_basis: Option<&'static str>,
    note: Option<String>,
}

/// A built span log for one solve.
#[derive(Debug)]
pub struct SpanLog {
    spans: Vec<Span>,
    run: RunHeader,
}

#[derive(Debug)]
struct RunHeader {
    file: String,
    division: Option<String>,
    verdict: String,
    wall_ns: u64,
    budget_ns: Option<u64>,
    peak_rss_bytes: Option<u64>,
    termination: Termination,
    host: Option<String>,
    solver_commit: Option<String>,
    config_line: Option<String>,
    instrumented: bool,
    instruments: Vec<String>,
    work_unit: Option<&'static str>,
    work: Option<u64>,
}

/// Which deterministic counter a stage's span reports, chosen so the unit
/// always names something the solver counted rather than something derived.
struct StageSpec {
    phase: &'static str,
    ns: u64,
    work_unit: Option<&'static str>,
    work: Option<u64>,
}

impl SpanLog {
    /// Builds the span log for one solve.
    ///
    /// The run span (id 0) always exists, even for a file nothing instrumented:
    /// a file with no spans is "not instrumented", and the run header says so
    /// with `instrumented: false`. It is never a file that took zero time.
    #[must_use]
    pub fn build(inputs: &SpanLogInputs<'_>) -> Self {
        let mut spans = Vec::new();
        let mut instruments = Vec::new();

        // Span 0 is the run. It closes iff the run returned: a watchdog kill
        // leaves it open, which is what makes the whole file renderable as
        // partial without a consumer inferring it from the verdict.
        let run_closed = match inputs.termination {
            Termination::Returned => Some(inputs.wall_ns),
            Termination::WatchdogKill | Termination::WorkerSpawnFailed => None,
        };
        spans.push(Span {
            id: 0,
            parent: None,
            kind: SpanKind::Run,
            route: None,
            phase: "run",
            opened_ns: 0,
            closed_ns: run_closed,
            edge: None,
            outcome: match inputs.termination {
                Termination::Returned => Outcome::Ran,
                Termination::WatchdogKill | Termination::WorkerSpawnFailed => Outcome::Killed,
            },
            verdict: None,
            reason: None,
            detail: None,
            bound: None,
            wall_ns: Some(inputs.wall_ns),
            work_unit: None,
            work: None,
            loop_count: None,
            loop_hist: None,
            loop_hist_available: false,
            complete: matches!(inputs.termination, Termination::Returned),
            time_basis: "observed",
            parent_basis: None,
            note: None,
        });

        let mut next_id: u64 = 1;
        let ladder_ids = push_ladder(&mut spans, &mut next_id, inputs, &mut instruments);
        // Recorded even though it emits no span: an instrument that published
        // and produced nothing drawable is a different statement from one that
        // never published, and the run header is the only place that
        // distinction can live.
        if let Some(lia) = &inputs.lia {
            instruments.push(format!("lia:{}", lia.sampled.label()));
        }
        push_instrument_stages(
            &mut spans,
            &mut next_id,
            inputs,
            &ladder_ids,
            &mut instruments,
        );

        // The run-level deterministic counter, by a fixed precedence so two
        // files in one division are compared on the same unit or not at all.
        // `None` where no reachable counter applies — never a zero.
        let (work_unit, work) = run_work(inputs);

        let instrumented = !instruments.is_empty();
        Self {
            run: RunHeader {
                file: inputs.file.to_owned(),
                division: inputs.division.map(str::to_owned),
                verdict: inputs.verdict.to_owned(),
                wall_ns: inputs.wall_ns,
                budget_ns: inputs.budget_ns,
                peak_rss_bytes: inputs.peak_rss_bytes,
                termination: inputs.termination,
                host: inputs.host.map(str::to_owned),
                solver_commit: inputs.solver_commit.map(str::to_owned),
                config_line: inputs.config_line.as_ref().map(|c| c.value.clone()),
                instrumented,
                instruments,
                work_unit,
                work,
            },
            spans,
        }
    }

    /// The one span that was still open when the run died, if any.
    ///
    /// This is the answer to "who held the budget when we died" — the question
    /// every blind file in this repository turned out to be asking.
    #[must_use]
    pub fn open_segment_span(&self) -> Option<u64> {
        self.spans
            .iter()
            .find(|s| s.kind == SpanKind::OpenSegment)
            .map(|s| s.id)
    }

    /// How many spans the log carries, run span included.
    #[must_use]
    pub fn len(&self) -> usize {
        self.spans.len()
    }

    /// Whether the log carries only the run span — a file nothing instrumented.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.spans.len() <= 1
    }

    /// Renders the log as JSON Lines: one `{"kind":"run",…}` header followed by
    /// one `{"kind":"span",…}` object per span, in id order.
    ///
    /// Hand-rolled rather than `serde`: `axeyum-solver` has no serialization
    /// dependency and this format is small, fixed, and gated by a golden test.
    #[must_use]
    pub fn to_jsonl(&self) -> Vec<String> {
        let mut lines = Vec::with_capacity(self.spans.len() + 1);
        lines.push(self.run_line());
        for span in &self.spans {
            lines.push(span_line(span));
        }
        lines
    }

    fn run_line(&self) -> String {
        let r = &self.run;
        let mut out = String::with_capacity(512);
        out.push_str("{\"kind\":\"run\",\"schema_version\":");
        let _ = write!(out, "{SPAN_LOG_SCHEMA_VERSION}");
        out.push_str(",\"file\":");
        push_str(&mut out, &r.file);
        out.push_str(",\"division\":");
        push_opt_str(&mut out, r.division.as_deref());
        out.push_str(",\"verdict\":");
        push_str(&mut out, &r.verdict);
        let _ = write!(out, ",\"wall_ns\":{}", r.wall_ns);
        out.push_str(",\"budget_ns\":");
        push_opt_u64(&mut out, r.budget_ns);
        // Peak resident set, beside the wall clock and the deterministic work.
        // `null` means the target has no `VmHWM`, never that the run was free.
        out.push_str(",\"peak_rss_bytes\":");
        push_opt_u64(&mut out, r.peak_rss_bytes);
        out.push_str(",\"termination\":");
        push_str(&mut out, r.termination.label());
        out.push_str(",\"host\":");
        push_opt_str(&mut out, r.host.as_deref());
        out.push_str(",\"solver_commit\":");
        push_opt_str(&mut out, r.solver_commit.as_deref());
        out.push_str(",\"config\":");
        push_opt_str(&mut out, r.config_line.as_deref());
        let _ = write!(out, ",\"instrumented\":{}", r.instrumented);
        out.push_str(",\"instruments\":[");
        for (i, name) in r.instruments.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            push_str(&mut out, name);
        }
        out.push_str("],\"work_unit\":");
        push_opt_str(&mut out, r.work_unit);
        out.push_str(",\"work\":");
        push_opt_u64(&mut out, r.work);
        // Named in the data so a renderer cannot mistake a derived offset for
        // an observed one; see the module docs.
        out.push_str(",\"time_basis\":\"prefix-sum-over-attempt-durations\"");
        let _ = write!(out, ",\"spans\":{}", self.spans.len());
        out.push('}');
        out
    }
}

fn span_line(s: &Span) -> String {
    let mut out = String::with_capacity(384);
    out.push_str("{\"kind\":\"span\",\"span_id\":");
    let _ = write!(out, "{}", s.id);
    out.push_str(",\"parent_id\":");
    push_opt_u64(&mut out, s.parent);
    out.push_str(",\"span_kind\":");
    push_str(&mut out, s.kind.label());
    out.push_str(",\"route\":");
    push_opt_str(&mut out, s.route.as_deref());
    out.push_str(",\"phase\":");
    push_str(&mut out, s.phase);
    let _ = write!(out, ",\"opened_at_ns\":{}", s.opened_ns);
    out.push_str(",\"closed_at_ns\":");
    push_opt_u64(&mut out, s.closed_ns);
    out.push_str(",\"edge_type\":");
    push_opt_str(&mut out, s.edge.map(EdgeType::label));
    out.push_str(",\"outcome\":");
    push_str(&mut out, s.outcome.label());
    out.push_str(",\"verdict\":");
    push_opt_str(&mut out, s.verdict);
    out.push_str(",\"reason\":");
    push_opt_str(&mut out, s.reason.as_deref());
    out.push_str(",\"detail\":");
    push_opt_str(&mut out, s.detail.as_deref());
    out.push_str(",\"bound\":");
    push_opt_str(&mut out, s.bound.as_deref());
    out.push_str(",\"wall_ns\":");
    push_opt_u64(&mut out, s.wall_ns);
    out.push_str(",\"work_unit\":");
    push_opt_str(&mut out, s.work_unit);
    out.push_str(",\"work\":");
    push_opt_u64(&mut out, s.work);
    out.push_str(",\"loop_count\":");
    push_opt_u64(&mut out, s.loop_count);
    // `null` beside the flag that says the absence is the solver's, not this
    // renderer's — a loop whose rounds were not timed still says so.
    out.push_str(",\"loop_hist\":");
    match &s.loop_hist {
        None => out.push_str("null"),
        Some(buckets) => {
            out.push('[');
            for (i, count) in buckets.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                let _ = write!(out, "{count}");
            }
            out.push(']');
        }
    }
    out.push_str(",\"loop_hist_available\":");
    let _ = write!(out, "{}", s.loop_hist_available);
    let _ = write!(out, ",\"complete\":{}", s.complete);
    out.push_str(",\"time_basis\":");
    push_str(&mut out, s.time_basis);
    out.push_str(",\"parent_basis\":");
    push_opt_str(&mut out, s.parent_basis);
    out.push_str(",\"note\":");
    push_opt_str(&mut out, s.note.as_deref());
    out.push('}');
    out
}

/// Emits the dispatch ladder: one span per recorded attempt, plus the open
/// segment when the run was killed. Returns the `(span id, route)` pairs a
/// later instrument can attach to.
///
/// Split out of [`SpanLog::build`] because it is the one part of it carrying a
/// rule rather than a transcription: an attempt is a child of the RUN, and the
/// edge to the one before it is what says the two were alternatives.
fn push_ladder(
    spans: &mut Vec<Span>,
    next_id: &mut u64,
    inputs: &SpanLogInputs<'_>,
    instruments: &mut Vec<String>,
) -> Vec<(u64, String)> {
    let mut ladder_ids: Vec<(u64, String)> = Vec::new();
    if let Some(route) = &inputs.route {
        instruments.push(format!("route:{}", route.sampled.label()));
        let complete = route.sampled == Sampled::Complete;
        let attempts = route.value.attempts();
        let elapsed = route.value.elapsed();
        let mut cursor: u64 = 0;
        let mut previous_declined = false;
        for (index, attempt) in attempts.iter().enumerate() {
            let dur = elapsed
                .get(index)
                .map_or(0, |d| u64::try_from(d.as_nanos()).unwrap_or(u64::MAX));
            let opened = cursor;
            cursor = cursor.saturating_add(dur);
            let id = *next_id;
            *next_id += 1;
            let (outcome, verdict, reason, detail, bound) = classify(&attempt.outcome);
            // The FIRST attempt is contained by the run; every later one is
            // there because the previous route declined. Drawing the second
            // as a child of the first is the mistake this field exists to
            // prevent.
            let edge = if previous_declined {
                EdgeType::FellThrough
            } else {
                EdgeType::Nested
            };
            previous_declined = matches!(
                attempt.outcome,
                RouteOutcome::Declined(_) | RouteOutcome::Probe(_)
            );
            spans.push(Span {
                id,
                parent: Some(0),
                kind: SpanKind::RouteAttempt,
                route: Some(attempt.route.to_owned()),
                phase: "dispatch",
                opened_ns: opened,
                closed_ns: Some(cursor),
                edge: Some(edge),
                outcome,
                verdict,
                reason,
                detail,
                bound,
                wall_ns: Some(dur),
                work_unit: None,
                work: None,
                loop_count: None,
                loop_hist: None,
                loop_hist_available: false,
                complete,
                time_basis: "prefix-sum",
                parent_basis: None,
                note: None,
            });
            if attempt.route != "probe" {
                ladder_ids.push((id, attempt.route.to_owned()));
            }
        }

        // The open segment. `bound_by` maximises over RECORDED attempts and
        // an attempt is recorded when it FINISHES, so on a killed run the
        // route actually eating the budget contributed nothing to that
        // comparison. Measured 2026-09-08 on a `QF_LRA` file: `bound_by`
        // named a 20 ms probe on a 25,241 ms run. This span carries the
        // missing time.
        if let Some(open_ns) = inputs.open_segment_ns {
            let id = *next_id;
            *next_id += 1;
            spans.push(Span {
                id,
                parent: Some(0),
                kind: SpanKind::OpenSegment,
                // Deliberately not a route name. A trace learns a route's
                // label on the way OUT, so the route running when the kill
                // landed is unnamed. `after` names the boundary, which is
                // all the instrument honestly knows.
                route: None,
                phase: "open",
                opened_ns: cursor,
                closed_ns: None,
                edge: Some(EdgeType::FellThrough),
                outcome: Outcome::Killed,
                verdict: None,
                reason: Some("watchdog-kill".to_owned()),
                detail: route.value.last_recorded_route().map(str::to_owned),
                bound: inputs.budget_ns.map(|ns| format!("wall-ns:{ns}")),
                wall_ns: Some(open_ns),
                work_unit: None,
                work: None,
                loop_count: None,
                loop_hist: None,
                loop_hist_available: false,
                complete: false,
                time_basis: "prefix-sum",
                parent_basis: None,
                note: Some(
                    "the route running here is unnamed: a trace records a route on the way \
                     out, so `detail` names the last route that RETURNED, not the one holding \
                     the budget"
                        .to_owned(),
                ),
            });
        }
    }
    ladder_ids
}

/// Emits one stage span per instrument reading, attached by [`attach_to`].
///
/// Split out of [`SpanLog::build`] for length. Every block here follows the
/// same shape: gate on the reading existing, record its provenance, and emit
/// the stages with the deterministic counter each one actually owns.
fn push_instrument_stages(
    spans: &mut Vec<Span>,
    next_id: &mut u64,
    inputs: &SpanLogInputs<'_>,
    ladder_ids: &[(u64, String)],
    instruments: &mut Vec<String>,
) {
    // Stage spans. Each instrument snapshot is per-QUERY, so attribution to
    // a route is only sound in the two cases `attach_to` accepts.
    if let Some(front_door) = &inputs.front_door_parse {
        instruments.push(format!("front-door:{}", front_door.sampled.label()));
        let (parent, basis) = attach_to("front-door", ladder_ids);
        push_stage(
            spans,
            next_id,
            parent,
            basis,
            Some("front-door"),
            &StageSpec {
                phase: "parse",
                ns: nanos(front_door.value),
                work_unit: None,
                work: None,
            },
            front_door.sampled,
        );
    }
    if let Some(dl) = &inputs.dl_online {
        let (elapsed, calls) = dl.value;
        if calls > 0 {
            instruments.push(format!("dl-online:{}", dl.sampled.label()));
            let (parent, basis) = attach_to("dl-online", ladder_ids);
            push_stage(
                spans,
                next_id,
                parent,
                basis,
                Some("dl-online"),
                &StageSpec {
                    phase: "dl-online",
                    ns: nanos(elapsed),
                    work_unit: Some("calls"),
                    work: Some(calls),
                },
                dl.sampled,
            );
        }
    }
    push_bv_stages(spans, next_id, inputs, ladder_ids, instruments);
    push_theory_stages(spans, next_id, inputs, ladder_ids, instruments);
    push_lazy_loop(spans, next_id, inputs, ladder_ids, instruments);
}

/// The `sat-bv` pipeline's stage spans, plus the in-flight stage a killed
/// check was inside. Its own function so the `pending` rule below stays
/// readable: a stage `BvLayerStats` defaults to zero because it was never
/// REACHED must not be emitted as a measured zero.
fn push_bv_stages(
    spans: &mut Vec<Span>,
    next_id: &mut u64,
    inputs: &SpanLogInputs<'_>,
    ladder_ids: &[(u64, String)],
    instruments: &mut Vec<String>,
) {
    if let Some(bv) = &inputs.bv {
        instruments.push(format!("bv-layer:{}", bv.sampled.label()));
        let (parent, basis) = attach_to("sat-bv", ladder_ids);
        let s = &bv.value;
        for spec in &[
            StageSpec {
                phase: "bit_blast",
                ns: nanos(s.bit_blast),
                work_unit: Some("aig_nodes"),
                work: Some(s.aig_nodes),
            },
            StageSpec {
                phase: "cnf_encode",
                ns: nanos(s.cnf_encode),
                work_unit: Some("cnf_clauses"),
                work: Some(s.cnf_clauses),
            },
            StageSpec {
                phase: "cnf_inprocess",
                ns: nanos(s.cnf_inprocess),
                work_unit: None,
                work: None,
            },
            StageSpec {
                phase: "sat_solve",
                ns: nanos(s.solve),
                work_unit: None,
                work: None,
            },
            StageSpec {
                phase: "model_lift",
                ns: nanos(s.model_lift),
                work_unit: None,
                work: None,
            },
            StageSpec {
                phase: "model_replay",
                ns: nanos(s.model_replay),
                work_unit: None,
                work: None,
            },
        ] {
            push_stage(
                spans,
                next_id,
                parent,
                basis,
                Some("sat-bv"),
                spec,
                bv.sampled,
            );
        }
    }
    // A `sat-bv` check killed mid-pipeline has stages it never REACHED, and
    // `BvLayerStats` defaults those to zero. A zero that means "not reached"
    // rendered beside a zero that means "measured" is the exact shape of
    // absence-as-zero this format exists to refuse, so the unreached stages
    // are emitted as spans with no duration at all.
    if let Some((stage, pending)) = &inputs.bv_stage {
        let (parent, basis) = attach_to("sat-bv", ladder_ids);
        let id = *next_id;
        *next_id += 1;
        let opened = span_start(spans, parent);
        spans.push(Span {
            id,
            parent: Some(parent),
            kind: SpanKind::Stage,
            route: Some("sat-bv".to_owned()),
            phase: "bv_stage_in_flight",
            opened_ns: opened,
            closed_ns: None,
            edge: Some(EdgeType::Nested),
            outcome: Outcome::Killed,
            verdict: None,
            reason: Some((*stage).to_owned()),
            detail: Some(pending.join(",")),
            bound: None,
            wall_ns: None,
            work_unit: None,
            work: None,
            loop_count: None,
            loop_hist: None,
            loop_hist_available: false,
            complete: false,
            time_basis: "duration-only",
            parent_basis: Some(basis),
            note: Some(
                "the check was inside this stage when it was killed; `detail` names the \
                 stages it had NOT reached, whose timings are absent rather than zero"
                    .to_owned(),
            ),
        });
    }
}

/// The CDCL(T) driver's stage spans.
fn push_theory_stages(
    spans: &mut Vec<Span>,
    next_id: &mut u64,
    inputs: &SpanLogInputs<'_>,
    ladder_ids: &[(u64, String)],
    instruments: &mut Vec<String>,
) {
    if let Some(theory) = &inputs.theory {
        instruments.push(format!("theory-layer:{}", theory.sampled.label()));
        let (parent, basis) = attach_to("cdcl-t", ladder_ids);
        let s = &theory.value;
        for spec in &[
            StageSpec {
                phase: "boolean_propagate",
                ns: nanos(s.boolean_propagate),
                work_unit: Some("decisions"),
                work: Some(s.decisions),
            },
            StageSpec {
                phase: "theory_assert",
                ns: nanos(s.theory_assert),
                work_unit: None,
                work: None,
            },
            StageSpec {
                phase: "theory_propagate",
                ns: nanos(s.theory_propagate),
                work_unit: Some("theory_propagations"),
                work: Some(s.theory_propagations),
            },
            StageSpec {
                phase: "theory_push_pop",
                ns: nanos(s.theory_push_pop),
                work_unit: None,
                work: None,
            },
            StageSpec {
                phase: "conflict_analysis",
                ns: nanos(s.conflict_analysis),
                work_unit: Some("theory_conflicts"),
                work: Some(s.theory_conflicts),
            },
            StageSpec {
                phase: "theory_final_check",
                ns: nanos(s.theory_final_check),
                work_unit: Some("final_checks"),
                work: Some(s.final_checks),
            },
            StageSpec {
                phase: "theory_explain",
                ns: nanos(s.theory_explain),
                work_unit: None,
                work: None,
            },
        ] {
            push_stage(
                spans,
                next_id,
                parent,
                basis,
                Some("cdcl-t"),
                spec,
                theory.sampled,
            );
        }
    }
}

/// The abstraction/refinement loops: **one span per loop that was entered**,
/// each carrying its own round count and per-round distribution, then the
/// three-way split of where a round's time goes.
///
/// One span per loop, not one for all of them. Until 2026-09-08 this emitted a
/// single span whose `loop_count` was `lra_rounds + nra_rounds`, and a
/// `QF_NIA` sweep read "all 50 files enter the refinement loop, 25 for exactly
/// one round" off it — a statement about the `nra` loop reached from the real
/// relaxation refuter, presented as one about the nonlinear-integer route. Two
/// deciders behind one count is how that happened.
///
/// `instruments` is taken even though only one block writes it, so every stage
/// emitter has one signature.
fn push_lazy_loop(
    spans: &mut Vec<Span>,
    next_id: &mut u64,
    inputs: &SpanLogInputs<'_>,
    ladder_ids: &[(u64, String)],
    instruments: &mut Vec<String>,
) {
    let Some(lazy) = &inputs.lazy else {
        return;
    };
    let s = &lazy.value;
    if s.entries() > 0 {
        instruments.push(format!("lazy-smt:{}", lazy.sampled.label()));
    }
    let mut emitted_stages = false;
    for which in LazySmtLoop::ALL {
        if s.entries_of(which) == 0 {
            continue;
        }
        let (parent, basis) = attach_to("lazy-smt", ladder_ids);
        let id = *next_id;
        *next_id += 1;
        let opened = span_start(spans, parent);
        spans.push(lazy_loop_span(id, parent, basis, opened, lazy, which));
        // The three-way split, so "the propositional solve grew" is
        // distinguishable from "the second LP per round is the cost" — the two
        // have opposite fixes and both scale with the round count.
        //
        // Emitted ONCE, under the first loop span, because the underlying
        // fields are query-wide sums across every lazy loop. Hanging the same
        // seconds under each of three parents would make the tree sum to three
        // times the query.
        if emitted_stages {
            continue;
        }
        emitted_stages = true;
        push_lazy_stage_children(spans, next_id, id, s, lazy.sampled);
    }
}

/// One loop's span. Split out of [`push_lazy_loop`] so the emitter stays under
/// the line cap now that there are three loops rather than one.
fn lazy_loop_span(
    id: u64,
    parent: u64,
    basis: &'static str,
    opened: u64,
    lazy: &Reading<LazySmtCounters>,
    which: LazySmtLoop,
) -> Span {
    let s = &lazy.value;
    let rounds = s.rounds_of(which);
    let entries = s.entries_of(which);
    let hist = s.hist(which);
    // The loop's OWN cost, from its own histogram, not the query-wide stage
    // totals: with three loops behind one counter set those totals are a sum
    // over all of them and would attribute another loop's seconds to this span.
    let accounted = nanos(hist.total());
    let pending_ms = if s.pending_loop == which.index() {
        s.pending_round.as_millis()
    } else {
        0
    };
    Span {
        id,
        parent: Some(parent),
        kind: SpanKind::RefinementLoop,
        route: Some(format!("lazy-smt:{}", which.label())),
        phase: "refinement",
        opened_ns: opened,
        closed_ns: Some(opened.saturating_add(accounted)),
        edge: Some(EdgeType::RefinementRound),
        outcome: Outcome::Ran,
        verdict: None,
        reason: None,
        detail: Some(format!(
            "loop={} entries={entries} rounds={rounds} filed_rounds={} \
             max_round_ms={} max_round_index={} pending_round_ms={pending_ms}",
            which.label(),
            hist.rounds(),
            hist.max().as_millis(),
            hist.max_round(),
        )),
        bound: None,
        wall_ns: Some(accounted),
        work_unit: Some("rounds"),
        work: Some(rounds),
        loop_count: Some(rounds),
        loop_hist: (!hist.is_empty()).then(|| hist.buckets().to_vec()),
        loop_hist_available: !hist.is_empty(),
        complete: lazy.sampled == Sampled::Complete,
        time_basis: "duration-only",
        parent_basis: Some(basis),
        note: Some(
            "loop_hist is log2 MILLISECOND buckets: index 0 is <1 ms, index k is \
             [2^(k-1), 2^k) ms, the last index is the tail. A round still in flight \
             is NOT in it -- see pending_round_ms in the detail. The three stage \
             children are query-wide totals across ALL lazy loops, not this loop's \
             alone, and hang under the FIRST loop span only"
                .to_owned(),
        ),
    }
}

/// The three query-wide stage children, emitted once under `parent`.
fn push_lazy_stage_children(
    spans: &mut Vec<Span>,
    next_id: &mut u64,
    parent: u64,
    s: &LazySmtCounters,
    sampled: Sampled,
) {
    for spec in &[
        StageSpec {
            phase: "skeleton_solve",
            ns: nanos(s.skeleton_solve),
            work_unit: Some("skeleton_solves"),
            work: Some(
                s.skeleton_sat
                    .saturating_add(s.skeleton_unsat)
                    .saturating_add(s.skeleton_unknown),
            ),
        },
        StageSpec {
            phase: "theory_check",
            ns: nanos(s.theory_check),
            work_unit: Some("cubes"),
            work: Some(
                s.theory_sat
                    .saturating_add(s.theory_unsat)
                    .saturating_add(s.theory_unknown),
            ),
        },
        StageSpec {
            phase: "core_extraction",
            ns: nanos(s.core_extraction),
            work_unit: Some("blocking_clauses"),
            work: Some(s.blocking_clauses),
        },
    ] {
        push_stage(
            spans,
            next_id,
            parent,
            "loop-parent",
            Some("lazy-smt"),
            spec,
            sampled,
        );
    }
}

/// Maps a recorded route outcome onto the span vocabulary.
///
/// The one non-mechanical line: a
/// [`crate::route_trace::DeclineReason::Budget`] is **not** a decline, it is an
/// exhausted bound, and the detail it carries is the bound that bit.
fn classify(
    outcome: &RouteOutcome,
) -> (
    Outcome,
    Option<&'static str>,
    Option<String>,
    Option<String>,
    Option<String>,
) {
    match outcome {
        RouteOutcome::Probe(detail) => (Outcome::Probe, None, None, Some(detail.clone()), None),
        RouteOutcome::Decided(Verdict::Sat) => (Outcome::Decided, Some("sat"), None, None, None),
        RouteOutcome::Decided(Verdict::Unsat) => {
            (Outcome::Decided, Some("unsat"), None, None, None)
        }
        RouteOutcome::Declined(reason) => match reason {
            DeclineReason::Unsupported => (
                Outcome::Declined,
                None,
                Some("unsupported".to_owned()),
                None,
                None,
            ),
            // Same span `reason` as the payload-free form on purpose — the two
            // are the same *kind* of decline, and a consumer grouping by reason
            // must keep seeing one bucket. What was missing was the message,
            // which now reaches the span's detail field.
            DeclineReason::UnsupportedDetail(detail) => (
                Outcome::Declined,
                None,
                Some("unsupported".to_owned()),
                Some(detail.clone()),
                None,
            ),
            DeclineReason::NotApplicable => (
                Outcome::Declined,
                None,
                Some("not-applicable".to_owned()),
                None,
                None,
            ),
            DeclineReason::Budget(detail) => (
                Outcome::Exhausted,
                None,
                Some("budget".to_owned()),
                Some(detail.clone()),
                Some(detail.clone()),
            ),
            DeclineReason::Incomplete(unknown) => (
                Outcome::Declined,
                None,
                Some("incomplete".to_owned()),
                Some(unknown.detail.clone()),
                None,
            ),
            DeclineReason::VerifierRejected(detail) => (
                Outcome::Declined,
                None,
                Some("verifier-rejected".to_owned()),
                Some(detail.clone()),
                None,
            ),
        },
    }
}

/// Where a per-query instrument's stage spans attach, and on what basis.
///
/// An instrument snapshot describes the query, not one attempt in the trail, so
/// there are exactly two cases where attaching it to a route is sound: the
/// route label matches the instrument's own name, or the trail has one non-probe
/// attempt and there is nothing to be ambiguous between. Everything else
/// attaches to the run span and says `"unattributed"` — a renderer can then
/// draw it outside the ladder instead of under a route that may not have run it.
fn attach_to(instrument: &str, ladder: &[(u64, String)]) -> (u64, &'static str) {
    if let Some((id, _)) = ladder.iter().find(|(_, route)| route == instrument) {
        return (*id, "route-label-match");
    }
    if ladder.len() == 1 {
        return (ladder[0].0, "sole-route");
    }
    (0, "unattributed")
}

fn push_stage(
    spans: &mut Vec<Span>,
    next_id: &mut u64,
    parent: u64,
    basis: &'static str,
    route: Option<&str>,
    spec: &StageSpec,
    sampled: Sampled,
) {
    let id = *next_id;
    *next_id += 1;
    let opened = span_start(spans, parent);
    spans.push(Span {
        id,
        parent: Some(parent),
        kind: SpanKind::Stage,
        route: route.map(str::to_owned),
        phase: spec.phase,
        opened_ns: opened,
        closed_ns: Some(opened.saturating_add(spec.ns)),
        edge: Some(EdgeType::Nested),
        outcome: Outcome::Ran,
        verdict: None,
        reason: None,
        detail: None,
        bound: None,
        wall_ns: Some(spec.ns),
        work_unit: spec.work_unit,
        work: spec.work,
        loop_count: None,
        loop_hist: None,
        loop_hist_available: false,
        complete: sampled == Sampled::Complete,
        time_basis: "duration-only",
        parent_basis: Some(basis),
        note: None,
    });
}

/// The run's deterministic work counter, by a fixed precedence.
///
/// One unit per run, chosen from what the query actually exercised, so a
/// consumer switching the gallery's axis from wall time to work compares files
/// on a unit it can name — and sees `null` on the files where no reachable
/// counter applies rather than a zero that looks like free work.
///
/// Ticks (`axeyum_cnf::ticks`) would be the right unit for all of them and are
/// not reachable from a shipping solve; see the module's *Known gaps*.
fn run_work(inputs: &SpanLogInputs<'_>) -> (Option<&'static str>, Option<u64>) {
    if let Some(theory) = &inputs.theory
        && theory.value.decisions > 0
    {
        return (Some("decisions"), Some(theory.value.decisions));
    }
    if let Some(lia) = &inputs.lia
        && lia.value.simplex_pivots > 0
    {
        return (Some("simplex_pivots"), Some(lia.value.simplex_pivots));
    }
    if let Some(lazy) = &inputs.lazy {
        let rounds = lazy.value.lra_rounds.saturating_add(lazy.value.nra_rounds);
        if rounds > 0 {
            return (Some("refinement_rounds"), Some(rounds));
        }
    }
    if let Some(bv) = &inputs.bv
        && bv.value.cnf_clauses > 0
    {
        return (Some("cnf_clauses"), Some(bv.value.cnf_clauses));
    }
    (None, None)
}

/// The offset a child span inherits: its parent's own offset.
///
/// A stage span has a length and no observed position (see the module docs), so
/// it is drawn from wherever its parent started. A parent id that is not in
/// `spans` yields 0 rather than panicking: this is telemetry.
fn span_start(spans: &[Span], parent: u64) -> u64 {
    spans
        .iter()
        .find(|s| s.id == parent)
        .map_or(0, |s| s.opened_ns)
}

fn nanos(d: Duration) -> u64 {
    u64::try_from(d.as_nanos()).unwrap_or(u64::MAX)
}

fn push_opt_u64(out: &mut String, value: Option<u64>) {
    match value {
        Some(v) => {
            let _ = write!(out, "{v}");
        }
        None => out.push_str("null"),
    }
}

fn push_opt_str(out: &mut String, value: Option<&str>) {
    match value {
        Some(v) => push_str(out, v),
        None => out.push_str("null"),
    }
}

/// Writes `value` as a JSON string literal, escaping what RFC 8259 requires.
fn push_str(out: &mut String, value: &str) {
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Reads the SMT-LIB division off a corpus path, or `None`.
///
/// A division is a path SEGMENT that is a division name (`QF_BV`, `UF`, …), not
/// a substring: `.../QF_LRA/2017-Heizmann/...` is `QF_LRA`, and a file whose
/// path has no such segment gets `None` rather than a guess from the logic
/// declared inside it — a `(set-logic)` line and the division a file was
/// benchmarked in are different claims.
#[must_use]
pub fn division_from_path(path: &str) -> Option<&str> {
    path.split('/').rev().find(|segment| {
        !segment.is_empty()
            && segment
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
            && segment.chars().any(|c| c.is_ascii_uppercase())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::{UnknownKind, UnknownReason};
    use crate::lia_counters::LiaCounters;

    fn ladder() -> RouteTrace {
        let mut trace = RouteTrace::new();
        trace.record_probe("fragment=QF_LRA routes=[dl-online,lra]");
        trace.record_declined("dl-online", DeclineReason::NotApplicable);
        trace.record_declined("nra", DeclineReason::Budget("cnf-nodes=2000000".into()));
        trace.record_decided("lia-simplex", Verdict::Unsat);
        trace
    }

    #[test]
    fn a_budget_decline_is_exhausted_and_names_the_bound() {
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unsat",
            route: Some(Reading::complete(ladder())),
            ..SpanLogInputs::default()
        });
        let lines = log.to_jsonl();
        let nra = lines
            .iter()
            .find(|l| l.contains("\"route\":\"nra\""))
            .expect("the nra attempt must be emitted");
        assert!(
            nra.contains("\"outcome\":\"exhausted\""),
            "a budget decline is an exhausted bound, not a modelling decline: {nra}"
        );
        assert!(
            nra.contains("\"bound\":\"cnf-nodes=2000000\""),
            "the bound that bit must be on the span: {nra}"
        );
        // The distinction the format exists for: the other decline must NOT be
        // exhausted.
        let dl = lines
            .iter()
            .find(|l| l.contains("\"route\":\"dl-online\""))
            .expect("the dl-online attempt must be emitted");
        assert!(dl.contains("\"outcome\":\"declined\""), "got: {dl}");
        assert!(dl.contains("\"bound\":null"), "got: {dl}");
    }

    #[test]
    fn the_ladder_is_sequential_not_nested() {
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unsat",
            route: Some(Reading::complete(ladder())),
            ..SpanLogInputs::default()
        });
        let lines = log.to_jsonl();
        let attempts: Vec<&String> = lines
            .iter()
            .filter(|l| l.contains("\"span_kind\":\"route_attempt\""))
            .collect();
        assert_eq!(attempts.len(), 4, "one span per recorded attempt");
        for line in &attempts {
            assert!(
                line.contains("\"parent_id\":0"),
                "every ladder rung is a child of the RUN, never of the route \
                 before it — that is the flame-graph mistake: {line}"
            );
        }
        assert!(
            attempts[1].contains("\"edge_type\":\"fell_through\""),
            "an attempt after a decline fell through to: {}",
            attempts[1]
        );
    }

    #[test]
    fn a_killed_run_leaves_the_open_span_unclosed_and_the_run_span_too() {
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unknown",
            wall_ns: 25_241_000_000,
            budget_ns: Some(24_000_000_000),
            termination: Termination::WatchdogKill,
            route: Some(Reading {
                value: ladder(),
                sampled: Sampled::InFlight,
            }),
            open_segment_ns: Some(25_215_000_000),
            ..SpanLogInputs::default()
        });
        assert!(log.open_segment_span().is_some());
        let lines = log.to_jsonl();
        let open = lines
            .iter()
            .find(|l| l.contains("\"span_kind\":\"open_segment\""))
            .expect("a killed run must emit the open segment");
        assert!(
            open.contains("\"closed_at_ns\":null"),
            "an unclosed span is the answer to who held the budget: {open}"
        );
        assert!(open.contains("\"outcome\":\"killed\""), "got: {open}");
        assert!(
            open.contains("\"wall_ns\":25215000000"),
            "the open segment carries the missing time: {open}"
        );
        let run = lines
            .iter()
            .find(|l| l.contains("\"span_kind\":\"run\""))
            .expect("the run span always exists");
        assert!(
            run.contains("\"closed_at_ns\":null"),
            "a killed run's own span is open too: {run}"
        );
    }

    #[test]
    fn a_file_with_no_instruments_is_not_instrumented_never_zero() {
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unknown",
            wall_ns: 0,
            ..SpanLogInputs::default()
        });
        assert!(log.is_empty());
        let header = &log.to_jsonl()[0];
        assert!(
            header.contains("\"instrumented\":false"),
            "a file nothing measured must say so: {header}"
        );
        assert!(
            header.contains("\"work_unit\":null") && header.contains("\"work\":null"),
            "no reachable counter is null, not 0: {header}"
        );
    }

    #[test]
    fn a_refinement_loop_is_one_span_per_loop_carrying_its_own_round_histogram() {
        // The histogram is BUILT BY RECORDING, not typed in: a fixture that
        // set `round_hist` by hand would pass with the recorder deleted, which
        // is precisely the failure this test exists to catch. The two loops are
        // given deliberately different round shapes so a span that took the
        // wrong loop's distribution cannot pass.
        let counters = {
            let guard = crate::lazy_smt_counters::LazySmtCountersGuard::enable();
            crate::lazy_smt_counters::record_entry(LazySmtLoop::Nra, 7);
            // One enormous round.
            crate::lazy_smt_counters::record_skeleton(
                LazySmtLoop::Nra,
                Duration::from_millis(1),
                crate::lazy_smt_counters::RoundOutcome::Sat,
            );
            crate::lazy_smt_counters::record_theory(
                Duration::from_millis(4_000),
                crate::lazy_smt_counters::RoundOutcome::Unknown,
            );
            crate::lazy_smt_counters::record_entry(LazySmtLoop::Nia, 3);
            // Three tiny ones.
            for _ in 0..3 {
                crate::lazy_smt_counters::record_skeleton(
                    LazySmtLoop::Nia,
                    Duration::from_micros(200),
                    crate::lazy_smt_counters::RoundOutcome::Sat,
                );
            }
            drop(guard);
            crate::lazy_smt_counters::last_lazy_smt_counters().expect("armed")
        };
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unknown",
            lazy: Some(Reading::complete(counters)),
            ..SpanLogInputs::default()
        });
        let lines = log.to_jsonl();
        let loops: Vec<&String> = lines
            .iter()
            .filter(|l| l.contains("\"span_kind\":\"refinement_loop\""))
            .collect();
        assert_eq!(
            loops.len(),
            2,
            "one span per loop ENTERED, and the lra loop was not: {loops:?}"
        );
        let nra = loops
            .iter()
            .find(|l| l.contains("\"route\":\"lazy-smt:nra\""))
            .expect("the nra loop must be its own span");
        let nia = loops
            .iter()
            .find(|l| l.contains("\"route\":\"lazy-smt:nia\""))
            .expect("the nia loop must be its own span");
        // 4001 ms lands in log2 bucket 12 ([2048, 4096) ms); 200 us lands in
        // bucket 0 (<1 ms). Spelled out rather than recomputed here, so the
        // expectation is a statement and not a restatement of the code.
        assert!(
            nra.contains("\"loop_count\":1") && nra.contains("\"loop_hist_available\":true"),
            "got: {nra}"
        );
        assert!(
            nra.contains("\"loop_hist\":[0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0]"),
            "ONE round of ~4 s must sit alone in the 2048-4096 ms bucket: {nra}"
        );
        assert!(
            nia.contains("\"loop_count\":3")
                && nia.contains("\"loop_hist\":[3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]"),
            "THREE sub-millisecond rounds must sit in bucket 0: {nia}"
        );
        // The distinction the old single-span shape could not make: the two
        // loops have different round shapes behind one `rounds()` total, and
        // the fix each needs is the opposite of the other's.
        assert!(
            !nra.contains("\"loop_hist\":[3,") && !nia.contains("\"loop_hist_available\":false"),
            "a span must carry ITS loop's distribution: nra={nra} nia={nia}"
        );
    }

    #[test]
    fn a_loop_whose_rounds_were_never_timed_says_the_distribution_is_absent() {
        // The negative control for the test above, and the reason
        // `loop_hist_available` survives as its own field: a counter snapshot
        // with rounds but no FILED round must still refuse to draw them.
        let counters = LazySmtCounters {
            nra_entries: 1,
            nra_rounds: 513,
            ..LazySmtCounters::default()
        };
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unknown",
            lazy: Some(Reading::complete(counters)),
            ..SpanLogInputs::default()
        });
        let lines = log.to_jsonl();
        let loop_span = lines
            .iter()
            .find(|l| l.contains("\"span_kind\":\"refinement_loop\""))
            .expect("the loop must still be a span");
        assert!(loop_span.contains("\"loop_count\":513"), "got: {loop_span}");
        assert!(
            loop_span.contains("\"loop_hist\":null")
                && loop_span.contains("\"loop_hist_available\":false"),
            "513 untimed rounds must not become a drawn distribution: {loop_span}"
        );
    }

    #[test]
    fn an_in_flight_reading_marks_every_span_it_produced_incomplete() {
        let counters = LazySmtCounters {
            lra_entries: 1,
            lra_rounds: 4,
            ..LazySmtCounters::default()
        };
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unknown",
            lazy: Some(Reading {
                value: counters,
                sampled: Sampled::InFlight,
            }),
            ..SpanLogInputs::default()
        });
        for line in log
            .to_jsonl()
            .iter()
            .filter(|l| l.contains("\"route\":\"lazy-smt\""))
        {
            assert!(
                line.contains("\"complete\":false"),
                "a mid-flight counter is a lower bound and the span must say so: {line}"
            );
        }
    }

    #[test]
    fn a_per_query_instrument_is_unattributed_when_the_ladder_is_ambiguous() {
        let theory = TheoryLayerStats {
            boolean_propagate: Duration::from_millis(120),
            decisions: 63_623,
            ..TheoryLayerStats::default()
        };
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unsat",
            route: Some(Reading::complete(ladder())),
            theory: Some(Reading::complete(theory)),
            ..SpanLogInputs::default()
        });
        let line = log
            .to_jsonl()
            .into_iter()
            .find(|l| l.contains("\"phase\":\"boolean_propagate\""))
            .expect("the theory stage must be emitted");
        assert!(
            line.contains("\"parent_basis\":\"unattributed\"") && line.contains("\"parent_id\":0"),
            "an instrument that describes the QUERY must not be drawn under a \
             route that may not have run it: {line}"
        );
        assert!(
            line.contains("\"work_unit\":\"decisions\"") && line.contains("\"work\":63623"),
            "the deterministic counter must travel beside the wall time: {line}"
        );
    }

    #[test]
    fn a_route_labelled_instrument_attaches_to_its_route() {
        let mut trace = RouteTrace::new();
        trace.record_probe("p");
        trace.record_declined("dl-online", DeclineReason::NotApplicable);
        trace.record_declined("lia-simplex", DeclineReason::Unsupported);
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unknown",
            route: Some(Reading::complete(trace)),
            dl_online: Some(Reading::complete((Duration::from_millis(7), 3))),
            ..SpanLogInputs::default()
        });
        let line = log
            .to_jsonl()
            .into_iter()
            .find(|l| l.contains("\"phase\":\"dl-online\""))
            .expect("the dl-online stage must be emitted");
        assert!(
            line.contains("\"parent_basis\":\"route-label-match\""),
            "got: {line}"
        );
        assert!(!line.contains("\"parent_id\":0"), "got: {line}");
    }

    #[test]
    fn an_incomplete_unknown_is_not_reported_as_a_budget() {
        let mut trace = RouteTrace::new();
        trace.record_declined(
            "nra",
            DeclineReason::Incomplete(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "nonlinear real arithmetic is incomplete here".into(),
            }),
        );
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unknown",
            route: Some(Reading::complete(trace)),
            ..SpanLogInputs::default()
        });
        let line = log
            .to_jsonl()
            .into_iter()
            .find(|l| l.contains("\"route\":\"nra\""))
            .expect("the attempt must be emitted");
        assert!(line.contains("\"outcome\":\"declined\""), "got: {line}");
        assert!(line.contains("\"bound\":null"), "got: {line}");
    }

    #[test]
    fn the_integer_routes_reach_the_work_axis_with_no_stage_span() {
        let counters = LiaCounters {
            simplex_pivots: 41_337,
            ..LiaCounters::default()
        };
        let log = SpanLog::build(&SpanLogInputs {
            file: "x.smt2",
            verdict: "unknown",
            lia: Some(Reading::complete(counters)),
            ..SpanLogInputs::default()
        });
        let lines = log.to_jsonl();
        assert!(
            lines[0].contains("\"work_unit\":\"simplex_pivots\"")
                && lines[0].contains("\"work\":41337"),
            "the integer routes carry a deterministic counter even with no \
             timing: {}",
            lines[0]
        );
        assert!(
            lines[0].contains("\"lia:complete\""),
            "an instrument that published and drew nothing is not an instrument \
             that never published: {}",
            lines[0]
        );
        // `LiaCounters` has no duration field at all, so there is nothing to
        // draw and the log must not invent one.
        assert!(
            !lines.iter().any(|l| l.contains("\"route\":\"lia\"")),
            "no stage span may be fabricated from counters with no timings"
        );
    }

    #[test]
    fn division_comes_from_a_path_segment_not_a_substring() {
        assert_eq!(
            division_from_path(
                "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/QF_LRA/2017-H/a.smt2"
            ),
            Some("QF_LRA")
        );
        assert_eq!(division_from_path("/tmp/scratch/a.smt2"), None);
    }

    #[test]
    fn every_emitted_line_is_one_json_object_with_no_raw_control_characters() {
        let mut trace = RouteTrace::new();
        trace.record_probe("detail with \"quotes\", a \\ and a\ttab");
        let log = SpanLog::build(&SpanLogInputs {
            file: "a \"weird\"\\name.smt2",
            verdict: "unknown",
            route: Some(Reading::complete(trace)),
            ..SpanLogInputs::default()
        });
        for line in log.to_jsonl() {
            assert!(line.starts_with('{') && line.ends_with('}'), "got: {line}");
            assert!(
                !line.contains('\n') && !line.contains('\t'),
                "a raw control character would break JSON Lines: {line}"
            );
        }
    }
}
