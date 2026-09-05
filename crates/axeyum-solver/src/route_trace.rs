//! Route-trace / decline-reason telemetry for the [`crate::check_auto`]
//! dispatcher.
//!
//! # The additive-telemetry contract
//!
//! A [`RouteTrace`] records *which* dispatch routes the auto-solver tried and
//! *why* each one declined, with the decisive route at the end of the trail. It
//! is the structured backing for a `(get-info :reason-unknown)`-style surface.
//!
//! The single load-bearing invariant is **verdict invariance**: producing a
//! trace must never change the answer. Concretely,
//!
//! ```text
//! check_auto_explained(arena, &a, &cfg).map(|(r, _)| r)
//!     == check_auto(arena, &a, &cfg)
//! ```
//!
//! for every query, always. This is achieved structurally rather than by
//! convention: [`crate::check_auto`] and [`crate::check_auto_explained`] call
//! the **same** internal dispatch, distinguished only by whether a
//! `&mut RouteTrace` recorder is threaded in. Recording is a pure side effect at
//! the decide/decline sites that already exist — it never participates in a
//! branch condition, so the control flow (and therefore the verdict) is
//! identical whether or not a recorder is present. The differential gate in
//! `tests/route_trace.rs` pins this for a deterministic corpus.
//!
//! The taxonomy deliberately **reuses** the existing decline vocabulary:
//! [`DeclineReason`] wraps [`crate::UnknownReason`] / [`crate::UnknownKind`]
//! content rather than inventing a parallel set of strings, so a route that
//! returns `Unknown(reason)` and one that records why it declined speak the same
//! language.

use core::fmt::Write as _;

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017),
// matching the shim already used at the dispatch call sites in `auto.rs`.
#[cfg(not(target_arch = "wasm32"))]
use std::time::{Duration, Instant};
#[cfg(target_arch = "wasm32")]
use web_time::{Duration, Instant};

use crate::backend::{CheckResult, UnknownKind, UnknownReason};

/// A decisive verdict recorded against a route — the satisfiability answer a
/// route returned when it did *not* decline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The route decided the query satisfiable.
    Sat,
    /// The route decided the query unsatisfiable.
    Unsat,
}

/// Why a dispatch route declined to decide the query.
///
/// This reuses the existing [`UnknownKind`] / [`UnknownReason`] vocabulary
/// rather than introducing a parallel taxonomy: `Incomplete`, `ResourceLimit`,
/// and `Budget` carry the same classification (and detail string) the solver
/// would surface in a [`CheckResult::Unknown`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclineReason {
    /// The route does not handle this theory/fragment at all (it reported an
    /// `Unsupported` decline, or its feature gate did not match).
    Unsupported,
    /// The probe determined this route does not match the query's shape, so it
    /// was skipped without running.
    NotApplicable,
    /// A deterministic resource budget — a node, CNF, round, or width cap —
    /// was exhausted. The string carries the [`UnknownReason::detail`].
    Budget(String),
    /// The route ran but returned `Unknown` for an incompleteness reason; the
    /// payload preserves the original [`UnknownReason`].
    Incomplete(UnknownReason),
    /// A verify-before-return route ran and produced a candidate, but its own
    /// re-check rejected it (so the candidate was discarded, not returned).
    VerifierRejected(String),
}

impl DeclineReason {
    /// Maps an [`UnknownReason`] onto a [`DeclineReason`], routing the
    /// budget-style kinds to [`DeclineReason::Budget`] and the rest to
    /// [`DeclineReason::Incomplete`] (which preserves the full reason).
    #[must_use]
    pub fn from_unknown(reason: &UnknownReason) -> Self {
        match reason.kind {
            UnknownKind::Timeout
            | UnknownKind::ResourceLimit
            | UnknownKind::MemoryLimit
            | UnknownKind::NodeBudget
            | UnknownKind::EncodingBudget => DeclineReason::Budget(reason.detail.clone()),
            UnknownKind::Incomplete | UnknownKind::Other => {
                DeclineReason::Incomplete(reason.clone())
            }
        }
    }
}

impl core::fmt::Display for DeclineReason {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DeclineReason::Unsupported => write!(f, "unsupported"),
            DeclineReason::NotApplicable => write!(f, "not-applicable"),
            DeclineReason::Budget(detail) => write!(f, "budget: {detail}"),
            DeclineReason::Incomplete(reason) => {
                write!(f, "incomplete: {}", reason.detail)
            }
            DeclineReason::VerifierRejected(detail) => {
                write!(f, "verifier-rejected: {detail}")
            }
        }
    }
}

/// The outcome of a single recorded route attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RouteOutcome {
    /// The probe classification preamble (not a real route): records the
    /// detected fragment and the planned route ordering.
    Probe(String),
    /// The route decided the query.
    Decided(Verdict),
    /// The route declined; the query continued to the next route.
    Declined(DeclineReason),
}

impl core::fmt::Display for RouteOutcome {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RouteOutcome::Probe(detail) => write!(f, "{detail}"),
            RouteOutcome::Decided(Verdict::Sat) => write!(f, "decided sat"),
            RouteOutcome::Decided(Verdict::Unsat) => write!(f, "decided unsat"),
            RouteOutcome::Declined(reason) => write!(f, "declined ({reason})"),
        }
    }
}

/// One entry in a [`RouteTrace`]: a route label and what happened.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RouteAttempt {
    /// A stable, deterministic route label (a `&'static str`), e.g. `"qf-bv"`.
    pub route: &'static str,
    /// What the route did.
    pub outcome: RouteOutcome,
}

impl core::fmt::Display for RouteAttempt {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}: {}", self.route, self.outcome)
    }
}

/// An ordered record of the dispatch routes tried for one auto-solve, with the
/// decisive route (if any) last.
///
/// See the [module documentation](crate::route_trace) for the verdict-invariance
/// contract this telemetry upholds.
///
/// # Timing
///
/// Each recorded attempt also carries the wall-clock time elapsed since the
/// *previous* recorded attempt (or since the trace was created, for the
/// first) — see [`Self::elapsed`] / [`Self::total_elapsed`]. This is what
/// makes a declined route's cost visible: a route that ran for 20 of a 24 s
/// budget before giving up otherwise leaves no trace of where the time went.
///
/// Timing is **not** part of [`RouteTrace`]'s [`PartialEq`]/[`Eq`]: those
/// compare only the recorded `attempts` (route, outcome), never the elapsed
/// durations. Wall-clock time is inherently non-reproducible run to run, and
/// the determinism contract this module upholds (see the module docs, and
/// `tests/route_trace.rs::trace_is_deterministic_across_runs`) is about
/// dispatch *order and outcome*, not timing. Comparing two traces for
/// equality therefore still answers exactly the question it always did.
#[derive(Debug, Clone)]
pub struct RouteTrace {
    attempts: Vec<RouteAttempt>,
    /// Wall-clock elapsed per attempt, aligned by index with `attempts`.
    /// Deliberately excluded from `PartialEq`/`Eq` — see the struct docs.
    elapsed: Vec<Duration>,
    /// The instant the most recently recorded attempt was recorded (or the
    /// instant the trace was created, before any attempt exists). Used to
    /// compute the next `elapsed` entry.
    last: Instant,
}

impl Default for RouteTrace {
    fn default() -> Self {
        Self {
            attempts: Vec::new(),
            elapsed: Vec::new(),
            last: Instant::now(),
        }
    }
}

/// Structural equality: same recorded `(route, outcome)` sequence. Timing is
/// deliberately excluded — see the [`RouteTrace`] struct docs.
impl PartialEq for RouteTrace {
    fn eq(&self, other: &Self) -> bool {
        self.attempts == other.attempts
    }
}

impl Eq for RouteTrace {}

impl RouteTrace {
    /// An empty trace. Starts its elapsed-time clock now.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The recorded attempts, in dispatch order.
    #[must_use]
    pub fn attempts(&self) -> &[RouteAttempt] {
        &self.attempts
    }

    /// Wall-clock elapsed per recorded attempt, aligned by index with
    /// [`Self::attempts`]: `elapsed()[i]` is the time from the previous
    /// attempt's record call (or trace creation, for `i == 0`) to attempt
    /// `i`'s record call. Always the same length as `attempts`.
    #[must_use]
    pub fn elapsed(&self) -> &[Duration] {
        &self.elapsed
    }

    /// The sum of [`Self::elapsed`] — the total wall-clock time spent inside
    /// dispatch since the trace was created, across every recorded attempt.
    #[must_use]
    pub fn total_elapsed(&self) -> Duration {
        self.elapsed
            .iter()
            .copied()
            .fold(Duration::ZERO, |acc, d| acc + d)
    }

    /// Whether the trace recorded no attempts.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.attempts.is_empty()
    }

    /// The last recorded attempt, if any.
    #[must_use]
    pub fn last(&self) -> Option<&RouteAttempt> {
        self.attempts.last()
    }

    /// Records the wall-clock time since the previous record call (or trace
    /// creation) as the next `elapsed` entry. Called once per `record_*`
    /// method, immediately alongside the corresponding `attempts` push, so
    /// the two vectors stay aligned.
    fn tick(&mut self) {
        let now = Instant::now();
        self.elapsed.push(now.saturating_duration_since(self.last));
        self.last = now;
    }

    /// Records the probe preamble: the detected fragment and planned route
    /// ordering. Conventionally the first entry of a trace.
    pub fn record_probe(&mut self, detail: impl Into<String>) {
        self.attempts.push(RouteAttempt {
            route: "probe",
            outcome: RouteOutcome::Probe(detail.into()),
        });
        self.tick();
    }

    /// Records that `route` decided the query with `verdict`.
    pub fn record_decided(&mut self, route: &'static str, verdict: Verdict) {
        self.attempts.push(RouteAttempt {
            route,
            outcome: RouteOutcome::Decided(verdict),
        });
        self.tick();
    }

    /// Records that `route` declined for `reason`.
    pub fn record_declined(&mut self, route: &'static str, reason: DeclineReason) {
        self.attempts.push(RouteAttempt {
            route,
            outcome: RouteOutcome::Declined(reason),
        });
        self.tick();
    }

    /// Records the terminal outcome derived from a [`CheckResult`]: a `Decided`
    /// entry for `Sat`/`Unsat`, or a `Declined(Incomplete/Budget)` entry that
    /// preserves the `Unknown` reason. This is the single sink that closes a
    /// trace once a route's [`CheckResult`] is in hand, keeping the last entry
    /// consistent with the overall verdict.
    pub fn record_result(&mut self, route: &'static str, result: &CheckResult) {
        match result {
            CheckResult::Sat(_) => self.record_decided(route, Verdict::Sat),
            CheckResult::Unsat => self.record_decided(route, Verdict::Unsat),
            CheckResult::Unknown(reason) => {
                self.record_declined(route, DeclineReason::from_unknown(reason));
            }
        }
    }
}

impl core::fmt::Display for RouteTrace {
    /// Prints the ordered trail, one `route: outcome` per line.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for (i, attempt) in self.attempts.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(f, "{attempt}")?;
        }
        Ok(())
    }
}

/// Schema version of [`RouteTrace::to_json`]'s output. Bump on any field
/// rename/removal so a consumer can reject a rendering it does not understand.
pub const ROUTE_TRACE_JSON_SCHEMA_VERSION: u32 = 1;

/// Appends `value` to `out` as a JSON string literal, escaping per RFC 8259.
///
/// Non-ASCII scalar values pass through unescaped (they are already valid UTF-8
/// JSON); only `"`, `\`, and the C0 controls need transformation.
///
/// This is public so a consumer embedding [`RouteTrace::to_json`] inside a
/// larger artifact (a bench record, a JSONL line) escapes its *own* fields with
/// the same tested routine instead of hand-rolling a second one that drifts.
/// A subtly different escaper is how an artifact silently becomes invalid JSON.
pub fn push_json_string(out: &mut String, value: &str) {
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => {
                // `write!` into the buffer rather than allocating a temporary
                // `format!` string per control character.
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// The stable wire name of an [`UnknownKind`].
///
/// [`UnknownKind`] is `#[non_exhaustive]`, so the wildcard arm is required; an
/// unrecognised kind renders as `"other"` rather than failing, because this is
/// telemetry and must never be able to abort a solve.
fn unknown_kind_str(kind: UnknownKind) -> &'static str {
    match kind {
        UnknownKind::Timeout => "timeout",
        UnknownKind::ResourceLimit => "resource-limit",
        UnknownKind::MemoryLimit => "memory-limit",
        UnknownKind::NodeBudget => "node-budget",
        UnknownKind::EncodingBudget => "encoding-budget",
        UnknownKind::Incomplete => "incomplete",
        _ => "other",
    }
}

impl RouteTrace {
    /// Renders the trace as a single-line, deterministic JSON object.
    ///
    /// This is the persistence form consumed by `axeyum-bench` artifacts and by
    /// the bridge-catalogue replay validator, which needs the observed dispatch
    /// order as data rather than as `Display` prose.
    ///
    /// # Determinism
    ///
    /// The output is a pure function of the recorded attempts: field order is
    /// fixed by construction, attempts keep dispatch order, and no map is
    /// iterated. Two runs that record the same attempts render byte-identical
    /// text, which is what makes the rendering usable in a golden test.
    ///
    /// # Schema
    ///
    /// ```text
    /// {"schema_version":1,"attempts":[
    ///   {"route":"probe","outcome":"probe","detail":"…"},
    ///   {"route":"qf-bv","outcome":"decided","verdict":"unsat"},
    ///   {"route":"nra-real-root","outcome":"declined","reason":"not-applicable"},
    ///   {"route":"lia-simplex","outcome":"declined","reason":"budget","detail":"…"},
    ///   {"route":"euf-online","outcome":"declined","reason":"incomplete",
    ///    "kind":"incomplete","detail":"…"}
    /// ]}
    /// ```
    ///
    /// `detail` is present exactly when the variant carries one; `kind` only on
    /// `incomplete`, where it preserves the original [`UnknownKind`]
    /// classification.
    #[must_use]
    pub fn to_json(&self) -> String {
        self.render_json(false)
    }

    /// Renders the trace exactly like [`Self::to_json`], with one addition:
    /// each attempt object carries an extra `"elapsed_ns"` member giving that
    /// attempt's [`Self::elapsed`] entry as whole nanoseconds.
    ///
    /// This is the opt-in serializer the timing feature adds. [`Self::to_json`]
    /// is left byte-for-byte unchanged by design (see the `RouteTrace` struct
    /// docs and `tests/route_trace.rs`) precisely so every existing consumer —
    /// golden tests, committed bench artifacts, the bridge-catalogue replay
    /// validator — keeps parsing the schema it already expects. A caller that
    /// wants to see where a declined route's time went (`explain_corpus`,
    /// `smtcomp_cli`'s trace output) opts in explicitly by calling this method
    /// instead.
    ///
    /// # Schema
    ///
    /// ```text
    /// {"schema_version":1,"attempts":[
    ///   {"route":"probe","outcome":"probe","detail":"…","elapsed_ns":1200},
    ///   {"route":"qf-bv","outcome":"decided","verdict":"unsat","elapsed_ns":48200000}
    /// ]}
    /// ```
    #[must_use]
    pub fn to_json_with_timing(&self) -> String {
        self.render_json(true)
    }

    fn render_json(&self, include_timing: bool) -> String {
        let per_attempt_capacity = if include_timing { 96 } else { 64 };
        let mut out = String::with_capacity(64 + self.attempts.len() * per_attempt_capacity);
        out.push_str("{\"schema_version\":");
        out.push_str(&ROUTE_TRACE_JSON_SCHEMA_VERSION.to_string());
        out.push_str(",\"attempts\":[");
        for (i, attempt) in self.attempts.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            out.push_str("{\"route\":");
            push_json_string(&mut out, attempt.route);
            match &attempt.outcome {
                RouteOutcome::Probe(detail) => {
                    out.push_str(",\"outcome\":\"probe\",\"detail\":");
                    push_json_string(&mut out, detail);
                }
                RouteOutcome::Decided(verdict) => {
                    out.push_str(",\"outcome\":\"decided\",\"verdict\":");
                    push_json_string(
                        &mut out,
                        match verdict {
                            Verdict::Sat => "sat",
                            Verdict::Unsat => "unsat",
                        },
                    );
                }
                RouteOutcome::Declined(reason) => {
                    out.push_str(",\"outcome\":\"declined\",\"reason\":");
                    match reason {
                        DeclineReason::Unsupported => {
                            push_json_string(&mut out, "unsupported");
                        }
                        DeclineReason::NotApplicable => {
                            push_json_string(&mut out, "not-applicable");
                        }
                        DeclineReason::Budget(detail) => {
                            push_json_string(&mut out, "budget");
                            out.push_str(",\"detail\":");
                            push_json_string(&mut out, detail);
                        }
                        DeclineReason::Incomplete(unknown) => {
                            push_json_string(&mut out, "incomplete");
                            out.push_str(",\"kind\":");
                            push_json_string(&mut out, unknown_kind_str(unknown.kind));
                            out.push_str(",\"detail\":");
                            push_json_string(&mut out, &unknown.detail);
                        }
                        DeclineReason::VerifierRejected(detail) => {
                            push_json_string(&mut out, "verifier-rejected");
                            out.push_str(",\"detail\":");
                            push_json_string(&mut out, detail);
                        }
                    }
                }
            }
            if include_timing {
                out.push_str(",\"elapsed_ns\":");
                out.push_str(&self.elapsed[i].as_nanos().to_string());
            }
            out.push('}');
        }
        out.push_str("]}");
        out
    }
}

/// An optional route-trace recorder threaded through the dispatch.
///
/// The auto-dispatcher takes a `Recorder` so the *same* code path serves both
/// [`crate::check_auto`] (no recorder) and [`crate::check_auto_explained`] (a
/// recorder). The methods are no-ops when the recorder is absent, so threading
/// one in never changes a branch condition — the verdict-invariance guarantee.
pub(crate) type Recorder<'a> = Option<&'a mut RouteTrace>;

/// Records `f` against an optional recorder, doing nothing when absent.
pub(crate) fn with_recorder(rec: &mut Recorder<'_>, f: impl FnOnce(&mut RouteTrace)) {
    if let Some(trace) = rec.as_deref_mut() {
        f(trace);
    }
}

#[cfg(test)]
mod json_tests {
    use super::*;

    #[test]
    fn empty_trace_renders_an_empty_attempt_list() {
        assert_eq!(
            RouteTrace::new().to_json(),
            "{\"schema_version\":1,\"attempts\":[]}"
        );
    }

    #[test]
    fn every_outcome_variant_renders_its_documented_shape() {
        let mut trace = RouteTrace::new();
        trace.record_probe("bv");
        trace.record_declined("a", DeclineReason::Unsupported);
        trace.record_declined("b", DeclineReason::NotApplicable);
        trace.record_declined("c", DeclineReason::Budget("nodes".into()));
        trace.record_declined(
            "d",
            DeclineReason::Incomplete(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "nl".into(),
            }),
        );
        trace.record_declined("e", DeclineReason::VerifierRejected("replay".into()));
        trace.record_decided("f", Verdict::Unsat);
        assert_eq!(
            trace.to_json(),
            "{\"schema_version\":1,\"attempts\":[\
{\"route\":\"probe\",\"outcome\":\"probe\",\"detail\":\"bv\"},\
{\"route\":\"a\",\"outcome\":\"declined\",\"reason\":\"unsupported\"},\
{\"route\":\"b\",\"outcome\":\"declined\",\"reason\":\"not-applicable\"},\
{\"route\":\"c\",\"outcome\":\"declined\",\"reason\":\"budget\",\"detail\":\"nodes\"},\
{\"route\":\"d\",\"outcome\":\"declined\",\"reason\":\"incomplete\",\
\"kind\":\"incomplete\",\"detail\":\"nl\"},\
{\"route\":\"e\",\"outcome\":\"declined\",\"reason\":\"verifier-rejected\",\
\"detail\":\"replay\"},\
{\"route\":\"f\",\"outcome\":\"decided\",\"verdict\":\"unsat\"}]}"
        );
    }

    #[test]
    fn budget_kinds_map_onto_their_stable_wire_names() {
        for (kind, wire) in [
            (UnknownKind::Timeout, "timeout"),
            (UnknownKind::ResourceLimit, "resource-limit"),
            (UnknownKind::MemoryLimit, "memory-limit"),
            (UnknownKind::NodeBudget, "node-budget"),
            (UnknownKind::EncodingBudget, "encoding-budget"),
            (UnknownKind::Incomplete, "incomplete"),
            (UnknownKind::Other, "other"),
        ] {
            assert_eq!(unknown_kind_str(kind), wire);
        }
    }

    /// Detail strings are backend-supplied and can contain quotes, backslashes,
    /// and newlines; an unescaped render would emit invalid JSON and silently
    /// corrupt every downstream artifact that embeds a trace.
    #[test]
    fn detail_strings_are_json_escaped() {
        let mut trace = RouteTrace::new();
        trace.record_declined("x", DeclineReason::Budget("a\"b\\c\nd\te\u{1}f".into()));
        assert_eq!(
            trace.to_json(),
            "{\"schema_version\":1,\"attempts\":[{\"route\":\"x\",\
\"outcome\":\"declined\",\"reason\":\"budget\",\
\"detail\":\"a\\\"b\\\\c\\nd\\te\\u0001f\"}]}"
        );
    }

    #[test]
    fn rendering_is_byte_stable_and_preserves_dispatch_order() {
        let mut trace = RouteTrace::new();
        trace.record_probe("int");
        trace.record_declined("first", DeclineReason::Unsupported);
        trace.record_decided("second", Verdict::Sat);
        assert_eq!(trace.to_json(), trace.to_json());
        let rendered = trace.to_json();
        let first = rendered.find("first").expect("first route present");
        let second = rendered.find("second").expect("second route present");
        assert!(first < second, "attempts must keep dispatch order");
    }

    /// A declined route followed by a decided one records two elapsed values
    /// (one per attempt), and their sum equals the trace's total — the
    /// invariant that makes a declined route's cost visible instead of just
    /// its outcome.
    #[test]
    fn declined_then_decided_carries_two_elapsed_values_summing_to_total() {
        let mut trace = RouteTrace::new();
        trace.record_declined("a", DeclineReason::Unsupported);
        std::thread::sleep(Duration::from_millis(2));
        trace.record_decided("b", Verdict::Sat);

        let elapsed = trace.elapsed();
        assert_eq!(elapsed.len(), 2, "one elapsed entry per attempt");
        assert_eq!(elapsed.len(), trace.attempts().len());

        let summed = elapsed.iter().copied().fold(Duration::ZERO, |a, d| a + d);
        assert_eq!(summed, trace.total_elapsed());

        // The sleep between the two records means the second attempt's
        // elapsed dominates and is observably nonzero.
        assert!(
            elapsed[1] >= Duration::from_millis(1),
            "declined route's cost must be visible: elapsed[1]={:?}",
            elapsed[1]
        );
    }

    /// Adding per-attempt timing must not change [`RouteTrace::to_json`]'s
    /// output: it is pinned against the same literal
    /// [`every_outcome_variant_renders_its_documented_shape`] already checks,
    /// built the identical way. Timing is opt-in via
    /// [`RouteTrace::to_json_with_timing`] only.
    #[test]
    fn default_to_json_is_unchanged_by_timing_support() {
        let mut trace = RouteTrace::new();
        trace.record_probe("bv");
        trace.record_declined("a", DeclineReason::Unsupported);
        trace.record_declined("b", DeclineReason::NotApplicable);
        trace.record_declined("c", DeclineReason::Budget("nodes".into()));
        trace.record_declined(
            "d",
            DeclineReason::Incomplete(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "nl".into(),
            }),
        );
        trace.record_declined("e", DeclineReason::VerifierRejected("replay".into()));
        trace.record_decided("f", Verdict::Unsat);
        assert_eq!(
            trace.to_json(),
            "{\"schema_version\":1,\"attempts\":[\
{\"route\":\"probe\",\"outcome\":\"probe\",\"detail\":\"bv\"},\
{\"route\":\"a\",\"outcome\":\"declined\",\"reason\":\"unsupported\"},\
{\"route\":\"b\",\"outcome\":\"declined\",\"reason\":\"not-applicable\"},\
{\"route\":\"c\",\"outcome\":\"declined\",\"reason\":\"budget\",\"detail\":\"nodes\"},\
{\"route\":\"d\",\"outcome\":\"declined\",\"reason\":\"incomplete\",\
\"kind\":\"incomplete\",\"detail\":\"nl\"},\
{\"route\":\"e\",\"outcome\":\"declined\",\"reason\":\"verifier-rejected\",\
\"detail\":\"replay\"},\
{\"route\":\"f\",\"outcome\":\"decided\",\"verdict\":\"unsat\"}]}",
            "to_json must stay byte-identical once timing support lands"
        );
    }

    /// The opt-in timed serializer adds `elapsed_ns` per attempt and nothing
    /// else: same route/outcome content as `to_json`, one extra member.
    #[test]
    fn to_json_with_timing_adds_elapsed_ns_per_attempt_only() {
        let mut trace = RouteTrace::new();
        trace.record_declined("a", DeclineReason::Unsupported);
        trace.record_decided("b", Verdict::Sat);

        let plain = trace.to_json();
        let timed = trace.to_json_with_timing();
        assert_ne!(plain, timed, "timed rendering must differ from the default");
        assert_eq!(
            timed.matches("\"elapsed_ns\":").count(),
            2,
            "one elapsed_ns member per attempt"
        );
        // Stripping every `,"elapsed_ns":<digits>` from the timed rendering
        // must recover the plain rendering exactly.
        let mut stripped = String::new();
        let mut rest = timed.as_str();
        while let Some(pos) = rest.find(",\"elapsed_ns\":") {
            stripped.push_str(&rest[..pos]);
            rest = &rest[pos + ",\"elapsed_ns\":".len()..];
            let digits_end = rest
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len());
            rest = &rest[digits_end..];
        }
        stripped.push_str(rest);
        assert_eq!(stripped, plain);
    }

    #[test]
    fn route_trace_equality_ignores_timing() {
        let mut a = RouteTrace::new();
        a.record_decided("x", Verdict::Sat);
        std::thread::sleep(Duration::from_millis(2));
        let mut b = RouteTrace::new();
        b.record_decided("x", Verdict::Sat);

        // Real wall-clock elapsed will differ between the two traces, but
        // structural equality (route/outcome only) must still hold.
        assert_ne!(a.elapsed()[0], b.elapsed()[0]);
        assert_eq!(a, b, "RouteTrace equality must ignore timing");
    }
}
