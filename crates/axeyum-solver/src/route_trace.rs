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
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RouteTrace {
    attempts: Vec<RouteAttempt>,
}

impl RouteTrace {
    /// An empty trace.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The recorded attempts, in dispatch order.
    #[must_use]
    pub fn attempts(&self) -> &[RouteAttempt] {
        &self.attempts
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

    /// Records the probe preamble: the detected fragment and planned route
    /// ordering. Conventionally the first entry of a trace.
    pub fn record_probe(&mut self, detail: impl Into<String>) {
        self.attempts.push(RouteAttempt {
            route: "probe",
            outcome: RouteOutcome::Probe(detail.into()),
        });
    }

    /// Records that `route` decided the query with `verdict`.
    pub fn record_decided(&mut self, route: &'static str, verdict: Verdict) {
        self.attempts.push(RouteAttempt {
            route,
            outcome: RouteOutcome::Decided(verdict),
        });
    }

    /// Records that `route` declined for `reason`.
    pub fn record_declined(&mut self, route: &'static str, reason: DeclineReason) {
        self.attempts.push(RouteAttempt {
            route,
            outcome: RouteOutcome::Declined(reason),
        });
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
