//! Does an `unknown` say **why**?
//!
//! # The defect this gate exists for
//!
//! Measured 2026-09-11 over the 81 files `bench-results/parity-details/QF_DT.tsv`
//! records as unsolved by us and decided by the reference — the whole
//! addressable `QF_DT` gap — the shipped competition CLI printed a reason for
//! **11**. The other 70 printed the bare word `unknown` with a route trail
//! holding one entry: the unconditional `fd:parse` *probe*, which says the
//! ingest stage RAN and never that anything refused.
//!
//! The cause was not a missing reason. Every one of those files produced a
//! `SolverError::Unsupported` naming the exact construct, and `datatype-elim`
//! had recorded a decline before it — and then two separate places threw both
//! away:
//!
//! 1. `check_auto_explained` reached the dispatch through `?`, so an error
//!    destroyed the `RouteTrace` it had just filled in; and `check_auto`
//!    absorbed that trace with `Result::inspect`, which does not run on `Err`.
//! 2. The CLI's `Err(_) => "unknown"` arm discarded the error itself.
//!
//! So the reason existed at three points and reached none of them. These tests
//! pin the repairs at the layer where each belongs.
//!
//! # Why each assertion can fail
//!
//! Per this repository's checker discipline, a checker whose exit status does
//! not depend on its finding is worse than none. `a_decided_query_records_no_
//! dispatch_error` is the control that stops the others passing vacuously: if
//! the recording were wired to fire on every query it would still satisfy
//! "an errored dispatch records something".
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{
    DeclineReason, RouteAttributionGuard, RouteOutcome, SolverConfig, last_route_attribution,
    solve_smtlib,
};

/// A `QF_DT` script in the shape of the Barrett/Reynolds family that is 70 of
/// the 81 addressable-gap files: mutually recursive datatypes with an `is-c`
/// tester applied to a **selector application** rather than a variable.
///
/// Trimmed from
/// `smtlib-2024/.../QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l20044.cvc.smt2`
/// and kept inline rather than pointed at the corpus, so the gate does not
/// depend on a `/nas3` mount that most hosts do not have.
const DISPATCH_ERROR_SCRIPT: &str = r"
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
((cons (car tree) (cdr list)) (null))
((node (children list)) (leaf (data nat)))
))
(declare-fun x1 () nat)
(assert (and ((_ is succ) (pred zero)) (not (= zero (pred x1)))))
(check-sat)
";

/// A script the dispatch decides outright — the control population.
const DECIDED_SCRIPT: &str = r"
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 3))
(assert (< x 2))
(check-sat)
";

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_millis(5_000)),
        ..SolverConfig::default()
    }
}

/// Every `Declined` entry in the current attribution, as `(route, rendered)`.
fn declines() -> Vec<(String, String)> {
    last_route_attribution()
        .attempts()
        .iter()
        .filter_map(|a| match &a.outcome {
            RouteOutcome::Declined(reason) => Some((a.route.to_owned(), reason.to_string())),
            _ => None,
        })
        .collect()
}

#[test]
fn an_errored_dispatch_publishes_the_routes_that_ran_and_the_error_text() {
    let _guard = RouteAttributionGuard::enable();
    let outcome = solve_smtlib(DISPATCH_ERROR_SCRIPT, &config());
    assert!(
        outcome.is_err(),
        "this fixture exists because the dispatch ERRORS on it; if it now \
         decides, the fixture has stopped covering the path and must be \
         replaced, not deleted: {outcome:?}"
    );
    let declines = declines();
    assert!(
        !declines.is_empty(),
        "an errored dispatch published NO declined route at all — the whole \
         defect. attribution: {:?}",
        last_route_attribution().attempts()
    );
    let (route, rendered) = declines
        .iter()
        .find(|(route, _)| route == "dispatch-error")
        .unwrap_or_else(|| {
            panic!("no terminal `dispatch-error` entry; declines were {declines:?}")
        });
    assert_eq!(route, "dispatch-error");
    assert!(
        rendered.len() > "unsupported: ".len(),
        "the terminal entry must carry the error's OWN text, not an empty \
         placeholder: {rendered:?}"
    );
    // Derived, not invented: the rendered reason has to be a substring-carrier
    // of the error the front door actually returned.
    let error = outcome.unwrap_err().to_string();
    let inner = error.rsplit(": ").next().unwrap_or(&error);
    assert!(
        rendered.contains(inner),
        "the recorded reason must be the error's own words.\n  error:    {error}\n  recorded: {rendered}"
    );
}

/// The control. If `dispatch-error` were recorded unconditionally — the
/// cheapest way to make the test above pass — this one dies.
#[test]
fn a_decided_query_records_no_dispatch_error() {
    let _guard = RouteAttributionGuard::enable();
    let outcome = solve_smtlib(DECIDED_SCRIPT, &config());
    assert!(outcome.is_ok(), "control fixture must decide: {outcome:?}");
    let declines = declines();
    assert!(
        !declines.iter().any(|(route, _)| route == "dispatch-error"),
        "a query that did not error must not carry a dispatch-error entry: {declines:?}"
    );
}

/// Turning the attribution on must not change the answer — the one
/// load-bearing invariant of the whole telemetry, re-asserted on the error
/// path specifically because that path now does more work than it did.
#[test]
fn publishing_an_errored_dispatch_does_not_change_the_answer() {
    let without = format!("{:?}", solve_smtlib(DISPATCH_ERROR_SCRIPT, &config()));
    let with = {
        let _guard = RouteAttributionGuard::enable();
        format!("{:?}", solve_smtlib(DISPATCH_ERROR_SCRIPT, &config()))
    };
    assert_eq!(
        without, with,
        "the recorder must be a pure side effect on the error path too"
    );
}

/// A route that declined with a message in hand must record the message.
///
/// Eleven `auto.rs` sites bound a `SolverError::Unsupported` payload to `_` and
/// recorded the payload-free `DeclineReason::Unsupported`. On this fixture the
/// `datatype-elim` rung is one of them, so a regression there is visible as a
/// decline that renders as the bare word.
#[test]
fn an_unsupported_decline_carries_the_refusing_calls_message() {
    let _guard = RouteAttributionGuard::enable();
    let _ = solve_smtlib(DISPATCH_ERROR_SCRIPT, &config());
    let declines = declines();
    let bare: Vec<_> = declines
        .iter()
        .filter(|(_, rendered)| rendered == "unsupported")
        .collect();
    assert!(
        bare.is_empty(),
        "these routes declined as `Unsupported` with nothing after it; the \
         refusing call's message was in hand and was dropped: {bare:?}\n\
         (full decline list: {declines:?})"
    );
    assert!(
        declines
            .iter()
            .any(|(_, rendered)| rendered.starts_with("unsupported: ")),
        "positive control: this fixture MUST produce at least one message-carrying \
         `unsupported` decline, or the emptiness above proves nothing. \
         declines: {declines:?}"
    );
}

/// A script the parser cannot read is refused at ingest, and the trail's only
/// `fd:parse` entry was the unconditional *probe* — which records that the
/// stage RAN and never that it refused. A reader could not tell an ingest
/// refusal from a parse that succeeded and handed a route the work.
#[test]
fn an_ingest_refusal_is_recorded_against_fd_parse() {
    let _guard = RouteAttributionGuard::enable();
    let outcome = solve_smtlib("(assert (", &config());
    assert!(
        outcome.is_err(),
        "this fixture exists because ingest REFUSES it: {outcome:?}"
    );
    let parse: Vec<_> = last_route_attribution()
        .attempts()
        .iter()
        .filter(|a| a.route == "fd:parse")
        .map(|a| format!("{}", a.outcome))
        .collect();
    assert!(
        parse.iter().any(|o| o.starts_with("declined")),
        "`fd:parse` must record a DECLINE, not only its probe: {parse:?}"
    );
    assert!(
        parse
            .iter()
            .any(|o| o.starts_with("declined (unsupported: ") && o.len() > 30),
        "the decline must carry the parser's own message: {parse:?}"
    );
}

/// The control for the test above: a script that parses records the probe and
/// **no** `fd:parse` decline. Without this, recording a decline on every file
/// would pass.
#[test]
fn a_parseable_script_records_no_fd_parse_decline() {
    let _guard = RouteAttributionGuard::enable();
    let outcome = solve_smtlib(DECIDED_SCRIPT, &config());
    assert!(outcome.is_ok(), "control fixture must parse: {outcome:?}");
    let trace = last_route_attribution();
    let declined: Vec<_> = trace
        .attempts()
        .iter()
        .filter(|a| a.route == "fd:parse" && matches!(a.outcome, RouteOutcome::Declined(_)))
        .map(|a| a.route)
        .collect();
    assert!(
        declined.is_empty(),
        "a script that parsed must not carry an ingest refusal: {declined:?}"
    );
}

/// The shape [`DeclineReason::UnsupportedDetail`] exists to make countable:
/// two declines that are the same *kind* but not the same *information*.
#[test]
fn the_two_unsupported_forms_are_distinguishable() {
    assert_ne!(
        DeclineReason::Unsupported.to_string(),
        DeclineReason::UnsupportedDetail("why".to_owned()).to_string(),
        "collapsing these two renders a reasoned decline as a placeholder"
    );
}
