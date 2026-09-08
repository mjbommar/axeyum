//! Front-door route attribution (ADR-1760): verdict invariance, coverage, and
//! the separability of "which route decided" from "which route bound".
//!
//! # What this gate is for
//!
//! `route_trace.rs`'s telemetry was only reachable through
//! `check_auto_explained`, which decides the *flat assertion view*. The shipped
//! front door (`solve_smtlib`) runs a word-only fallback, an FP prefix fold, a
//! source-level string ladder, a `StringGate`, and seven post-dispatch second
//! chances **outside** `check_auto`, any of which can supply the verdict. That
//! is why `explain_corpus` disagrees with the front door on 134 of 397
//! benchmarks — so an answer read off the diagnostic path does not transfer.
//!
//! `RouteAttributionGuard` makes the attribution available from the front door
//! itself. The non-negotiable property is that turning it on changes **no**
//! verdict, and that is asserted here directly over the committed regression
//! corpus rather than argued from the structure of the code.
//!
//! # Why the assertions fail loudly rather than warn
//!
//! Per this repository's checker discipline: a checker whose exit status does
//! not depend on its finding is worse than no checker. Every check below
//! `assert!`s, and `attribution_is_not_vacuous` exists specifically so that a
//! guard which silently stopped recording anything cannot leave the other tests
//! green — an all-empty trace satisfies "no verdict changed" perfectly.
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::time::Duration;

use axeyum_solver::{
    CheckResult, RouteAttributionGuard, RouteOutcome, RouteTrace, SolverConfig,
    last_route_attribution, solve_smtlib,
};

/// A per-file wall budget small enough to keep the suite quick but large enough
/// that most corpus files decide. Files that hit it come back `unknown`, which
/// is a first-class result and still exercises the undecided-attribution path.
const BUDGET: Duration = Duration::from_millis(3_000);

fn corpus_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/regression")
}

/// Recursively collect `*.smt2` files under `dir`, sorted for determinism.
fn collect_smt2(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    paths.sort();
    for p in paths {
        if p.is_dir() {
            collect_smt2(&p, out);
        } else if p.extension().is_some_and(|e| e == "smt2") {
            out.push(p);
        }
    }
}

fn corpus_files() -> Vec<PathBuf> {
    let root = corpus_root();
    assert!(
        root.is_dir(),
        "regression corpus missing at {}",
        root.display()
    );
    let mut files = Vec::new();
    collect_smt2(&root, &mut files);
    assert!(
        files.len() >= 100,
        "expected the committed regression corpus (>=100 files), found {} — \
         a shrunken population would make every assertion below weaker without \
         failing",
        files.len()
    );
    files
}

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(BUDGET),
        ..SolverConfig::default()
    }
}

/// The verdict as a comparable tag. Models are deliberately NOT compared: two
/// runs of a `sat` may legitimately return different witnesses, and this gate
/// is about the sat/unsat/unknown answer, which is what a harness records.
fn tag(result: &Result<axeyum_solver::SmtLibOutcome, axeyum_solver::SolverError>) -> &'static str {
    match result {
        Ok(o) => match o.result {
            CheckResult::Sat(_) => "sat",
            CheckResult::Unsat => "unsat",
            CheckResult::Unknown(_) => "unknown",
        },
        Err(_) => "error",
    }
}

/// Solves `text` once with attribution off and once with it on, returning the
/// two verdict tags and the trace collected on the second run.
fn solve_both(text: &str) -> (&'static str, &'static str, RouteTrace) {
    let cfg = config();
    let plain = tag(&solve_smtlib(text, &cfg));
    let (attributed, trace) = {
        let guard = RouteAttributionGuard::enable();
        let t = tag(&solve_smtlib(text, &cfg));
        drop(guard);
        (t, last_route_attribution())
    };
    (plain, attributed, trace)
}

/// THE non-negotiable property: enabling attribution changes no verdict.
#[test]
fn attribution_does_not_change_any_verdict() {
    let files = corpus_files();
    let mut mismatches = Vec::new();
    let mut checked = 0usize;
    for path in &files {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        checked += 1;
        let (plain, attributed, _) = solve_both(&text);
        if plain != attributed {
            mismatches.push(format!("{}: off={plain} on={attributed}", path.display()));
        }
    }
    assert!(
        checked >= 100,
        "only {checked} files were actually read and solved — a gate that \
         examines nothing exits 0"
    );
    assert!(
        mismatches.is_empty(),
        "route attribution changed {} verdict(s), which it must never do:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
    eprintln!("verdict invariance: {checked} files, 0 mismatches");
}

/// The anti-vacuity guard. "No verdict changed" is satisfied perfectly by an
/// instrument that records nothing at all, so the invariance test above cannot
/// detect a collector that silently went dead. This one fails if it does.
#[test]
fn attribution_is_not_vacuous() {
    let files = corpus_files();
    let mut with_attempts = 0usize;
    let mut with_decider = 0usize;
    let mut distinct_routes = std::collections::BTreeSet::new();
    let mut checked = 0usize;
    for path in &files {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        checked += 1;
        let (_, _, trace) = solve_both(&text);
        if !trace.is_empty() {
            with_attempts += 1;
        }
        for a in trace.attempts() {
            distinct_routes.insert(a.route);
        }
        if trace.decided_by().is_some() {
            with_decider += 1;
        }
    }
    // Every front-door call parses, and parse is a recorded stage, so a file
    // that produced no attempts at all means collection did not reach the front
    // door.
    assert_eq!(
        with_attempts,
        checked,
        "{} of {checked} files recorded no attribution at all",
        checked - with_attempts
    );
    // The corpus is overwhelmingly decidable at this budget; if almost nothing
    // has a deciding route, `decided_by` is broken rather than the solver.
    assert!(
        with_decider * 2 > checked,
        "only {with_decider} of {checked} decided files named a deciding route"
    );
    // A single route label everywhere would mean the labels carry no
    // information — the exact failure mode of a dispatch table that cannot
    // fail to "produce".
    assert!(
        distinct_routes.len() >= 5,
        "attribution used only {} distinct route labels ({:?}) — that is a \
         constant, not a measurement",
        distinct_routes.len(),
        distinct_routes
    );
    eprintln!(
        "coverage: {checked} files, {with_decider} with a deciding route, \
         {} distinct route labels",
        distinct_routes.len()
    );
}

/// Attribution collected with the guard OFF must be empty — otherwise the
/// shipping path is paying for telemetry nobody asked for.
#[test]
fn nothing_is_recorded_with_the_guard_off() {
    let text = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
                (assert (= x (_ bv3 8)))\n(check-sat)\n";
    // A guard on a *previous* solve must not leak into this one.
    {
        let _g = RouteAttributionGuard::enable();
        let _ = solve_smtlib(text, &config());
    }
    let before = last_route_attribution();
    assert!(
        !before.is_empty(),
        "the guarded control solve recorded nothing, so this test's negative \
         result would be meaningless"
    );

    // Now solve unguarded and confirm the accumulator did not grow.
    let _ = solve_smtlib(text, &config());
    let after = last_route_attribution();
    assert_eq!(
        after.attempts().len(),
        before.attempts().len(),
        "an unguarded solve appended {} attempt(s) to the attribution",
        after.attempts().len() - before.attempts().len()
    );
}

/// The second question this instrument exists to answer: "which route bound
/// the query" must be *derivable and distinct* from "which route spoke last".
///
/// This asserts the mechanism on a constructed trace rather than hoping a
/// corpus file exhibits it — the property is that `bound_by` reads the timing
/// and `last` reads the position, so they can disagree. A test that only
/// checked corpus files would pass vacuously on a corpus where they happen to
/// coincide.
#[test]
fn bound_by_is_separable_from_printed_last() {
    let mut trace = RouteTrace::new();
    // An expensive route that declined, then a cheap one that declined after
    // it: exactly the shape that made a 403-file census wrong on 67 of 70.
    trace.record_declined("expensive", axeyum_solver::DeclineReason::NotApplicable);
    std::thread::sleep(Duration::from_millis(25));
    trace.record_declined("cheap-last", axeyum_solver::DeclineReason::Unsupported);

    let (_, last, _) = (0, trace.last().unwrap(), 0);
    let (_, bound, bound_ms) = trace
        .bound_by()
        .expect("a non-empty trace has a binding route");
    assert_eq!(last.route, "cheap-last", "the last entry is positional");
    assert_eq!(
        bound.route, "cheap-last",
        "the binding route is the most EXPENSIVE segment; here the sleep is \
         charged to the segment that ends after it"
    );
    assert!(bound_ms >= Duration::from_millis(20));

    // Now the reverse ordering: sleep BEFORE the first record, so the expensive
    // segment is the first entry and the last entry is cheap. `bound_by` must
    // now name a different route from `last`, which is the whole point.
    let mut trace = RouteTrace::new();
    std::thread::sleep(Duration::from_millis(25));
    trace.record_declined(
        "expensive-first",
        axeyum_solver::DeclineReason::NotApplicable,
    );
    trace.record_declined("cheap-last", axeyum_solver::DeclineReason::Unsupported);
    let last = trace.last().unwrap().route;
    let (_, bound, _) = trace.bound_by().unwrap();
    assert_eq!(last, "cheap-last");
    assert_eq!(bound.route, "expensive-first");
    assert_ne!(
        bound.route, last,
        "bound_by and last must be able to differ — if they cannot, this \
         instrument answers only the question that has already been wrong"
    );
}

/// `decided_by` must agree with the verdict actually returned: a decided file
/// names a decisive route, and an `unknown` names none.
#[test]
fn decided_by_agrees_with_the_returned_verdict() {
    let files = corpus_files();
    let mut disagreements = Vec::new();
    let mut checked = 0usize;
    for path in &files {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        checked += 1;
        let (_, attributed, trace) = solve_both(&text);
        // The one inconsistency worth failing on: the file was DECIDED but no
        // route in the trail claimed the decision, which means the instrument
        // has a hole where a verdict came from.
        //
        // The converse — an `unknown` whose trail does contain a decide — is
        // deliberately NOT a failure. It is the legitimate shape of a query
        // where an inner round decided a sub-problem and a later stage then
        // declined the file as a whole (measured on the UFLIA re-dispatch case
        // in `nested_dispatch_does_not_flood_the_attribution`).
        if matches!(attributed, "sat" | "unsat") && trace.decided_by().is_none() {
            disagreements.push(format!(
                "{}: verdict={attributed} but no deciding route",
                path.display()
            ));
        }
    }
    assert!(checked >= 100, "only {checked} files examined");
    assert!(
        disagreements.is_empty(),
        "{} file(s) were decided with no route claiming the decision:\n{}",
        disagreements.len(),
        disagreements.join("\n")
    );
}

/// Nested `check_auto` calls (a route solving a sub-query) must not be folded
/// into the top-level attribution: without the depth guard a file's trail is
/// dominated by whichever route recursed the most, and "which route decided
/// this file" becomes unanswerable.
#[test]
fn nested_dispatch_does_not_flood_the_attribution() {
    // A quantified UF query drives instantiation, which calls `check_auto`
    // recursively on each instance.
    let text = "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n\
                (assert (forall ((x Int)) (> (f x) 0)))\n\
                (assert (< (f 1) 0))\n(check-sat)\n";
    let guard = RouteAttributionGuard::enable();
    let _ = solve_smtlib(text, &config());
    drop(guard);
    let trace = last_route_attribution();
    assert!(!trace.is_empty(), "no attribution recorded");
    // The exact count depends on the dispatch ladder, but a runaway nested
    // recorder produces hundreds to thousands of entries for this query. A
    // generous ceiling still fails loudly if the depth guard is removed.
    assert!(
        trace.attempts().len() < 200,
        "attribution recorded {} attempts for one query — nested dispatch is \
         leaking into the top-level trail",
        trace.attempts().len()
    );
    // `check_auto_explained` records one `probe` preamble per dispatch, so the
    // probe count is the number of TOP-LEVEL dispatches this front-door call
    // made.
    //
    // More than one is legitimate and was measured: this very query records
    // four. The quantifier loop that sits *above* `check_auto` re-dispatches
    // the whole query once per instantiation round (three rounds where
    // `uf-arithmetic` decided the candidate `sat`, then a final round where
    // `lia-dpll` decided `unsat`). Those are separate top-level decisions, not
    // recursion inside one — recording them is the point, since the LAST of
    // them is the one whose verdict is returned.
    //
    // What must not happen is the guard failing open, which turns every nested
    // sub-solve made *inside* a dispatch into a top-level entry and produces
    // probe counts in the hundreds. The ceiling is set to catch that, not to
    // pin the round count, which is a property of the quantifier loop and would
    // make this test fail for an unrelated reason.
    let probes = trace
        .attempts()
        .iter()
        .filter(|a| matches!(a.outcome, RouteOutcome::Probe(_)) && a.route == "probe")
        .count();
    assert!(
        (1..=32).contains(&probes),
        "{probes} dispatch probes recorded for one front-door call; expected a \
         handful (one per instantiation round). Zero means nothing was \
         recorded; a large number means the outermost-dispatch guard is failing \
         open and nested sub-solves are being promoted to top-level entries."
    );
    // The trail's last DECIDED entry must be the one whose verdict came back,
    // which is exactly what makes `decided_by` usable on a re-dispatching query
    // like this one: three earlier rounds decided `sat` and were superseded.
    let outcome = solve_smtlib(text, &config()).expect("query solves");
    let (_, decided, _) = trace
        .decided_by()
        .expect("a decided query names a deciding route");
    match outcome.result {
        CheckResult::Unsat => assert!(
            matches!(
                decided.outcome,
                RouteOutcome::Decided(axeyum_solver::Verdict::Unsat)
            ),
            "verdict was unsat but decided_by names {decided}"
        ),
        CheckResult::Sat(_) => assert!(
            matches!(
                decided.outcome,
                RouteOutcome::Decided(axeyum_solver::Verdict::Sat)
            ),
            "verdict was sat but decided_by names {decided}"
        ),
        CheckResult::Unknown(_) => {}
    }
}
