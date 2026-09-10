//! A DEFINITE verdict that arrives after its deadline is KEPT, not discarded
//! (ADR-1906, roadmap item 3.9).
//!
//! Two gates used to throw away an answer the search had already computed —
//! `sat_bv_backend.rs`'s post-search clock re-read and `combined.rs`'s
//! post-backend one — and they sit **in series** on the `QF_BV` front door, so a
//! test that exercised only one would have passed while the shipped route stayed
//! broken. Both are covered here, by DIFFERENT mechanisms, for exactly that
//! reason. The measurement is
//! `docs/research/03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md`
//! and the per-route safety argument is
//! `docs/research/03-measurements/late-result-keep-safety-2026-09-10.md`.
//!
//! # Why the instance here is a wide MULTIPLY and not the `ndist.b` shape
//!
//! The measurement that motivated the keep used the `pspace/ndist.b` family, but
//! that family can no longer produce a late result on demand: the same change
//! set gave the CDCL core an ITERATION cadence for its deadline, and `ndist.b`
//! runs plenty of search-loop iterations, so it is now cut off AT the budget and
//! honestly reports `unknown`. Measured: width 12,288 went from returning at
//! 11.1 s against a 10 s budget to returning at 10.075 s.
//!
//! A wide `bvmul` is the opposite shape and is what keeps the gate reachable:
//! it is **encoding-bound with a short search** (~47% of its wall clock is
//! bit-blasting plus CNF construction, and its search runs FEWER than the 1,024
//! iterations the cadence needs to fire even once). So its search cannot be
//! interrupted, and a budget placed between "encoding done" and "search done"
//! produces a decided verdict past the deadline every time. Measured on the
//! committed corpus at width 512: a 700 ms budget returns `sat` at 1,034 ms
//! (551 ms encode, 441 ms search).
//!
//! # Why these tests calibrate before they assert
//!
//! A fixed millisecond budget cannot straddle both the debug and the release
//! profile (this gate runs in debug; the notes measure release), and a budget
//! that is too small trips the *pre*-solve gate instead — a different code path,
//! so the test would pass or fail for a reason unrelated to its subject. The
//! backend test therefore solves once with **no** deadline, reads the real
//! encode and search costs out of `SolveStats`, and derives a budget that
//! provably lands between them. Every run also asserts that it **actually
//! overran**, because a run that finished inside its budget never reaches the
//! gate and would pass vacuously.
#![cfg(feature = "full")]

use std::time::{Duration, Instant};

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{
    Capabilities, CheckResult, SatBvBackend, SolveStats, SolverBackend, SolverConfig, SolverError,
    UnknownKind, check_with_all_theories,
};

/// A single wide multiply constrained to a constant product — the `bvwide-mul`
/// shape from `corpus/public-curated/synthetic/QF_BV/width-graduated/`.
///
/// Encoding is ~`w²` gates while the search is short, which is the property this
/// suite needs (see the module docs).
fn wide_mul(width: u32) -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", width).expect("x");
    let y = arena.bv_var("y", width).expect("y");
    let product = arena.bv_mul(x, y).expect("bvmul");
    let target = arena.bv_const(width, 15).expect("target");
    let eq = arena.eq(product, target).expect("eq");
    (arena, vec![eq])
}

/// Width for the calibrated test. Wide enough that encoding and search are both
/// measurable in a debug build, narrow enough that two solves stay cheap.
const WIDTH: u32 = 192;

/// What one un-deadlined solve cost, and the budget derived from it.
struct Calibration {
    /// Encode cost (bit-blast + CNF construction), from `SolveStats::translate`.
    translate: Duration,
    /// Total wall clock of the un-deadlined solve.
    total: Duration,
    /// A budget that lands strictly between the two: past the encoding, so the
    /// PRE-solve gate cannot fire, and inside the search, so the deadline passes
    /// while a verdict is still being produced.
    budget: Duration,
}

/// Solves the instance with no deadline at all, confirms it is `sat`, and
/// derives the budget the deadlined run will use.
fn calibrate() -> Calibration {
    let (arena, assertions) = wide_mul(WIDTH);
    let mut backend = SatBvBackend::new();
    let started = Instant::now();
    let result = backend
        .check(&arena, &assertions, &SolverConfig::default())
        .expect("backend invocation succeeds");
    let total = started.elapsed();
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "calibration must decide the instance with no deadline; got {result:?}"
    );
    let stats = backend
        .last_stats()
        .expect("a completed check publishes stats");
    let translate = stats.translate;

    // Half way between "encoding finished" and "search finished". Far enough
    // past the encode that a slower second run still clears the pre-solve gate,
    // far enough short of the end that the deadline is genuinely crossed.
    let search = total.saturating_sub(translate);
    let budget = translate + search / 2;

    // A calibration that cannot produce a usable budget is a FAILURE, not a
    // reason to skip: a skipped test is one that cannot fail.
    assert!(
        budget > translate && budget < total && !search.is_zero(),
        "calibration produced an unusable budget: translate={translate:?} \
         total={total:?} search={search:?} budget={budget:?} — this test needs \
         an instance whose encode and search are both measurable at width {WIDTH}"
    );
    Calibration {
        translate,
        total,
        budget,
    }
}

/// Route 1 of 2: the cold `SatBvBackend` directly — the gate the measurement
/// named, `sat_bv_backend.rs`'s post-SAT-search clock re-read.
#[test]
fn a_sat_decided_past_the_deadline_survives_the_backend_gate() {
    let cal = calibrate();
    let (arena, assertions) = wide_mul(WIDTH);
    let config = SolverConfig::default().with_timeout(cal.budget);
    let started = Instant::now();
    let result = SatBvBackend::new()
        .check(&arena, &assertions, &config)
        .expect("backend invocation succeeds");
    let elapsed = started.elapsed();

    assert!(
        elapsed > cal.budget,
        "the backend run finished INSIDE its budget ({elapsed:?} <= {:?}), so the \
         post-search deadline gate was never reached and the assertion below \
         proves nothing. Calibration: translate={:?} total={:?}",
        cal.budget,
        cal.translate,
        cal.total
    );
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "the search completed and produced a model; the budget expiring DURING \
         the search that produced it must not discard the verdict. Got {result:?} \
         after {elapsed:?} against a {:?} budget",
        cal.budget
    );
}

/// A backend that decides correctly but always answers LATE.
///
/// It delegates to a real `SatBvBackend` with the caller's deadline stripped —
/// so the model it returns is a genuine, replayable one — and then sleeps until
/// the caller's budget is provably gone. That makes `combined.rs`'s gate
/// reachable with no timing race at all: the result is definite and the clock
/// has definitely passed, on every machine and in every build profile.
///
/// This is deliberately NOT the same mechanism as route 1. The two gates are
/// separate call sites in separate files, and a shared mechanism is how one test
/// ends up standing in for two guards.
struct AlwaysLateBackend {
    inner: SatBvBackend,
    /// How far past the caller's budget to run before answering.
    overrun_by: Duration,
}

impl SolverBackend for AlwaysLateBackend {
    fn capabilities(&self) -> Capabilities {
        self.inner.capabilities()
    }

    fn check(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let mut unbounded = config.clone();
        unbounded.timeout = None;
        let result = self.inner.check(arena, assertions, &unbounded)?;
        // Only now spend past the caller's deadline, so the verdict above is a
        // real one produced by a real search.
        std::thread::sleep(config.timeout.unwrap_or_default() + self.overrun_by);
        Ok(result)
    }

    fn last_stats(&self) -> Option<&SolveStats> {
        self.inner.last_stats()
    }
}

/// Route 2 of 2: `check_with_all_theories` — the funnel every `QF_BV`
/// front-door arm in `auto.rs` goes through, and the SECOND late-result
/// discard.
///
/// This is the test that would have been missing had the fix followed only the
/// site the original measurement named: restore `combined.rs`'s unconditional
/// gate and this fails while route 1 above still passes.
///
/// It also covers the four gates DELETED from the projection chain and the
/// replay loop below that one, because a `Sat` kept at the first gate has to
/// walk all of them to be returned.
#[test]
fn a_sat_decided_past_the_deadline_survives_the_combined_theory_gate() {
    let (mut arena, assertions) = wide_mul(64);
    let budget = Duration::from_millis(50);
    let config = SolverConfig::default().with_timeout(budget);
    let mut backend = AlwaysLateBackend {
        inner: SatBvBackend::new(),
        overrun_by: Duration::from_millis(150),
    };

    let started = Instant::now();
    let result = check_with_all_theories(&mut backend, &mut arena, &assertions, 32, &config)
        .expect("combined-theory invocation succeeds");
    let elapsed = started.elapsed();

    assert!(
        elapsed > budget,
        "the backend under test is built to overrun; if it did not ({elapsed:?} \
         <= {budget:?}) this assertion proves nothing"
    );
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "the combined-theory funnel must keep the decided verdict too, and its \
         own projection + replay must be allowed to finish. Got {result:?} after \
         {elapsed:?} against a {budget:?} budget"
    );
}

/// Control 1: the keep is not "timeouts are off now". An UNDECIDED search is
/// still reported as `unknown`, never upgraded to a verdict.
///
/// `resource_limit` reaches the native CDCL core as `max_conflicts`, so zero
/// conflicts admits no search at all. The budget is generous on purpose — the
/// point is that a result the search did not produce is not invented,
/// independently of the clock.
#[test]
fn an_undecided_search_is_still_unknown() {
    let (arena, assertions) = wide_mul(WIDTH);
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(60))
        .with_resource_limit(0);
    let result = SatBvBackend::new()
        .check(&arena, &assertions, &config)
        .expect("backend invocation succeeds");
    let CheckResult::Unknown(reason) = result else {
        panic!("a search stopped at zero conflicts cannot decide anything; got {result:?}");
    };
    assert_eq!(
        reason.kind,
        UnknownKind::ResourceLimit,
        "an undecided search must report why it stopped: {reason:?}"
    );
}

/// Control 2: a budget that expires BEFORE the work still stops it.
///
/// This is the half of the deadline contract the keep does not touch and must
/// not weaken — consult the clock before committing to work, never after the
/// work has answered. An already-expired deadline must buy no verdict at all.
#[test]
fn an_expired_budget_still_refuses_to_decide() {
    let (arena, assertions) = wide_mul(WIDTH);
    let config = SolverConfig::default().with_timeout(Duration::ZERO);
    let result = SatBvBackend::new()
        .check(&arena, &assertions, &config)
        .expect("backend invocation succeeds");
    let CheckResult::Unknown(reason) = result else {
        panic!("a zero budget must not decide anything; got {result:?}");
    };
    assert_eq!(
        reason.kind,
        UnknownKind::Timeout,
        "an expired budget must report a timeout: {reason:?}"
    );
}
