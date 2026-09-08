//! The property the cross-thread instrument board exists for: a solve that is
//! **abandoned by a watchdog on another thread** still reports real counters,
//! and those counters are labelled partial.
//!
//! # Why this shape and not a unit test
//!
//! Every instrument in this crate publishes into thread-local storage when its
//! stage returns. A wall-clock watchdog is on a different thread and fires
//! before the stage returns, so both halves of that publish are unreachable at
//! exactly the moment the numbers matter — 22 of 33 lost `QF_LRA` files printed
//! no theory-layer line at all. Nothing short of a real solve on a real second
//! thread, sampled from the first while the second is still inside the search,
//! exercises that.
//!
//! # Why it cannot pass by accident
//!
//! The reading is taken from a thread that has not returned anything, so it can
//! only have come from a mid-search mirror flush
//! (`axeyum_cnf::NativeLayerStatsMirror`, written from inside the CDCL(T) search
//! loop). Disable that flush and the sample is `None` and this test fails; the
//! fixture is sized so a completed search is a test failure with its own
//! message rather than a silent pass.
#![cfg(feature = "full")]

use std::fmt::Write as _;
use std::sync::Arc;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use axeyum_solver::theories::cdclt_diagnostics::TheoryLayerStatsGuard;
use axeyum_solver::{
    BvLayerStatsGuard, ConfigTraceGuard, FrontDoorStatsGuard, GroupReading, LiaCounterGroup,
    LiaCountersGuard, LiveInstruments, RouteAttributionGuard, Sampled, SolverConfig,
    install_live_instruments, instrument, live_bv_layer_stats, live_config_trace_line,
    live_lia_counters, live_theory_layer_stats, solve_smtlib,
};

/// How long the stand-in watchdog waits for a sample before giving up. Well
/// under the solve's own budget, so the reading really is taken mid-search.
const SAMPLE_DEADLINE: Duration = Duration::from_secs(20);

/// The worker's own soft budget. It exists only so the thread stops burning a
/// core shortly after the test has read what it needs — the test never waits
/// for it.
const WORKER_BUDGET: Duration = Duration::from_secs(25);

/// A pigeonhole instance in `QF_LIA`: `pigeons` integer variables each confined
/// to `pigeons - 1` values, pairwise distinct.
///
/// Unsatisfiable, and unsatisfiable for a reason a branch-and-bound integer
/// solver has to enumerate rather than see — which is what makes it a fixture
/// that reliably outlives a watchdog on any machine, without depending on a
/// corpus file or on how fast the host is.
fn pigeonhole_lia(pigeons: usize) -> String {
    let mut s = String::from("(set-logic QF_LIA)\n");
    for i in 0..pigeons {
        let _ = writeln!(s, "(declare-fun x{i} () Int)");
    }
    for i in 0..pigeons {
        let _ = writeln!(s, "(assert (and (>= x{i} 0) (<= x{i} {})))", pigeons - 2);
    }
    for i in 0..pigeons {
        for j in (i + 1)..pigeons {
            let _ = writeln!(s, "(assert (not (= x{i} x{j})))");
        }
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn a_solve_abandoned_by_a_watchdog_still_reports_partial_counters() {
    let board = LiveInstruments::new();
    let worker_board = Arc::clone(&board);
    let text = pigeonhole_lia(11);
    let (finished_tx, finished_rx) = mpsc::channel::<()>();

    // The worker: the same shape `smtcomp_cli` uses — install the board, arm
    // the collection guards, then run the whole front door. It is deliberately
    // never joined; a watchdog does not get to join the thread it gave up on.
    let worker = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let _live = install_live_instruments(&worker_board);
            let _theory = TheoryLayerStatsGuard::enable();
            let _route = RouteAttributionGuard::enable();
            let _front_door = FrontDoorStatsGuard::enable();
            let config = SolverConfig::default().with_timeout(WORKER_BUDGET);
            let _ = solve_smtlib(&text, &config);
            let _ = finished_tx.send(());
        })
        .expect("spawned the worker");

    // The watchdog: poll the board, exactly as the main thread does after
    // `recv_timeout` expires. Polling rather than a single fixed sleep so the
    // test is not a race against how fast the host reaches the search.
    let started = Instant::now();
    let sample = loop {
        if let Some(sample) = live_theory_layer_stats(&board) {
            break sample;
        }
        assert!(
            finished_rx.try_recv().is_err(),
            "the fixture was DECIDED before anything was sampled: it is too easy \
             to stand in for a timed-out file, so this test would be vacuous"
        );
        assert!(
            started.elapsed() < SAMPLE_DEADLINE,
            "no theory-layer reading appeared in {SAMPLE_DEADLINE:?}: the search \
             is running but nothing is mirroring it"
        );
        std::thread::sleep(Duration::from_millis(20));
    };

    assert_eq!(
        sample.sampled,
        Sampled::InFlight,
        "the worker has not returned, so any reading has to be a mid-search one: \
         {sample:?}"
    );
    // Non-empty is the whole point: before the mirror this was `None` and the
    // harness printed `; theory-layer unavailable: …`.
    assert!(
        sample.value.decisions > 0,
        "a partial reading must carry real counters, not an empty struct: {:?}",
        sample.value
    );
    assert!(
        sample.value.boolean_propagate > Duration::ZERO
            || sample.value.theory_assert > Duration::ZERO,
        "stage timings are collected too, not only the integer counters: {:?}",
        sample.value
    );

    // The route trail survives the same way, and is likewise mid-flight: the
    // front door is still inside the attempt that is consuming the budget.
    let route = board
        .sample::<axeyum_solver::RouteTrace>(instrument::ROUTE)
        .expect("the front door records its parse stage before it dispatches");
    assert!(
        !route.value.is_empty(),
        "an attributed route trail, not an empty one"
    );
    assert_eq!(route.sampled, Sampled::InFlight);

    // The front door's parse finished long before the watchdog fired, so its
    // reading is complete even though the query's is not. Keeping the two
    // distinguishable is the reason `Sampled` is on every sample rather than
    // being inferred from the fact that a watchdog asked.
    let parse = board
        .sample::<axeyum_solver::FrontDoorStats>(instrument::FRONT_DOOR)
        .expect("parse ran");
    assert_eq!(parse.sampled, Sampled::Complete);

    drop(worker);
}

/// A bit-vector factoring instance: two 16-bit factors whose product is a fixed
/// 32-bit semiprime, with both factors forced above 1.
///
/// Unsatisfiable-or-hard for a reason the bit-blast pipeline has to search
/// rather than see, so a check on it reliably outlives a watchdog. Used only to
/// keep a `sat-bv` check RUNNING while the board is sampled; the verdict is
/// never read.
fn bv_factoring() -> String {
    String::from(
        "(set-logic QF_BV)\n\
         (declare-fun a () (_ BitVec 32))\n\
         (declare-fun b () (_ BitVec 32))\n\
         (assert (bvugt a (_ bv1 32)))\n\
         (assert (bvugt b (_ bv1 32)))\n\
         (assert (bvult a (_ bv65536 32)))\n\
         (assert (bvult b (_ bv65536 32)))\n\
         (assert (= (bvmul a b) (_ bv3221225473 32)))\n\
         (check-sat)\n",
    )
}

/// Runs `text` on a worker that installs `board` and arms every collection
/// guard `smtcomp_cli --trace` arms, then polls `sample` from THIS thread until
/// it answers — the same shape as a watchdog sampling a worker it has given up
/// on. The worker is never joined.
///
/// Returns whatever `sample` produced. Panics with its own message if the
/// worker DECIDES the fixture first, because a decided fixture makes any
/// assertion below it vacuous.
fn sample_while_running<T>(
    text: String,
    board: &Arc<LiveInstruments>,
    what: &str,
    mut sample: impl FnMut() -> Option<T>,
) -> T {
    let worker_board = Arc::clone(board);
    let (finished_tx, finished_rx) = mpsc::channel::<()>();
    let worker = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let _live = install_live_instruments(&worker_board);
            let _config = ConfigTraceGuard::enable();
            let _theory = TheoryLayerStatsGuard::enable();
            let _bv = BvLayerStatsGuard::enable();
            let _route = RouteAttributionGuard::enable();
            let _front_door = FrontDoorStatsGuard::enable();
            let _lia = LiaCountersGuard::enable();
            let config = SolverConfig::default().with_timeout(WORKER_BUDGET);
            let _ = solve_smtlib(&text, &config);
            let _ = finished_tx.send(());
        })
        .expect("spawned the worker");

    let started = Instant::now();
    let value = loop {
        if let Some(value) = sample() {
            break value;
        }
        assert!(
            finished_rx.try_recv().is_err(),
            "the fixture was DECIDED before {what} was sampled: it is too easy to \
             stand in for a timed-out file, so this assertion would be vacuous"
        );
        assert!(
            started.elapsed() < SAMPLE_DEADLINE,
            "no {what} reading appeared in {SAMPLE_DEADLINE:?}: the solve is \
             running but nothing is mirroring it"
        );
        std::thread::sleep(Duration::from_millis(20));
    };
    drop(worker);
    value
}

/// The `; config` line survived. Before the `ConfigTraceMirror` it did not: its
/// consulted/crossed sets were thread-local to the worker with no publish site,
/// so a watchdog could print the static half or nothing, and printing the
/// static half alone leaves `consulted=` silently absent — which reads as
/// "nothing was consulted".
#[test]
fn a_watchdog_kill_still_reports_the_config_line() {
    let board = LiveInstruments::new();
    let sampled = {
        let board = Arc::clone(&board);
        sample_while_running(pigeonhole_lia(11), &board.clone(), "a config", move || {
            // Only accept a reading that actually carries the thread-local half.
            // A line with the static fields alone is the failure this exists to
            // rule out, so it must not satisfy the poll.
            live_config_trace_line(&board).filter(|line| line.value.contains(" consulted="))
        })
    };
    assert_eq!(
        sampled.sampled,
        Sampled::InFlight,
        "the worker has not returned, so the consulted set may still grow: {sampled:?}"
    );
    assert!(
        sampled.value.starts_with("; config digest="),
        "the mirror renders the SAME bytes the completed path renders, from one \
         formatter: {}",
        sampled.value
    );
    assert!(
        sampled.value.contains(" consulted="),
        "the consulted set is the half that could not cross a thread, and is the \
         only reason this line is worth printing: {}",
        sampled.value
    );
    // A registered key, not free text: `consulted_keys_are_registered` gates the
    // producing side, and this checks the key reached the READER intact.
    assert!(
        sampled.value.contains("crates/axeyum-solver/src/"),
        "a consulted key names its governing file: {}",
        sampled.value
    );
}

/// The integer-route counters survived — the instrument the `QF_LIA` losses are
/// made of, and the one with no stage boundary at all to publish from.
#[test]
fn a_watchdog_kill_still_reports_partial_integer_route_counters() {
    let board = LiveInstruments::new();
    let sampled = {
        let board = Arc::clone(&board);
        sample_while_running(
            pigeonhole_lia(11),
            &board.clone(),
            "an integer-route",
            move || live_lia_counters(&board),
        )
    };
    assert_eq!(
        sampled.sampled,
        Sampled::InFlight,
        "the worker has not returned, so every field is a lower bound: {sampled:?}"
    );
    // The distinction the LIA lane established, kept on the partial path: a
    // reading whose offline group is `Measured` is a measurement, and one whose
    // group is `NotReached` is not a zero.
    assert_eq!(
        sampled.value.group_reading(LiaCounterGroup::Offline),
        GroupReading::Measured,
        "the pigeonhole fixture runs the offline decider, so its group must read \
         as measured and not as an unreached zero: {:?}",
        sampled.value
    );
    assert!(
        sampled.value.offline_calls > 0,
        "a partial reading must carry real counters, not an empty struct: {:?}",
        sampled.value
    );
}

/// A `sat-bv` check killed mid-pipeline names the stage it was inside.
///
/// `publish_bv_layer_stats` fires only when a check RETURNS, so before the
/// stage mirror this path reported nothing for exactly the `sat-bv` files we
/// lose.
#[test]
fn a_bv_check_killed_mid_pipeline_reports_the_stage_it_was_in() {
    let board = LiveInstruments::new();
    let sampled = {
        let board = Arc::clone(&board);
        sample_while_running(bv_factoring(), &board.clone(), "a bv-stage", move || {
            // A reading with no stage came from a check that RETURNED, which is
            // the case this test is not about.
            live_bv_layer_stats(&board).filter(|reading| reading.value.stage.is_some())
        })
    };
    assert_eq!(
        sampled.sampled,
        Sampled::InFlight,
        "a staged reading is taken at a boundary, never at a verdict: {sampled:?}"
    );
    let stage = sampled.value.stage.expect("filtered on above");
    // `pending()` is derived from `BvStage::ORDER`, so this also pins that a
    // stage added to the pipeline cannot be silently absent from the answer.
    let pending = stage.pending();
    assert!(
        !pending.contains(&stage),
        "the stage a check is INSIDE is reached, not pending: {stage:?}"
    );
    assert!(
        pending.iter().all(|later| *later > stage),
        "pending stages come after the current one, in pipeline order: \
         {stage:?} -> {pending:?}"
    );
    // The rule the stage line exists to enforce: numbers are published only
    // once the encoding has identified the run as `sat-bv`, so a reading from
    // an earlier stage carries NO numbers rather than a row of zeros.
    if stage <= axeyum_solver::BvStage::CnfEncode {
        assert!(
            sampled.value.stats.is_none(),
            "a reading taken at or before the CNF encoding cannot carry stage \
             timings — a zero there would read as measured: {sampled:?}"
        );
    }
}
