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
    FrontDoorStatsGuard, LiveInstruments, RouteAttributionGuard, Sampled, SolverConfig,
    install_live_instruments, instrument, live_theory_layer_stats, solve_smtlib,
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
