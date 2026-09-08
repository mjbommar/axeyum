//! Instrument readings a thread that is **not** the worker can sample while the
//! worker is still running.
//!
//! # The problem this exists for
//!
//! Every diagnostic instrument in this workspace follows the same shape: an
//! opt-in `Cell<bool>` collection flag, a thread-local accumulator, a
//! `*Guard::enable()` that arms it, and a `last_*()` reader — see
//! `crate::cdclt::TheoryLayerStatsGuard`, [`crate::BvLayerStatsGuard`],
//! `crate::DlOnlineStatsGuard`, `crate::FrontDoorStatsGuard`,
//! `crate::RouteAttributionGuard`. The accumulator is thread-local to the
//! thread that ran the stage, and the snapshot is published when the stage
//! returns.
//!
//! Both halves fail together under a wall-clock watchdog. `axeyum-bench`'s
//! `smtcomp_cli` runs the whole pipeline on a worker thread and enforces the
//! budget from the main thread, because the soft deadline inside the solve
//! cannot see the ingest stage. When the watchdog fires, the worker has not
//! returned — so no snapshot was ever published — and the watchdog is on
//! another thread — so it could not read one anyway. The runs that most need
//! the numbers are precisely the runs that report none: 22 of 33 lost `QF_LRA`
//! files printed no theory-layer line at all, and 3 of 5 traced `QF_IDL`
//! timeouts hit the same path.
//!
//! A [`LiveInstruments`] board is the shared half. The harness creates one,
//! [`install`]s it on the worker thread, and every instrument that already has
//! a publish point mirrors its reading onto it. The watchdog samples the board
//! from wherever it is.
//!
//! # What a sample is, and what it is never
//!
//! Every sample carries [`Sampled`], which says whether the reading is the
//! instrument's finished answer or a state the search happened to be in. A
//! consumer must **label a mid-flight reading as partial** wherever it presents
//! it: a truncated count that reads like a complete one is worse than no count,
//! because somebody will divide by it. Nothing sampled here is a rate's
//! denominator.
//!
//! # Cost
//!
//! Nothing is installed unless a caller installs it, and [`publish_live`] tests
//! one thread-local `Cell<bool>` and returns when nothing is. Every publish site
//! additionally sits inside its own instrument's existing collection flag, so a
//! default run reaches none of them. There is deliberately no atomic per counter
//! increment: instruments mirror whole snapshots at stage boundaries (and, for
//! the one search loop long enough to need it, on a fixed iteration cadence —
//! see `axeyum_cnf::NativeLayerStatsMirror`), because a shared write on the
//! propagation path would perturb the very timings the instrument reports.
//!
//! # Adding an instrument
//!
//! Give it a name in [`instrument`], call [`publish_live`] wherever it already
//! publishes its thread-local snapshot, and read it back with
//! [`LiveInstruments::sample`]. Nothing else is needed: the board stores any
//! `Any + Send + Sync` value, so an instrument keeps its own typed snapshot
//! rather than being flattened into a counter map that would lose the fields a
//! typed renderer already knows how to print.

use std::any::Any;
use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

/// The instrument names this workspace publishes, as a closed vocabulary.
///
/// `&'static str` constants rather than free text, for the same reason
/// `crate::route_trace`'s route labels are: a name is matched against on the
/// reading side, and a typo would be an instrument that silently never appears
/// rather than a compile error.
pub mod instrument {
    /// [`crate::layers::TheoryLayerStats`] from a completed CDCL(T) search.
    pub const THEORY_LAYER: &str = "theory-layer";
    /// The `axeyum_cnf::NativeLayerStatsMirror` a *running* native CDCL(T)
    /// search writes to. Sampled through `crate::live_theory_layer_stats`,
    /// which resolves it against [`THEORY_LAYER`] and hands back one answer.
    pub const THEORY_LAYER_MIRROR: &str = "theory-layer-mirror";
    /// The theory-side `crate::euf_egraph::TheoryEngineCounters` a running
    /// search's adapter mirrors; the native core cannot read them itself,
    /// because the theory is mutably borrowed by the search at the flush point.
    pub const THEORY_ENGINE_MIRROR: &str = "theory-engine-mirror";
    /// [`crate::BvLayerStats`] from a completed `sat-bv` check.
    pub const BV_LAYER: &str = "bv-layer";
    /// `crate::FrontDoorStats` as of the last completed parse.
    pub const FRONT_DOOR: &str = "front-door";
    /// `(Duration, u64)`: cumulative `dl_online` call time and call count.
    pub const DL_ONLINE: &str = "dl-online";
    /// `crate::RouteTrace` as of the last recorded route attempt.
    pub const ROUTE: &str = "route";
}

/// Whether a reading is an instrument's finished answer or a state the run
/// happened to be in when it was taken.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sampled {
    /// Taken while the stage was still running. **Partial**: monotone counters
    /// are lower bounds, timings are lower bounds, and a value derived from
    /// them (a rate, a share, a mean) is not defined.
    InFlight,
    /// Taken when the stage returned. Complete for that stage — which is not
    /// the same as complete for the query, since a query can run a stage more
    /// than once.
    Complete,
}

impl Sampled {
    /// The token a report line prints, so one spelling is used everywhere.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Sampled::InFlight => "in-flight",
            Sampled::Complete => "complete",
        }
    }
}

/// One instrument's reading, with the provenance a consumer has to print.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiveSample<T> {
    /// The reading itself.
    pub value: T,
    /// Whether [`LiveSample::value`] is partial; see [`Sampled`].
    pub sampled: Sampled,
    /// The board-wide publish sequence number this reading was stored at.
    /// Monotone across *all* instruments, so two slots can be ordered against
    /// each other — which is how a still-running search is told apart from a
    /// completed earlier one.
    pub sequence: u64,
}

/// One stored reading.
struct Slot {
    value: Box<dyn Any + Send + Sync>,
    sampled: Sampled,
    sequence: u64,
}

/// A board of instrument readings, shared across threads.
///
/// Created by whoever enforces the wall clock, installed on the worker thread
/// with [`install`], and sampled from any thread at any time — including while
/// the worker runs and including after the worker has been abandoned.
#[derive(Default)]
pub struct LiveInstruments {
    /// A `BTreeMap`, never a `HashMap`: [`LiveInstruments::published`] feeds a
    /// report line, and this tree's determinism promise forbids output whose
    /// order depends on per-process hash seeding.
    slots: Mutex<BTreeMap<&'static str, Slot>>,
    /// The next publish sequence number.
    sequence: AtomicU64,
}

impl std::fmt::Debug for LiveInstruments {
    /// Hand-written because a `Slot` holds a `dyn Any`, which has no `Debug`.
    /// Prints what a reader can act on: which instruments have published and
    /// with what provenance.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LiveInstruments")
            .field("published", &self.published())
            .finish()
    }
}

impl LiveInstruments {
    /// An empty board.
    #[must_use]
    pub fn new() -> Arc<Self> {
        Arc::new(Self::default())
    }

    /// Stores `value` for `name`, replacing whatever was there.
    ///
    /// A poisoned lock is recovered rather than propagated: this is telemetry,
    /// and a panic on one thread must never become a second panic inside a
    /// solve.
    pub fn publish<T: Any + Send + Sync>(&self, name: &'static str, value: T, sampled: Sampled) {
        let sequence = self.sequence.fetch_add(1, Ordering::Relaxed);
        let mut slots = self.slots.lock().unwrap_or_else(PoisonError::into_inner);
        slots.insert(
            name,
            Slot {
                value: Box::new(value),
                sampled,
                sequence,
            },
        );
    }

    /// The reading stored for `name`, if any and if it is a `T`.
    ///
    /// A type mismatch reports `None` rather than panicking: a board is shared
    /// state and a wrong-typed read is a reader's bug, not a reason to take the
    /// process down mid-solve.
    #[must_use]
    pub fn sample<T: Any + Send + Sync + Clone>(&self, name: &str) -> Option<LiveSample<T>> {
        let slots = self.slots.lock().unwrap_or_else(PoisonError::into_inner);
        let slot = slots.get(name)?;
        let value = slot.value.downcast_ref::<T>()?.clone();
        Some(LiveSample {
            value,
            sampled: slot.sampled,
            sequence: slot.sequence,
        })
    }

    /// Every instrument that has published, with its provenance and sequence
    /// number, in name order.
    #[must_use]
    pub fn published(&self) -> Vec<(&'static str, Sampled, u64)> {
        let slots = self.slots.lock().unwrap_or_else(PoisonError::into_inner);
        slots
            .iter()
            .map(|(name, slot)| (*name, slot.sampled, slot.sequence))
            .collect()
    }

    /// Whether any instrument has published.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.slots
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .is_empty()
    }
}

thread_local! {
    /// Whether a board is installed on this thread. Split out of the
    /// `RefCell` below so [`publish_live`] on an uninstrumented thread — which
    /// is every thread on a default run — is one `Cell<bool>` read and a
    /// return, with no borrow and no `Arc` traffic.
    static LIVE_ACTIVE: Cell<bool> = const { Cell::new(false) };
    /// The board installed on this thread, if any.
    static LIVE_BOARD: RefCell<Option<Arc<LiveInstruments>>> = const { RefCell::new(None) };
}

/// Installs `board` for the lifetime of the returned guard, restoring whatever
/// was installed before on drop so nested installs compose.
///
/// Same RAII convention as every collection guard in this crate. Installing a
/// board does not enable any instrument: each one still consults its own
/// collection flag, so a board on a thread with no guards armed simply never
/// receives anything.
pub fn install(board: &Arc<LiveInstruments>) -> LiveInstrumentsGuard {
    let previous = LIVE_BOARD.with(|slot| slot.borrow_mut().replace(Arc::clone(board)));
    let was_active = LIVE_ACTIVE.with(|flag| flag.replace(true));
    LiveInstrumentsGuard {
        previous,
        was_active,
    }
}

/// Restores the previously installed board (if any) on drop; see [`install`].
pub struct LiveInstrumentsGuard {
    previous: Option<Arc<LiveInstruments>>,
    was_active: bool,
}

impl Drop for LiveInstrumentsGuard {
    fn drop(&mut self) {
        let previous = self.previous.take();
        LIVE_BOARD.with(|slot| *slot.borrow_mut() = previous);
        LIVE_ACTIVE.with(|flag| flag.set(self.was_active));
    }
}

/// Whether a board is installed on this thread.
///
/// Call this before building a value that only exists to be published: the
/// publish itself is already a no-op without a board, but constructing the
/// value is not.
#[must_use]
pub fn installed() -> bool {
    LIVE_ACTIVE.with(Cell::get)
}

/// Publishes `value` to this thread's board, if one is installed.
///
/// A silent no-op otherwise — the same convention every other lever in this
/// crate follows when its flag is off.
pub fn publish_live<T: Any + Send + Sync>(name: &'static str, value: T, sampled: Sampled) {
    if !installed() {
        return;
    }
    LIVE_BOARD.with(|slot| {
        // `try_borrow` rather than `borrow`: this is telemetry reached from
        // deep inside a solve, and a re-entrant publish (which no current call
        // path produces) must drop the reading, never panic mid-search.
        if let Ok(board) = slot.try_borrow()
            && let Some(board) = board.as_ref()
        {
            board.publish(name, value, sampled);
        }
    });
}

#[cfg(test)]
mod tests {
    use super::{LiveInstruments, Sampled, install, installed, instrument, publish_live};
    use std::sync::Arc;
    use std::sync::mpsc;

    #[test]
    fn publishing_without_a_board_is_a_no_op() {
        assert!(!installed(), "no board is installed by default");
        publish_live(instrument::FRONT_DOOR, 7_u32, Sampled::Complete);
        // Nothing to assert against but the absence of a panic and of a board:
        // the point is that an uninstrumented thread reaches the publish site
        // and nothing happens.
        assert!(!installed());
    }

    #[test]
    fn a_sample_round_trips_with_its_provenance() {
        let board = LiveInstruments::new();
        let _guard = install(&board);
        publish_live(instrument::FRONT_DOOR, 3_u32, Sampled::InFlight);
        let sample = board
            .sample::<u32>(instrument::FRONT_DOOR)
            .expect("just published");
        assert_eq!(sample.value, 3);
        assert_eq!(sample.sampled, Sampled::InFlight);
        assert_eq!(sample.sampled.label(), "in-flight");
    }

    #[test]
    fn a_wrong_typed_read_reports_absence_rather_than_panicking() {
        let board = LiveInstruments::new();
        board.publish(instrument::BV_LAYER, 1_u32, Sampled::Complete);
        assert!(board.sample::<String>(instrument::BV_LAYER).is_none());
        assert!(board.sample::<u32>(instrument::BV_LAYER).is_some());
    }

    #[test]
    fn sequence_numbers_order_two_different_instruments() {
        let board = LiveInstruments::new();
        board.publish(instrument::ROUTE, 1_u32, Sampled::InFlight);
        board.publish(instrument::BV_LAYER, 2_u32, Sampled::Complete);
        let first = board.sample::<u32>(instrument::ROUTE).unwrap();
        let second = board.sample::<u32>(instrument::BV_LAYER).unwrap();
        assert!(
            first.sequence < second.sequence,
            "{first:?} was published first"
        );
    }

    #[test]
    fn dropping_the_guard_restores_the_previous_board() {
        let outer = LiveInstruments::new();
        let guard = install(&outer);
        {
            let inner = LiveInstruments::new();
            let _inner_guard = install(&inner);
            publish_live(instrument::ROUTE, 1_u32, Sampled::InFlight);
            assert!(inner.sample::<u32>(instrument::ROUTE).is_some());
        }
        publish_live(instrument::ROUTE, 2_u32, Sampled::InFlight);
        assert_eq!(outer.sample::<u32>(instrument::ROUTE).unwrap().value, 2);
        drop(guard);
        assert!(!installed(), "the board is gone with its guard");
    }

    /// The property the whole module exists for: a reading published on one
    /// thread is visible from another **while that thread is still running**.
    ///
    /// The worker never returns anything and is never joined until the reading
    /// has been taken — exactly the shape of a watchdog giving up on a solve —
    /// and the main thread still gets the counter.
    #[test]
    fn a_reading_published_by_a_running_worker_is_visible_from_another_thread() {
        let board = LiveInstruments::new();
        let worker_board = Arc::clone(&board);
        let (published_tx, published_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel::<()>();
        let worker = std::thread::spawn(move || {
            let _guard = install(&worker_board);
            publish_live(instrument::THEORY_LAYER, 41_u32, Sampled::InFlight);
            published_tx.send(()).expect("receiver alive");
            // Blocks until the main thread has read the board, so the reading
            // is taken from a thread that has NOT finished.
            let _ = release_rx.recv();
        });
        published_rx.recv().expect("worker published");
        let sample = board
            .sample::<u32>(instrument::THEORY_LAYER)
            .expect("a running worker's reading is readable from here");
        assert_eq!(sample.value, 41);
        assert_eq!(sample.sampled, Sampled::InFlight);
        let _ = release_tx.send(());
        worker.join().expect("worker finished");
    }
}
