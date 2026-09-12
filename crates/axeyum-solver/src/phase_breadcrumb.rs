//! Where the worker **is**, not where it has **been**: a phase stack written on
//! ENTRY, readable from another thread while the worker is still inside it.
//!
//! # The gap this closes
//!
//! [`crate::route_trace`] and every instrument in [`crate::live_instruments`]
//! record at a boundary a stage has already crossed. `RouteTrace` records a
//! route when it DECIDES or DECLINES; `LazySmtCounters` flushes at the end of a
//! round; `BvStageMirror` publishes when a stage finishes. That is the right
//! shape for a query that returns, and exactly the wrong shape for a query that
//! does not: on a watchdog kill the last thing every one of them says is the
//! name of something that had already finished.
//!
//! Measured 2026-09-12 on `QF_UFLRA`'s
//! `cpachecker-induction.minepump_spec1_product56_false-unreach-call.cil.c.smt2`
//! at a 24 s budget with `--trace`: the trail read `fd:parse`, `probe`,
//! `dl-online` declined, `nra-real-root` declined, `nra` declined `unsupported`
//! — the last of them **38 ms** into the run — and then 25 s of nothing.
//! `RouteTrace::open_segment` could say the missing 25 s existed (that is what
//! it was added for) but nothing in the tree could say what was inside it.
//!
//! A breadcrumb frame is pushed when a phase is ENTERED and popped when it
//! returns, so the deepest frame is always the code that is running right now.
//! The stack lives behind an `Arc` published to the [`crate::live_instruments`]
//! board, so the watchdog thread reads it from wherever it is — and because the
//! harness *abandons* the worker rather than killing it, the `Mutex` is never
//! left poisoned by the kill itself (and a poisoned one is recovered anyway:
//! this is telemetry, and must never turn one panic into two).
//!
//! # What it costs when nobody is looking
//!
//! Off by default, like every other lever here. [`enter`] tests one
//! thread-local `Cell<bool>` and returns an unarmed guard; the guard's `Drop`
//! tests one `Option` on itself and returns. No clock is read, no lock is
//! taken, and no allocation happens. The determinism promise for a
//! `resource_limit`-only run is therefore untouched: the breadcrumb never
//! participates in a branch condition that a solver decision depends on, and
//! an unarmed run executes the same instructions it did before.
//!
//! # Where a frame may be placed
//!
//! An armed push/pop is one uncontended `Mutex` lock, one `Instant::now`, and a
//! `BTreeMap` bump. That is cheap per call and ruinous per pivot, so frames go
//! on **coarse phases**: a dispatch route, a theory entry point, an elimination
//! pass — never inside a propagation or pivot loop. The `enters` counter exists
//! precisely so a reader can tell "one call that has run for 24 s" from "four
//! million calls that each took 6 µs" without a frame per iteration.

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, PoisonError};

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::{Duration, Instant};
#[cfg(target_arch = "wasm32")]
use web_time::{Duration, Instant};

/// One live stack frame: a phase that has been entered and has not returned.
#[derive(Debug, Clone, Copy)]
struct Frame {
    label: &'static str,
    entered: Instant,
}

#[derive(Debug, Default)]
struct Inner {
    /// The phases currently entered, outermost first.
    stack: Vec<Frame>,
    /// How many times each label has been entered, for the whole run. A
    /// `BTreeMap`, never a `HashMap`: this feeds a report line and output order
    /// must not depend on per-process hash seeding.
    enters: BTreeMap<&'static str, u64>,
    /// The deepest stack the run ever reached, as labels. Kept because a phase
    /// that is entered and left in a refinement loop is invisible in `stack`
    /// at the instant the watchdog happens to read it, and "we got at least
    /// this far" is a different fact from "we are here now".
    deepest: Vec<&'static str>,
}

/// A cross-thread record of the phase stack a worker is currently inside.
///
/// Created and installed by whoever runs the worker (see [`install`]), read by
/// whoever enforces the wall clock (see [`PhaseBreadcrumb::snapshot`]).
#[derive(Debug, Default)]
pub struct PhaseBreadcrumb {
    inner: Mutex<Inner>,
}

/// A reading of a [`PhaseBreadcrumb`], taken from any thread at any time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhaseSnapshot {
    /// The phases entered and not yet returned, outermost first, each with how
    /// long it has been inside that frame as of the moment of the read.
    pub stack: Vec<(&'static str, Duration)>,
    /// Entry counts per label for the whole run so far, in label order. A
    /// count far above 1 on a frame that is *not* on `stack` is a loop that
    /// keeps re-entering a phase, which reads very differently from one long
    /// call.
    pub enters: Vec<(&'static str, u64)>,
    /// The deepest stack reached at any point in the run, as labels.
    pub deepest: Vec<&'static str>,
}

impl PhaseSnapshot {
    /// The innermost entered phase — the code that was running when the
    /// reading was taken — or `None` when no instrumented phase was active.
    ///
    /// `None` is a real answer and must be printed as one: it means the worker
    /// was somewhere this module has not put a frame, which is a finding about
    /// the instrument rather than about the solver.
    #[must_use]
    pub fn innermost(&self) -> Option<(&'static str, Duration)> {
        self.stack.last().copied()
    }

    /// Whether any frame was entered at all during the run.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.stack.is_empty() && self.enters.is_empty()
    }

    /// The `;`-prefixed trace line's body, without the `partial`/complete token
    /// the caller prepends.
    ///
    /// The stack renders innermost-LAST (`outer>inner`), matching the order a
    /// call chain is written everywhere else in this tree.
    #[must_use]
    pub fn trace_line(&self) -> String {
        use core::fmt::Write as _;
        let mut line = String::from("phase ");
        if self.stack.is_empty() {
            // Deliberately not an empty `stack=` field: "no frame was entered"
            // and "a frame was entered and this reader lost it" must not render
            // the same way.
            line.push_str("stack=none");
        } else {
            line.push_str("stack=");
            for (i, (label, held)) in self.stack.iter().enumerate() {
                if i > 0 {
                    line.push('>');
                }
                let _ = write!(line, "{label}({}ms)", held.as_millis());
            }
        }
        let _ = write!(line, " depth={}", self.stack.len());
        match self.innermost() {
            Some((label, held)) => {
                let _ = write!(line, " in={label} in_ms={}", held.as_millis());
            }
            None => line.push_str(" in=none in_ms=na"),
        }
        if !self.deepest.is_empty() {
            let _ = write!(line, " deepest={}", self.deepest.join(">"));
        }
        if !self.enters.is_empty() {
            line.push_str(" enters=");
            for (i, (label, count)) in self.enters.iter().enumerate() {
                if i > 0 {
                    line.push(',');
                }
                let _ = write!(line, "{label}:{count}");
            }
        }
        line
    }
}

impl PhaseBreadcrumb {
    /// An empty breadcrumb.
    #[must_use]
    pub fn new() -> Arc<Self> {
        Arc::new(Self::default())
    }

    /// Reads the current stack.
    ///
    /// A poisoned lock is recovered rather than propagated, for the same reason
    /// [`crate::live_instruments::LiveInstruments::publish`] recovers one.
    #[must_use]
    pub fn snapshot(&self) -> PhaseSnapshot {
        let now = Instant::now();
        let inner = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
        PhaseSnapshot {
            stack: inner
                .stack
                .iter()
                .map(|f| (f.label, now.saturating_duration_since(f.entered)))
                .collect(),
            enters: inner.enters.iter().map(|(k, v)| (*k, *v)).collect(),
            deepest: inner.deepest.clone(),
        }
    }

    fn push(&self, label: &'static str) {
        let entered = Instant::now();
        let mut inner = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
        inner.stack.push(Frame { label, entered });
        *inner.enters.entry(label).or_insert(0) += 1;
        if inner.stack.len() > inner.deepest.len() {
            inner.deepest = inner.stack.iter().map(|f| f.label).collect();
        }
    }

    fn pop(&self, label: &'static str) {
        let mut inner = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
        // Pop by label rather than blindly: a `?`-heavy function can drop
        // guards in an order the stack does not expect, and an unbalanced pop
        // that silently removed somebody else's frame would make the reading
        // wrong in a way nothing could detect. If the top is not ours we are
        // the victim of such a case and leave the stack alone.
        if inner.stack.last().is_some_and(|f| f.label == label) {
            inner.stack.pop();
        }
    }
}

thread_local! {
    /// Whether a breadcrumb is installed on this thread. Split out of the
    /// `RefCell` so [`enter`] on an uninstrumented thread — which is every
    /// thread on a default run — is one `Cell<bool>` read and a return.
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    /// The breadcrumb installed on this thread, if any.
    static BOARD: RefCell<Option<Arc<PhaseBreadcrumb>>> = const { RefCell::new(None) };
}

/// Installs `breadcrumb` on this thread for the lifetime of the returned guard,
/// restoring whatever was installed before on drop so nested installs compose.
pub fn install(breadcrumb: &Arc<PhaseBreadcrumb>) -> InstallGuard {
    let previous = BOARD.with(|slot| slot.borrow_mut().replace(Arc::clone(breadcrumb)));
    let was_active = ACTIVE.with(|flag| flag.replace(true));
    InstallGuard {
        previous,
        was_active,
    }
}

/// Restores the previously installed breadcrumb (if any) on drop; see
/// [`install`].
#[derive(Debug)]
pub struct InstallGuard {
    previous: Option<Arc<PhaseBreadcrumb>>,
    was_active: bool,
}

impl Drop for InstallGuard {
    fn drop(&mut self) {
        let previous = self.previous.take();
        BOARD.with(|slot| *slot.borrow_mut() = previous);
        ACTIVE.with(|flag| flag.set(self.was_active));
    }
}

/// Whether a breadcrumb is installed on this thread.
#[must_use]
pub fn installed() -> bool {
    ACTIVE.with(Cell::get)
}

/// Creates a breadcrumb, installs it on this thread, and publishes the handle
/// to this thread's [`crate::live_instruments`] board — the one call a harness
/// makes, matching the `*Guard::enable()` convention every other instrument
/// here follows.
///
/// The handle, not a snapshot, goes on the board: see
/// [`crate::live_instruments::instrument::PHASE`].
///
/// Returns `None` when no board is installed, because without one nothing could
/// ever read the breadcrumb and arming it would be pure cost.
#[must_use = "the breadcrumb is uninstalled when the guard drops"]
pub fn arm() -> Option<InstallGuard> {
    if !crate::live_instruments::installed() {
        return None;
    }
    let breadcrumb = PhaseBreadcrumb::new();
    let guard = install(&breadcrumb);
    crate::live_instruments::publish_live(
        crate::live_instruments::instrument::PHASE,
        breadcrumb,
        crate::live_instruments::Sampled::InFlight,
    );
    Some(guard)
}

/// Takes a reading of the breadcrumb published on `board`, from any thread.
///
/// `None` means no breadcrumb was ever installed (the run was not instrumented)
/// — which a reader must render differently from an installed breadcrumb whose
/// stack is empty, since the second says the worker was outside every
/// instrumented phase and the first says nothing at all.
#[must_use]
pub fn live_phase(
    board: &crate::live_instruments::LiveInstruments,
) -> Option<crate::live_instruments::LiveSample<PhaseSnapshot>> {
    let handle =
        board.sample::<Arc<PhaseBreadcrumb>>(crate::live_instruments::instrument::PHASE)?;
    Some(crate::live_instruments::LiveSample {
        value: handle.value.snapshot(),
        sampled: crate::live_instruments::Sampled::InFlight,
        sequence: handle.sequence,
    })
}

/// Pushes `label` onto this thread's breadcrumb; the returned guard pops it.
///
/// A silent no-op without an installed breadcrumb, at the cost of one
/// thread-local `bool` read on the way in and one `Option` test on the way out.
#[must_use = "the frame is popped when the guard drops; dropping it immediately records nothing"]
pub fn enter(label: &'static str) -> FrameGuard {
    if !installed() {
        return FrameGuard { label: None };
    }
    BOARD.with(|slot| {
        // `try_borrow`, never `borrow`: reached from deep inside a solve, and a
        // re-entrant call (which no current path produces) must drop the frame
        // rather than panic mid-search.
        if let Ok(board) = slot.try_borrow()
            && let Some(board) = board.as_ref()
        {
            board.push(label);
            FrameGuard { label: Some(label) }
        } else {
            FrameGuard { label: None }
        }
    })
}

/// Pops the frame [`enter`] pushed. Unarmed guards pop nothing.
#[derive(Debug)]
pub struct FrameGuard {
    label: Option<&'static str>,
}

impl Drop for FrameGuard {
    fn drop(&mut self) {
        let Some(label) = self.label else {
            return;
        };
        BOARD.with(|slot| {
            if let Ok(board) = slot.try_borrow()
                && let Some(board) = board.as_ref()
            {
                board.pop(label);
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::{PhaseBreadcrumb, enter, install, installed};
    use std::sync::Arc;
    use std::sync::mpsc;

    #[test]
    fn entering_without_an_install_is_a_no_op() {
        assert!(!installed());
        let g = enter("nowhere");
        assert!(!installed());
        drop(g);
    }

    #[test]
    fn the_innermost_frame_is_the_running_phase() {
        let bc = PhaseBreadcrumb::new();
        let _install = install(&bc);
        let _outer = enter("outer");
        let _inner = enter("inner");
        let snap = bc.snapshot();
        assert_eq!(
            snap.stack.iter().map(|(l, _)| *l).collect::<Vec<_>>(),
            vec!["outer", "inner"]
        );
        assert_eq!(snap.innermost().map(|(l, _)| l), Some("inner"));
        assert!(snap.trace_line().contains("in=inner"));
        assert!(snap.trace_line().contains("depth=2"));
    }

    #[test]
    fn a_returned_phase_leaves_the_stack_but_keeps_its_count() {
        let bc = PhaseBreadcrumb::new();
        let _install = install(&bc);
        for _ in 0..3 {
            let _f = enter("loop-body");
        }
        let snap = bc.snapshot();
        assert!(snap.stack.is_empty(), "every frame returned");
        assert_eq!(snap.enters, vec![("loop-body", 3)]);
        assert_eq!(snap.deepest, vec!["loop-body"]);
        let line = snap.trace_line();
        assert!(line.contains("stack=none"), "{line}");
        assert!(line.contains("in=none"), "{line}");
        assert!(line.contains("enters=loop-body:3"), "{line}");
    }

    /// The property the module exists for: the reading is taken from a thread
    /// that is not the worker, while the worker is still inside the phase —
    /// exactly the shape of a watchdog giving up on a solve.
    #[test]
    fn a_running_workers_phase_is_readable_from_another_thread() {
        let bc = PhaseBreadcrumb::new();
        let worker_bc = Arc::clone(&bc);
        let (entered_tx, entered_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel::<()>();
        let worker = std::thread::spawn(move || {
            let _install = install(&worker_bc);
            let _a = enter("dispatch");
            let _b = enter("lra::solve");
            entered_tx.send(()).expect("receiver alive");
            let _ = release_rx.recv();
        });
        entered_rx.recv().expect("worker entered");
        let snap = bc.snapshot();
        assert_eq!(snap.innermost().map(|(l, _)| l), Some("lra::solve"));
        assert_eq!(snap.deepest, vec!["dispatch", "lra::solve"]);
        let _ = release_tx.send(());
        worker.join().expect("worker finished");
    }

    #[test]
    fn an_empty_breadcrumb_says_so_rather_than_rendering_an_empty_stack() {
        let bc = PhaseBreadcrumb::new();
        let snap = bc.snapshot();
        assert!(snap.is_empty());
        let line = snap.trace_line();
        assert!(line.contains("stack=none"), "{line}");
        assert!(!line.contains("enters="), "{line}");
    }

    #[test]
    fn dropping_the_install_guard_restores_the_previous_breadcrumb() {
        let outer = PhaseBreadcrumb::new();
        let guard = install(&outer);
        {
            let inner = PhaseBreadcrumb::new();
            let _inner_guard = install(&inner);
            let _f = enter("inner-only");
            assert_eq!(
                inner.snapshot().innermost().map(|(l, _)| l),
                Some("inner-only")
            );
        }
        let _f = enter("outer-only");
        assert_eq!(
            outer.snapshot().innermost().map(|(l, _)| l),
            Some("outer-only")
        );
        drop(guard);
        assert!(!installed());
    }
}
