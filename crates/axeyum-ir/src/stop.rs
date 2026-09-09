//! Cooperative stop: "this thread's search is no longer wanted".
//!
//! # Why this exists
//!
//! A parallel portfolio needs the answer *"stop, someone else already
//! decided"*, and this tree had no way to say it. Every long-running route
//! polls a `deadline: Option<Instant>` computed from `config.timeout` **at
//! entry**, so once an arm is running there is no channel that reaches it: a
//! caller can neither shorten that deadline nor interrupt the call. Without one
//! a portfolio has exactly two bad options -- join every arm (so a query
//! decided in 0.5 s still costs the whole budget, a wall-clock regression on
//! every file the ladder already wins) or abandon the losing threads (which
//! bounds *time* and not *memory*: a detached route that keeps allocating is
//! how one test in this repository reached 125 GB and OOM-killed the host).
//!
//! So the token is **thread-local and cooperative**. A worker installs one for
//! the duration of its arm; the group requests a stop on every arm except the
//! winner; the arm observes it at the sites that already poll the deadline and
//! returns the graceful `unknown` those sites already return.
//!
//! # Why it lives in `axeyum-ir`
//!
//! The check has to be visible from BOTH `axeyum-solver` (the theory routes'
//! `past_deadline` helpers) and `axeyum-cnf` (the CDCL core's per-conflict
//! poll, which is where a bit-blasting arm actually spends its time). Those two
//! crates share only this one, and a stop flag that the SAT core cannot see
//! would leave the arm this portfolio most needs to cancel uncancellable.
//!
//! # Soundness
//!
//! Observing a stop request can only ever turn a search into `unknown` -- it is
//! read at sites that already return `unknown` for an expired deadline, and
//! `unknown` is a first-class result here. It can never convert a `sat` into an
//! `unsat` or the reverse, and a verdict already computed is unaffected. The
//! *winner* never has a stop requested on it, so a decided verdict is never
//! discarded because of one.
//!
//! # Determinism
//!
//! A stop is wall-clock-driven and therefore NOT deterministic: whether a given
//! arm observes one depends on which arm finished first on this run. That is
//! why a stop may only ever *discard* an arm's work -- the surviving verdict is
//! the one the group would have returned anyway. Nothing in this module may be
//! used to choose between two verdicts; see `axeyum_solver::portfolio` for the
//! fixed priority rule that does the choosing.

use std::cell::{Cell, RefCell};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

/// A shared "stop requested" flag, cloneable across threads.
///
/// Cheap to clone (one `Arc` bump) and cheap to poll (one relaxed load), which
/// matters because the poll sits inside refinement loops that run millions of
/// times.
#[derive(Debug, Clone, Default)]
pub struct StopToken(Arc<AtomicBool>);

impl StopToken {
    /// A fresh token with no stop requested.
    #[must_use]
    pub fn new() -> Self {
        Self(Arc::new(AtomicBool::new(false)))
    }

    /// Asks the holder of this token to stop.
    ///
    /// Idempotent and one-way: a token is never un-requested, because a route
    /// that has already observed the request may have returned `unknown`
    /// on the strength of it.
    pub fn request(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    /// Whether a stop has been requested on this token.
    #[must_use]
    pub fn is_requested(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }
}

thread_local! {
    /// Fast path: whether this thread has a token installed at all.
    ///
    /// Separate from [`TOKEN`] deliberately. Every deadline poll in the tree
    /// now runs [`stop_requested`], including on the main thread of a query
    /// that never uses a portfolio, and on that thread the whole check must be
    /// one thread-local `bool` read with no `RefCell` bookkeeping.
    static ARMED: Cell<bool> = const { Cell::new(false) };
    /// The installed token, if any.
    static TOKEN: RefCell<Option<StopToken>> = const { RefCell::new(None) };
}

/// Installs `token` on the current thread for the lifetime of the guard.
///
/// Nested installs are supported and restore the previous token on drop, so a
/// portfolio arm that itself dispatches a nested group cannot strand the outer
/// token.
#[derive(Debug)]
pub struct StopScope {
    previous: Option<StopToken>,
    previously_armed: bool,
}

impl StopScope {
    /// Installs `token` on this thread until the returned guard is dropped.
    #[must_use]
    pub fn install(token: &StopToken) -> Self {
        let previous = TOKEN.with(|slot| slot.replace(Some(token.clone())));
        let previously_armed = ARMED.with(|armed| armed.replace(true));
        Self {
            previous,
            previously_armed,
        }
    }
}

impl Drop for StopScope {
    fn drop(&mut self) {
        TOKEN.with(|slot| {
            *slot.borrow_mut() = self.previous.take();
        });
        ARMED.with(|armed| armed.set(self.previously_armed));
    }
}

/// Whether a stop has been requested for the work running on **this** thread.
///
/// One thread-local `bool` read when no token is installed, which is every
/// thread of every query that does not use a portfolio.
#[inline]
#[must_use]
pub fn stop_requested() -> bool {
    ARMED.with(Cell::get)
        && TOKEN.with(|slot| {
            slot.try_borrow()
                .ok()
                .and_then(|t| t.as_ref().map(StopToken::is_requested))
                .unwrap_or(false)
        })
}

/// The combined "should this search stop now?" test: a cooperative stop
/// request on this thread, or an expired wall-clock deadline.
///
/// The stop is tested FIRST because it is one thread-local `bool` read while
/// `Instant::now()` is a clock syscall's worth of work, and on the overwhelming
/// majority of calls (no portfolio anywhere in the process) the answer is
/// `false` and nothing else needs to be read.
///
/// Callers already handle `true` by returning a graceful `unknown`, which is
/// what makes adding the stop to this predicate sound rather than merely
/// convenient -- see the module docs.
#[inline]
#[must_use]
pub fn past_deadline(deadline: Option<std::time::Instant>) -> bool {
    stop_requested() || deadline.is_some_and(|d| std::time::Instant::now() >= d)
}

#[cfg(test)]
mod tests {
    use super::{StopScope, StopToken, stop_requested};

    #[test]
    fn a_thread_with_no_token_never_reports_a_stop() {
        assert!(!stop_requested());
        let token = StopToken::new();
        token.request();
        // Requested, but not installed here.
        assert!(!stop_requested());
    }

    #[test]
    fn an_installed_token_is_observed_and_the_scope_restores_the_previous_state() {
        let token = StopToken::new();
        {
            let _scope = StopScope::install(&token);
            assert!(!stop_requested());
            token.request();
            assert!(stop_requested());
        }
        assert!(!stop_requested(), "the scope must uninstall on drop");
    }

    #[test]
    fn a_nested_scope_restores_the_outer_token_rather_than_clearing_it() {
        let outer = StopToken::new();
        let inner = StopToken::new();
        outer.request();
        let _outer_scope = StopScope::install(&outer);
        assert!(stop_requested());
        {
            let _inner_scope = StopScope::install(&inner);
            assert!(
                !stop_requested(),
                "the inner token has no request; the outer one must not leak through"
            );
        }
        assert!(
            stop_requested(),
            "dropping the inner scope must restore the outer token, not clear it"
        );
    }

    #[test]
    fn a_token_installed_on_one_thread_is_invisible_to_another() {
        let token = StopToken::new();
        let _scope = StopScope::install(&token);
        token.request();
        assert!(stop_requested());
        let seen = std::thread::spawn(stop_requested).join().expect("joined");
        assert!(!seen, "the install is thread-local");
    }

    #[test]
    fn a_worker_thread_observes_a_request_made_from_the_parent() {
        let token = StopToken::new();
        let worker_token = token.clone();
        let handle = std::thread::spawn(move || {
            let _scope = StopScope::install(&worker_token);
            let start = std::time::Instant::now();
            while !stop_requested() {
                if start.elapsed() > std::time::Duration::from_secs(10) {
                    return false;
                }
                std::hint::spin_loop();
            }
            true
        });
        token.request();
        assert!(
            handle.join().expect("joined"),
            "the request must cross threads"
        );
    }
}
