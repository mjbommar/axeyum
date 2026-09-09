//! An embedder-installed "stop now" hook for the CDCL core's deadline poll.
//!
//! # Why a hook rather than a shared flag
//!
//! A parallel portfolio has to be able to cancel a losing arm, and a
//! bit-blasting arm spends nearly all of its wall time inside one call to the
//! CDCL core. Without a channel into that loop the coordinator has two bad
//! choices: wait for the arm to reach its own deadline (so a query decided in
//! 0.5 s still costs the whole budget), or abandon the thread (which bounds
//! *time* and not *memory* — an abandoned route that keeps allocating is how
//! this repository once reached 125 GB and OOM-killed the host).
//!
//! The flag itself lives in `axeyum-ir` (`axeyum_ir::stop`), because that is
//! where the theory routes read it. This crate deliberately does **not** depend
//! on the term IR — it is the CNF/SAT layer and knows nothing about terms — so
//! importing the flag directly would invert the layering for one `bool`.
//! Instead the embedder installs a predicate and this crate calls it. One
//! source of truth, no new dependency edge, and a `axeyum-cnf` used on its own
//! keeps its current behaviour exactly: with no hook installed the check is one
//! relaxed load of a null pointer-sized cell.
//!
//! # Soundness
//!
//! The hook is consulted only at sites that already poll a wall-clock deadline
//! and already answer `true` by abandoning the search with an **undecided**
//! outcome. It can therefore never turn a `sat` into an `unsat` or the reverse;
//! it can only cause a search to report that it did not finish.

use std::sync::OnceLock;

/// The installed predicate, if any. A plain `fn` pointer rather than a boxed
/// closure so the call is a direct indirect-call with no allocation and the
/// cell stays `Sync` without a lock.
static STOP_HOOK: OnceLock<fn() -> bool> = OnceLock::new();

/// Installs the predicate the CDCL core consults alongside its deadline.
///
/// First writer wins and later calls are ignored, so two embedders cannot
/// silently take the check away from each other. Intended to be called once per
/// process, with a predicate that is cheap (a thread-local read) and that
/// answers for **the calling thread**.
pub fn set_stop_hook(hook: fn() -> bool) {
    // A second install is not an error: the value is process-global and the
    // only caller in this workspace installs the same function.
    let _ignored_second_install = STOP_HOOK.set(hook);
}

/// Whether the embedder wants the work on this thread to stop.
///
/// `false` when no hook is installed, which is every build that does not use a
/// portfolio.
#[inline]
#[must_use]
pub(crate) fn stop_requested() -> bool {
    STOP_HOOK.get().is_some_and(|hook| hook())
}

/// The combined "should this search stop now?" test used by the CDCL core:
/// an embedder stop request, or an expired deadline.
///
/// The hook is tested first because when none is installed it is one load and a
/// branch, while `Instant::now()` is a clock read.
#[inline]
#[must_use]
pub(crate) fn past_deadline(deadline: Option<std::time::Instant>) -> bool {
    stop_requested() || deadline.is_some_and(|d| std::time::Instant::now() >= d)
}

#[cfg(test)]
mod tests {
    use super::{past_deadline, stop_requested};

    #[test]
    fn with_no_hook_the_check_is_exactly_the_deadline() {
        // This process installs no hook (the solver crate does, in its own test
        // binary), so the predicate must reduce to the deadline test.
        assert!(!stop_requested());
        assert!(!past_deadline(None));
        assert!(past_deadline(Some(
            std::time::Instant::now() - std::time::Duration::from_secs(1)
        )));
        assert!(!past_deadline(Some(
            std::time::Instant::now() + std::time::Duration::from_secs(60)
        )));
    }
}
