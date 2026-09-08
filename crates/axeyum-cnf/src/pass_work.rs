//! The deterministic meter / budget pair shared by this crate's
//! occurrence-list passes.
//!
//! # Why this is one type and not two copies
//!
//! [`crate::bve`] and [`crate::simplify`] are the same shape of pass: build
//! literal occurrence lists over the whole formula, walk them repeatedly, and
//! remove clauses *lazily* (a removed clause's id stays in every list it was
//! ever in and is skipped on scan). They therefore have the same cost
//! structure, want the same three numbers out — total spend, whether a budget
//! stopped the pass, and the reading at the last useful action — and want the
//! same one-comparison check on the hot path.
//!
//! BVE grew those numbers first (2026-09-08). Subsumption needed exactly them
//! and nothing else, so they moved here rather than being written twice: two
//! copies of a work meter drift in what they charge, and the moment they do,
//! "BVE spent 300 M steps and subsumption spent 40 M" stops being a comparison.
//! One type means one charging discipline and one unit.
//!
//! # The unit
//!
//! **Occurrence-list steps**: one per occurrence-list entry examined, one per
//! literal merged or compared while building a candidate, one per occurrence
//! entry written. It is the unit `CaDiCaL` and `Kissat` budget elimination and
//! forward subsumption in, and it is charged everywhere a pass touches memory
//! proportionally to formula size.
//!
//! Two properties are load-bearing. It is **deterministic** — a fixed formula
//! and fixed options give a fixed count on any host, which a
//! `deadline: Option<Instant>` cannot — and it is **monotone in the work that
//! actually costs**, so a budget in it bounds the pass rather than bounding one
//! component of it. (Both passes shipped with a bound on a component: BVE
//! capped *resolution attempts* and subsumption capped *subsumption checks*,
//! and on the files that cost seconds neither cap was ever reached, because
//! neither counts the occurrence-list scan that dominates.)
//!
//! # Why not `axeyum_ir::budget::WorkMeter`
//!
//! Because `axeyum-cnf` does not depend on `axeyum-ir`, and adding that
//! dependency to hold a `u64` counter would pull the term IR — sorts, terms,
//! the arena — into the CNF layer for no gain (ADR-0001: crate boundaries are
//! added when a boundary is proven by use, not to share a struct). The split is
//! deliberate and matches where the two decisions live: a pass **meters itself**
//! in its own crate, and the **policy** that turns a formula into a budget is
//! `axeyum_ir::budget`'s `EffortPolicy` / `EffortAccount` / `Grant`, used from
//! `axeyum-solver` where the admission decision is made. `PassWork::must_stop`
//! is the same `spent >= limit` test as `axeyum_ir::budget::Budget::exhausted`,
//! deliberately, so a limit computed there is consumed unchanged here.

/// A pass's work meter together with the budget bounding it.
///
/// Constructed with the pass's setup cost already charged (see
/// [`PassWork::with_setup`]), so a pass that does nothing still reports what its
/// occurrence lists cost to build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PassWork {
    spent: u64,
    /// Absolute stop value; [`u64::MAX`] when the pass is unbudgeted.
    limit: u64,
    at_last_progress: u64,
    exhausted: bool,
    dead_entries: u64,
}

impl PassWork {
    /// A meter starting at `setup`, bounded by `budget` (`None` = unbounded).
    ///
    /// **Setup is charged up front rather than left free.** Building the
    /// occurrence lists touches every literal occurrence once and every
    /// occurrence-list slot once, and it is exactly the fixed `O(|F|)` cost
    /// `CaDiCaL`'s accumulate-and-delay gate exists to amortise
    /// (`references/cadical/src/probe.cpp:902-907`). A meter that started at
    /// zero after setup would report a pass that did nothing as having spent
    /// nothing, and an admission test reading that number would be comparing a
    /// budget against a cost it had excluded.
    ///
    /// The last-progress reading starts at `setup` for the same reason: on a run
    /// that achieves nothing, "how much came after the last useful action" is
    /// answered by *all of it after setup*, not by zero.
    #[must_use]
    pub const fn with_setup(setup: u64, budget: Option<u64>) -> Self {
        Self {
            spent: setup,
            limit: match budget {
                Some(limit) => limit,
                None => u64::MAX,
            },
            at_last_progress: setup,
            exhausted: false,
            dead_entries: 0,
        }
    }

    /// Charges `units` of work. Saturating: never wraps, so an absurd charge
    /// degrades to "budget exhausted" and can never make an exhausted budget
    /// look fresh.
    #[inline]
    pub const fn charge(&mut self, units: u64) {
        self.spent = self.spent.saturating_add(units);
    }

    /// Total charged so far, setup included.
    #[inline]
    #[must_use]
    pub const fn spent(&self) -> u64 {
        self.spent
    }

    /// Records that the pass just did something useful (eliminated a variable,
    /// subsumed or strengthened a clause).
    #[inline]
    pub const fn note_progress(&mut self) {
        self.at_last_progress = self.spent;
    }

    /// The meter reading at the last [`PassWork::note_progress`], or the setup
    /// cost if there has not been one.
    ///
    /// [`PassWork::spent`] minus this is spend after the last useful action —
    /// pure waste, and the exact quantity a budget is trying to avoid. It is
    /// what makes a budget a *measured* constant rather than a guess: a budget
    /// at or above this reading costs the run nothing at all, and one below it
    /// can be priced in the progress it gives up. One unbudgeted sweep
    /// therefore prices every candidate budget, instead of needing one sweep
    /// per candidate.
    #[inline]
    #[must_use]
    pub const fn at_last_progress(&self) -> u64 {
        self.at_last_progress
    }

    /// **The hot check**: whether the budget is spent. One comparison, no
    /// clock, no allocation.
    ///
    /// Latches [`PassWork::exhausted`] when it fires, so a pass cannot break out
    /// of its loop without recording *why* it stopped. That distinction is the
    /// whole point of the meter: "reached its own fixpoint" and "ran out of
    /// budget" look identical in a wall-clock timing and call for opposite work.
    #[inline]
    pub const fn must_stop(&mut self) -> bool {
        if self.spent >= self.limit {
            self.exhausted = true;
            true
        } else {
            false
        }
    }

    /// Whether [`PassWork::must_stop`] ever fired.
    #[inline]
    #[must_use]
    pub const fn exhausted(&self) -> bool {
        self.exhausted
    }

    /// Records `count` occurrence entries examined whose clause had **already
    /// been removed**. These are charged like any other entry (the scan reads
    /// them either way); this counts them separately.
    #[inline]
    pub const fn charge_dead(&mut self, count: u64) {
        self.dead_entries = self.dead_entries.saturating_add(count);
    }

    /// Occurrence entries examined that were already dead — the size of the
    /// lazy-removal constant, measured rather than assumed.
    ///
    /// This is the number that decides whether compaction is worth anything to
    /// a pass. It is a *subset* of [`PassWork::spent`], not an addition to it,
    /// so `dead / spent` is the fraction of the pass's scanning that a perfect
    /// compactor would delete. A pass whose lists cannot go stale reports zero,
    /// and that zero is a finding rather than an absence of instrumentation.
    #[inline]
    #[must_use]
    pub const fn dead_entries(&self) -> u64 {
        self.dead_entries
    }
}

/// Compact an occurrence list once at least half its entries are dead.
///
/// Both passes remove clauses **lazily** — the id stays in every occurrence list
/// it was ever in, and every later scan of that list pays for it again. That is
/// a pure constant on the files that cost seconds, and a budget *hides* it
/// (the pass stops sooner) rather than removing it.
///
/// `live(id)` must be monotone: an id that is dead stays dead. Both callers
/// satisfy this — a clause slot set to `None` is never refilled, and new
/// clauses get fresh ids appended — which is what makes dropping the entry safe
/// rather than merely convenient.
///
/// Returns whether it compacted. The rewrite is charged to `work`, because it is
/// real work the pass does and a "free" optimisation that the meter cannot see
/// is one nobody can price.
///
/// # Why half
///
/// Compacting on every scan would make the pass quadratic in list length for
/// lists that never go stale; never compacting is today's behaviour. At the
/// halfway mark each rewrite is paid for by the next scan of the same list, so
/// the amortised cost is bounded by a constant factor while the scan cost is
/// halved — the standard lazy-deletion trade, and the same threshold `CaDiCaL`
/// uses for its garbage-collection trigger.
pub(crate) fn compact_dead_entries(
    list: &mut Vec<usize>,
    live_count: usize,
    work: &mut PassWork,
    live: impl Fn(usize) -> bool,
) -> bool {
    let before = list.len();
    if live_count * 2 > before {
        return false; // fewer than half the entries are dead
    }
    list.retain(|&id| live(id));
    work.charge(before as u64);
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Setup is inside the meter, not before it.
    ///
    /// Mutation control for `with_setup`'s `spent: setup` (deleting it, i.e.
    /// starting the meter at zero, makes this fail).
    #[test]
    fn setup_is_charged_before_the_pass_does_anything() {
        let work = PassWork::with_setup(1_000, None);
        assert_eq!(work.spent(), 1_000);
        assert_eq!(work.at_last_progress(), 1_000);
        assert!(!work.exhausted());
    }

    /// An unbudgeted meter never stops, and a budgeted one stops exactly at its
    /// limit — not one step early and not one step late.
    #[test]
    fn must_stop_fires_at_the_limit_and_never_without_one() {
        let mut unbounded = PassWork::with_setup(0, None);
        unbounded.charge(u64::MAX / 2);
        assert!(!unbounded.must_stop());
        assert!(!unbounded.exhausted());

        let mut bounded = PassWork::with_setup(0, Some(10));
        bounded.charge(9);
        assert!(!bounded.must_stop(), "9 < 10 must not stop");
        assert!(!bounded.exhausted());
        bounded.charge(1);
        assert!(bounded.must_stop(), "10 >= 10 must stop");
        assert!(bounded.exhausted(), "the reason must be latched");
    }

    /// The exhausted flag is latched by the check, so a pass cannot break out
    /// of its loop without recording why. Mutation control for the
    /// `self.exhausted = true` line.
    #[test]
    fn the_stop_reason_survives_further_charging() {
        let mut work = PassWork::with_setup(0, Some(4));
        work.charge(4);
        assert!(work.must_stop());
        work.charge(100);
        assert!(work.exhausted());
    }

    /// Progress is recorded at the reading it happened at, and the gap to the
    /// total is the waste a budget is trying to avoid.
    #[test]
    fn last_progress_brackets_the_free_budget() {
        let mut work = PassWork::with_setup(7, None);
        work.charge(20);
        work.note_progress();
        work.charge(300);
        assert_eq!(work.at_last_progress(), 27);
        assert_eq!(work.spent(), 327);
        assert_eq!(work.spent() - work.at_last_progress(), 300);
    }

    /// Dead entries are a subset of the spend, not an addition to it.
    ///
    /// Mutation control for `charge_dead`: it must not move `spent`, or the
    /// dead fraction stops being a fraction of the same denominator.
    #[test]
    fn dead_entries_are_counted_inside_the_spend_not_beside_it() {
        let mut work = PassWork::with_setup(0, None);
        work.charge(10);
        work.charge_dead(4);
        assert_eq!(work.spent(), 10, "counting a dead entry must not charge it");
        assert_eq!(work.dead_entries(), 4);
        assert!(work.dead_entries() <= work.spent());
    }

    /// Compaction fires at half dead, not before, and charges what it rewrote.
    ///
    /// Mutation control for the `live_count * 2 > before` threshold: flipping
    /// the comparison, or removing the early return, makes the first assertion
    /// fail; deleting the `work.charge` makes the last one fail.
    #[test]
    fn compaction_waits_for_half_the_list_to_die() {
        let mut work = PassWork::with_setup(0, None);
        let mut list = vec![0, 1, 2, 3];
        // Three of four live: below the threshold, so nothing happens at all.
        assert!(!compact_dead_entries(&mut list, 3, &mut work, |id| id != 0));
        assert_eq!(list, vec![0, 1, 2, 3]);
        assert_eq!(work.spent(), 0, "a scan that does not compact charges here");

        // Two of four live: at the threshold.
        assert!(compact_dead_entries(&mut list, 2, &mut work, |id| id > 1));
        assert_eq!(list, vec![2, 3], "order is preserved");
        assert_eq!(work.spent(), 4, "the rewrite is charged, not free");
    }
}
