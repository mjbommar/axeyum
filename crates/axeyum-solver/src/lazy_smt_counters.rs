//! Counters for the lazy-SMT (DPLL(T)) refinement loops in [`crate::dpll_t`].
//!
//! # The measurement that made this necessary
//!
//! `--trace` grew seven instrument lines and a cross-thread board so that a
//! timed-out file would still say where its budget went. Run against the 22
//! `QF_LRA` files that print no theory-layer line — the population the whole
//! effort was for — the answer came back the same on every one of them:
//! `bound_by=nra`, 99% of the total, and nothing else to say. Those files do
//! not lose their instruments to a watchdog. They return normally, and they are
//! silent because the route that consumed the budget has **no instrument at
//! all**.
//!
//! That route is [`crate::dpll_t::check_with_lra_dpll_within`]'s abstraction /
//! refinement loop (the `nra` label in the route trail covers both lazy-SMT
//! loops). Each round runs a full `sat-bv` check on a Boolean skeleton plus the
//! blocking clauses learned so far, then decides the chosen cube with the exact
//! theory. Every instrument that could have described it reports the wrong
//! thing:
//!
//! - `; theory-layer` is silent because the generic CDCL(T) driver never ran:
//!   the online-LRA probe at the top of that function declined structurally and
//!   the legacy loop below it took the query.
//! - `; bv-layer` is "last call wins", so on an N-round loop it describes round
//!   N and says nothing about the other N-1 or about how large N is.
//! - `; route` names the route and its share of the budget, which is how this
//!   was found, but a route label cannot say whether 24 seconds went to four
//!   enormous rounds or forty thousand small ones — and those have opposite
//!   remedies.
//!
//! # What this answers
//!
//! [`LazySmtCounters::rounds`] with the two stage timings splits the loop's cost
//! into the propositional half and the theory half, which is the first question
//! anybody asks of a refinement loop. [`LazySmtCounters::blocking_clauses`] and
//! `blocking_literals` say how fast the learned set grows, which is what makes
//! round `k` more expensive than round 1.
//!
//! # Reading a snapshot
//!
//! Same three-way discipline as [`crate::LiaCounters`]: [`last_lazy_smt_counters`]
//! returns [`Option`], and `None` means **collection was never enabled**, never
//! "the loops did nothing". A `Some` whose `entries` are zero means the loops
//! were never entered on this query — an honest measurement, and a different
//! statement from a `Some` with entries and zero rounds, which means a loop was
//! entered and bailed at its deadline check before the first round.
//! [`LazySmtCounters::reading`] returns which of the three it is; a bare `0`
//! must never be quoted without it.
//!
//! # Cost
//!
//! Off by default: every recording site reads one thread-local `Cell<bool>` and
//! returns. Armed, the clock is read four times per ROUND, and a round contains
//! a whole `sat-bv` check plus an exact theory decision — the instrument cannot
//! perturb what it measures at that granularity. There is no per-iteration work
//! anywhere finer than a round.

use std::cell::{Cell, RefCell};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

/// What a snapshot's numbers are allowed to be read as.
///
/// The same closed set [`crate::GroupReading`] establishes for the integer
/// routes, restated here because these counters are a different instrument with
/// a different entry site and sharing the enum would suggest they share a
/// policy, which they do not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LazySmtReading {
    /// Neither lazy-SMT loop was entered on this query. The fields are zero
    /// *because nothing ran*, which is a measurement — and the common case, since
    /// most queries never reach this route.
    NotReached,
    /// A loop was entered but bailed before completing a round: the deadline
    /// check at the head of the loop fired first. `rounds` is zero and that zero
    /// is real.
    EnteredNoRounds,
    /// A loop ran at least one round; every field is a measurement.
    Measured,
}

impl LazySmtReading {
    /// The token a report line prints, so one spelling is used everywhere.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            LazySmtReading::NotReached => "not-reached",
            LazySmtReading::EnteredNoRounds => "entered-no-rounds",
            LazySmtReading::Measured => "measured",
        }
    }
}

/// Which of the two lazy-SMT loops a recording belongs to.
///
/// Counted separately because they are different deciders behind one route
/// label: the linear loop decides each cube with the exact-rational
/// `check_with_lra_within`, the nonlinear one with the sign-cell CAD. Summing
/// them would produce a "theory check" total whose mean says nothing about
/// either engine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LazySmtLoop {
    /// [`crate::dpll_t::check_with_lra_dpll_within`], linear real arithmetic.
    Lra,
    /// `check_with_nra_dpll_within`, nonlinear real arithmetic over the CAD.
    Nra,
}

/// Counters for one query's lazy-SMT refinement loops.
///
/// Every field is a monotone total over the lifetime of the active
/// [`LazySmtCountersGuard`], so a per-query figure is a whole snapshot and a
/// per-round figure is a ratio. **Read [`LazySmtCounters::reading`] before
/// quoting any field.**
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct LazySmtCounters {
    /// Calls into the linear lazy-SMT loop.
    pub lra_entries: u64,
    /// Refinement rounds the linear loop completed the propositional half of.
    pub lra_rounds: u64,
    /// Calls into the nonlinear lazy-SMT loop.
    pub nra_entries: u64,
    /// Refinement rounds the nonlinear loop completed the propositional half of.
    pub nra_rounds: u64,

    /// Time inside the round's propositional solve (`check_with_all_theories`,
    /// i.e. a full `sat-bv` check over the skeleton plus every blocking clause
    /// learned so far), summed over rounds.
    pub skeleton_solve: Duration,
    /// Propositional solves that returned `sat`, so the round went on to the
    /// theory half.
    pub skeleton_sat: u64,
    /// Propositional solves that returned `unsat` — the loop's `unsat` exit.
    pub skeleton_unsat: u64,
    /// Propositional solves that returned `unknown`, which ends the loop.
    pub skeleton_unknown: u64,

    /// Time inside the round's theory decision on the chosen cube, summed over
    /// rounds. `skeleton_solve + theory_check` is the loop's accounted cost; the
    /// remainder of the route's `bound_ms` is abstraction and cube assembly.
    pub theory_check: Duration,
    /// Cubes the theory found consistent — the loop's `sat` exit.
    pub theory_sat: u64,
    /// Cubes the theory refuted, each of which contributes a blocking clause.
    pub theory_unsat: u64,
    /// Cubes the theory could not decide, which ends the loop.
    pub theory_unknown: u64,

    /// Time building the blocking clause a refuted cube contributes: the Farkas
    /// core extraction plus the clause construction, summed over rounds.
    ///
    /// Its own field because it is its own decider. `conflict_core` re-solves
    /// the refuted conjunction to obtain the Farkas multipliers that name the
    /// infeasible core — a second LP per round, on top of the one
    /// [`Self::theory_check`] already timed. Measured 2026-09-08 on the 22
    /// `QF_LRA` files bound by this route, `skeleton_solve + theory_check`
    /// accounted for only about half of the route's wall clock, and the
    /// remainder scaled with the ROUND count rather than with anything else —
    /// which is what pointed here. An accounting that leaves half the budget
    /// unattributed invites the next reader to guess.
    pub core_extraction: Duration,
    /// Blocking clauses learned, i.e. the size of the set that grows the
    /// propositional solve from round to round.
    pub blocking_clauses: u64,
    /// Literals across those clauses. `blocking_literals / blocking_clauses` is
    /// the mean learned-core width, which is what says whether the Farkas core
    /// is doing real work or the loop is blocking whole assignments.
    pub blocking_literals: u64,
    /// Atoms the abstraction produced, summed over entries. With `*_entries` it
    /// gives the mean skeleton width, which bounds how many rounds the loop can
    /// possibly need.
    pub atoms: u64,

    /// Blocking clauses whose Farkas certificate came from the theory decision
    /// that refuted the cube — no second LP.
    ///
    /// This and the three `cores_rederived_*` fields partition the
    /// [`Self::blocking_clauses`] total exactly, so a reader can check the
    /// accounting rather than take it on trust.
    pub cores_reused: u64,
    /// Re-derivations because the round carried **no** certificate: the cube was
    /// refuted without a linear refutation (a literally-`false` literal), so
    /// there was nothing to reuse.
    pub cores_rederived_absent: u64,
    /// Re-derivations because the carried certificate did not bind to the
    /// literal set the core was requested for. Zero on every current call path
    /// — the round hands over the certificate for the cube it just refuted —
    /// and non-zero would mean a refactor moved the two apart, which is the
    /// wrong-`unsat` shape this counter exists to make visible.
    pub cores_rederived_stale: u64,
    /// Re-derivations because the carried certificate failed its self-check on
    /// the reuse path. A producer never returns an unverified certificate, so
    /// this is a corruption tripwire and any non-zero reading is a defect.
    pub cores_rederived_unverified: u64,
    /// Conflicts blocked by the **whole** cube because no certificate lined up
    /// one-to-one with the assignment (an equality atom splits into two
    /// constraints, so the multiplier vector is longer than the assignment).
    /// Sound but coarse: a wide blocking clause rules out fewer assignments, so
    /// this is the counter that says the loop is learning weak lemmas.
    pub cores_full_assignment: u64,
}

impl LazySmtCounters {
    /// Which of the three statements this snapshot is making; see
    /// [`LazySmtReading`].
    #[must_use]
    pub fn reading(&self) -> LazySmtReading {
        if self.lra_entries == 0 && self.nra_entries == 0 {
            LazySmtReading::NotReached
        } else if self.rounds() == 0 {
            LazySmtReading::EnteredNoRounds
        } else {
            LazySmtReading::Measured
        }
    }

    /// Rounds across both loops.
    #[must_use]
    pub fn rounds(&self) -> u64 {
        self.lra_rounds.saturating_add(self.nra_rounds)
    }

    /// Farkas certificates the core extraction had to derive a **second** time,
    /// across all three reasons.
    ///
    /// The number this instrument was added to drive to zero: each one is a
    /// whole extra `QF_LRA` decision on a literal set the round had just
    /// decided. Read it against [`Self::cores_reused`] — a ratio, not a total,
    /// since both scale with the round count.
    #[must_use]
    pub fn cores_rederived(&self) -> u64 {
        self.cores_rederived_absent
            .saturating_add(self.cores_rederived_stale)
            .saturating_add(self.cores_rederived_unverified)
    }

    /// The loop cost this instrument accounts for: the propositional half plus
    /// the theory half.
    ///
    /// Deliberately NOT the route's total. The difference between this and the
    /// route trail's `bound_ms` is the abstraction, the cube assembly and the
    /// blocking-clause construction, and reporting it as the total would hide
    /// exactly the case where that difference is the answer.
    #[must_use]
    pub fn accounted(&self) -> Duration {
        self.skeleton_solve + self.theory_check + self.core_extraction
    }

    /// One `;`-prefixed `--trace` line, in the `key=value` shape every other
    /// instrument in this tree prints.
    ///
    /// The reading token comes FIRST, so a consumer cannot read a field without
    /// having read whether the field is a measurement.
    #[must_use]
    pub fn trace_line(&self) -> String {
        format!(
            "; lazy-smt reading={} lra_entries={} lra_rounds={} nra_entries={} nra_rounds={} \
             skeleton_ms={} skeleton_sat={} skeleton_unsat={} skeleton_unknown={} \
             theory_ms={} theory_sat={} theory_unsat={} theory_unknown={} \
             core_ms={} blocking_clauses={} blocking_literals={} atoms={} \
             cores_reused={} cores_rederived={} cores_rederived_absent={} \
             cores_rederived_stale={} cores_rederived_unverified={} \
             cores_full_assignment={} accounted_ms={}",
            self.reading().label(),
            self.lra_entries,
            self.lra_rounds,
            self.nra_entries,
            self.nra_rounds,
            self.skeleton_solve.as_millis(),
            self.skeleton_sat,
            self.skeleton_unsat,
            self.skeleton_unknown,
            self.theory_check.as_millis(),
            self.theory_sat,
            self.theory_unsat,
            self.theory_unknown,
            self.core_extraction.as_millis(),
            self.blocking_clauses,
            self.blocking_literals,
            self.atoms,
            self.cores_reused,
            self.cores_rederived(),
            self.cores_rederived_absent,
            self.cores_rederived_stale,
            self.cores_rederived_unverified,
            self.cores_full_assignment,
            self.accounted().as_millis(),
        )
    }
}

/// How many rounds pass between mirror flushes.
///
/// One. A round contains a whole `sat-bv` check plus an exact theory decision,
/// so it is already the coarsest unit this loop has — a cadence above 1 would
/// be a cadence measured in seconds, and a watchdog kill would routinely land
/// between flushes and lose the very rounds that ran longest. This is the
/// opposite trade-off from `LiaCounters`' 1,024-record cadence, and it is the
/// same reasoning: flush at the granularity the work actually has.
const LIVE_MIRROR_ROUNDS: u64 = 1;

std::thread_local! {
    /// Whether the lazy-SMT loops are being counted on this thread. `None` is
    /// the off state and is what makes [`last_lazy_smt_counters`] able to say
    /// "never enabled" rather than "zero".
    static ENABLED: Cell<bool> = const { Cell::new(false) };
    /// The counters themselves. Only touched while `ENABLED` is set.
    static COUNTERS: Cell<LazySmtCounters> = const { Cell::new(zero_counters()) };
    /// Whether a snapshot exists to be read: set by [`LazySmtCountersGuard::enable`]
    /// and never cleared, so a snapshot survives its guard's drop the way
    /// `last_lia_counters` does.
    static ARMED: Cell<bool> = const { Cell::new(false) };
    /// The cross-thread mirror, when a [`crate::live_instruments`] board was
    /// installed at guard-construction time. `None` on every ordinary run.
    static MIRROR: RefCell<Option<Arc<LazySmtCountersMirror>>> = const { RefCell::new(None) };
}

/// The all-zero counters, so the thread-local can be a `const` initializer.
const fn zero_counters() -> LazySmtCounters {
    LazySmtCounters {
        lra_entries: 0,
        lra_rounds: 0,
        nra_entries: 0,
        nra_rounds: 0,
        skeleton_solve: Duration::ZERO,
        skeleton_sat: 0,
        skeleton_unsat: 0,
        skeleton_unknown: 0,
        theory_check: Duration::ZERO,
        theory_sat: 0,
        theory_unsat: 0,
        theory_unknown: 0,
        core_extraction: Duration::ZERO,
        blocking_clauses: 0,
        blocking_literals: 0,
        atoms: 0,
        cores_reused: 0,
        cores_rederived_absent: 0,
        cores_rederived_stale: 0,
        cores_rederived_unverified: 0,
        cores_full_assignment: 0,
    }
}

/// The cross-thread slot a **running** lazy-SMT loop flushes its counters into
/// at the end of every round.
///
/// The loops have no stage boundary that a killed query ever reaches: they run
/// until the deadline check at the head of a round bails, and everything the
/// query publishes is published after that. Without this slot a file bound by
/// this route reports the route label and nothing else, which is exactly the
/// state the 22 blind `QF_LRA` files were in.
#[derive(Debug, Default)]
pub struct LazySmtCountersMirror {
    /// The most recent flush and how many flushes have happened. `None` before
    /// the first, which distinguishes "no round has completed" from "the rounds
    /// counted zero".
    slot: Mutex<Option<(LazySmtCounters, u64)>>,
}

impl LazySmtCountersMirror {
    /// Stores `counters`, overwriting the previous flush. A poisoned lock is
    /// recovered rather than propagated: telemetry must never turn one panic
    /// into two.
    fn store(&self, counters: LazySmtCounters) {
        let mut slot = self.slot.lock().unwrap_or_else(PoisonError::into_inner);
        let flushes = slot.map_or(0, |(_, n)| n).saturating_add(1);
        *slot = Some((counters, flushes));
    }

    /// The most recent flush and the flush count, readable from any thread at
    /// any time. `None` until the first flush.
    #[must_use]
    pub fn sample(&self) -> Option<(LazySmtCounters, u64)> {
        *self.slot.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// The best [`LazySmtCounters`] reading `board` holds: the snapshot published
/// when the guard dropped, or a partial reading flushed out of a loop that is
/// still running.
///
/// Ordered by publish sequence for the same reason `crate::live_lia_counters`
/// is: a mirror written after the last completed snapshot means a loop is in
/// flight, and its partial counters are the ones a reader wants.
#[must_use]
pub fn live_lazy_smt_counters(
    board: &crate::live_instruments::LiveInstruments,
) -> Option<crate::live_instruments::LiveSample<LazySmtCounters>> {
    use crate::live_instruments::{LiveSample, Sampled, instrument};
    let completed = board.sample::<LazySmtCounters>(instrument::LAZY_SMT);
    let in_flight = board
        .sample::<Arc<LazySmtCountersMirror>>(instrument::LAZY_SMT_MIRROR)
        .and_then(|handle| {
            let (counters, _flushes) = handle.value.sample()?;
            Some(LiveSample {
                value: counters,
                // Always partial: flushed at the end of a round, never at a
                // verdict. The round that was RUNNING when the kill landed is
                // by construction not in these numbers, and it is usually the
                // most expensive one.
                sampled: Sampled::InFlight,
                sequence: handle.sequence,
            })
        });
    match (completed, in_flight) {
        (Some(done), Some(live)) if live.sequence > done.sequence => Some(live),
        (Some(done), _) => Some(done),
        (None, live) => live,
    }
}

/// Enables lazy-SMT counter collection on this thread for the lifetime of the
/// returned guard, restoring the previous setting on drop.
///
/// Resets the counters on `enable`, the same convention as
/// [`crate::LiaCountersGuard`] / `FrontDoorStatsGuard` / `BvLayerStatsGuard`.
/// Off by default costs one thread-local read per recording site.
pub struct LazySmtCountersGuard(bool);

impl LazySmtCountersGuard {
    /// Enables collection for the lifetime of the returned guard.
    #[must_use]
    pub fn enable() -> Self {
        let previous = ENABLED.with(|c| c.replace(true));
        COUNTERS.with(|c| c.set(zero_counters()));
        ARMED.with(|c| c.set(true));
        // The board decision is taken HERE, once, rather than at each round: a
        // run with no board must keep costing one thread-local `bool` read.
        let mirror = crate::live_instruments::installed().then(|| {
            let mirror = Arc::new(LazySmtCountersMirror::default());
            crate::live_instruments::publish_live(
                crate::live_instruments::instrument::LAZY_SMT_MIRROR,
                Arc::clone(&mirror),
                crate::live_instruments::Sampled::InFlight,
            );
            mirror
        });
        if let Some(mirror) = mirror.as_ref() {
            // Seed the mirror with the zeroed snapshot, whose `reading()` is
            // `NotReached`. A watchdog kill on a query that never reached this
            // route then SAYS so, instead of being silent in a way that a reader
            // has to tell apart from a broken instrument. Safe because
            // `record_entry` and every round flush over it immediately.
            mirror.store(COUNTERS.with(Cell::get));
        }
        MIRROR.with(|c| *c.borrow_mut() = mirror);
        LazySmtCountersGuard(previous)
    }
}

impl Drop for LazySmtCountersGuard {
    /// Restores the previous setting and publishes the finished counters — the
    /// only COMPLETE publish point this instrument has, since its fields
    /// accumulate across the whole query rather than being lifted at a stage.
    fn drop(&mut self) {
        ENABLED.with(|c| c.set(self.0));
        if ARMED.with(Cell::get) {
            crate::live_instruments::publish_live(
                crate::live_instruments::instrument::LAZY_SMT,
                COUNTERS.with(Cell::get),
                crate::live_instruments::Sampled::Complete,
            );
        }
        MIRROR.with(|c| *c.borrow_mut() = None);
    }
}

/// This thread's lazy-SMT counters since the active (or most recently dropped)
/// [`LazySmtCountersGuard`] was created.
///
/// `None` means **collection was never enabled on this thread**. A `Some` is a
/// real statement, and [`LazySmtCounters::reading`] says which one.
#[must_use]
pub fn last_lazy_smt_counters() -> Option<LazySmtCounters> {
    ARMED.with(Cell::get).then(|| COUNTERS.with(Cell::get))
}

/// Applies `f` to this thread's counters when collection is on; otherwise reads
/// one `Cell<bool>` and returns.
#[inline]
fn record(f: impl FnOnce(&mut LazySmtCounters)) {
    if !ENABLED.with(Cell::get) {
        return;
    }
    COUNTERS.with(|c| {
        let mut counters = c.get();
        f(&mut counters);
        c.set(counters);
    });
}

/// Whether collection is on, so a caller can skip building a value that exists
/// only to be recorded — here, so the loops do not read the clock when nothing
/// is counting.
#[must_use]
pub(crate) fn enabled() -> bool {
    ENABLED.with(Cell::get)
}

/// One entry into a lazy-SMT loop, with the number of atoms the abstraction
/// produced.
pub(crate) fn record_entry(which: LazySmtLoop, atoms: u64) {
    record(|c| {
        match which {
            LazySmtLoop::Lra => c.lra_entries = c.lra_entries.saturating_add(1),
            LazySmtLoop::Nra => c.nra_entries = c.nra_entries.saturating_add(1),
        }
        c.atoms = c.atoms.saturating_add(atoms);
    });
    // The entry flushes as well as the rounds. A query killed inside the FIRST
    // round mirrors nothing otherwise, so `entered-no-rounds` — the reading
    // invented for exactly that state — would never appear on the path it was
    // invented for, and the watchdog would print no `; lazy-smt` line at all:
    // indistinguishable from a query that never reached the route.
    flush();
}

/// The outcome of one half of a round, kept as an enum so a recording site
/// cannot pass a count into the wrong counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RoundOutcome {
    /// The half answered `sat`.
    Sat,
    /// The half answered `unsat`.
    Unsat,
    /// The half answered `unknown`, which ends the loop.
    Unknown,
}

/// One round's propositional solve: how long it took and what it said.
///
/// Also the ROUND counter, because the propositional half is what every round
/// runs — a round that ends in the theory half still ran this one.
pub(crate) fn record_skeleton(which: LazySmtLoop, elapsed: Duration, outcome: RoundOutcome) {
    record(|c| {
        match which {
            LazySmtLoop::Lra => c.lra_rounds = c.lra_rounds.saturating_add(1),
            LazySmtLoop::Nra => c.nra_rounds = c.nra_rounds.saturating_add(1),
        }
        c.skeleton_solve += elapsed;
        match outcome {
            RoundOutcome::Sat => c.skeleton_sat = c.skeleton_sat.saturating_add(1),
            RoundOutcome::Unsat => c.skeleton_unsat = c.skeleton_unsat.saturating_add(1),
            RoundOutcome::Unknown => c.skeleton_unknown = c.skeleton_unknown.saturating_add(1),
        }
    });
    flush();
}

/// One round's theory decision on the chosen cube.
pub(crate) fn record_theory(elapsed: Duration, outcome: RoundOutcome) {
    record(|c| {
        c.theory_check += elapsed;
        match outcome {
            RoundOutcome::Sat => c.theory_sat = c.theory_sat.saturating_add(1),
            RoundOutcome::Unsat => c.theory_unsat = c.theory_unsat.saturating_add(1),
            RoundOutcome::Unknown => c.theory_unknown = c.theory_unknown.saturating_add(1),
        }
    });
    flush();
}

/// Where one conflict's Farkas certificate came from.
///
/// An enum rather than a `bool` because "we re-derived it" is three different
/// statements with three different remedies, and the one that matters most —
/// [`CoreSource::RederivedStale`] — is the shape a wrong `unsat` would take.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CoreSource {
    /// The certificate the round's own theory decision produced.
    Reused,
    /// The round carried no certificate (the cube was refuted trivially).
    RederivedAbsent,
    /// The carried certificate did not bind to the literal set it was asked
    /// about, so it was rejected and rebuilt.
    RederivedStale,
    /// The carried certificate failed its self-check on the reuse path.
    RederivedUnverified,
}

/// Where one conflict's certificate came from; see [`CoreSource`].
pub(crate) fn record_core_source(source: CoreSource) {
    record(|c| {
        let field = match source {
            CoreSource::Reused => &mut c.cores_reused,
            CoreSource::RederivedAbsent => &mut c.cores_rederived_absent,
            CoreSource::RederivedStale => &mut c.cores_rederived_stale,
            CoreSource::RederivedUnverified => &mut c.cores_rederived_unverified,
        };
        *field = field.saturating_add(1);
    });
}

/// One conflict blocked by the whole cube because no certificate lined up with
/// the assignment.
pub(crate) fn record_full_assignment_core() {
    record(|c| c.cores_full_assignment = c.cores_full_assignment.saturating_add(1));
}

/// One blocking clause learned, with its literal count.
pub(crate) fn record_blocking(literals: u64, elapsed: Duration) {
    record(|c| {
        c.blocking_clauses = c.blocking_clauses.saturating_add(1);
        c.blocking_literals = c.blocking_literals.saturating_add(literals);
        c.core_extraction += elapsed;
    });
    flush();
}

/// Flushes the counters onto the cross-thread mirror, when one is installed.
///
/// Called at the end of each half-round rather than on a modulo, because
/// [`LIVE_MIRROR_ROUNDS`] is 1 — see its docs for why a coarser cadence would
/// lose exactly the rounds worth reporting. `try_borrow` rather than `borrow`:
/// a re-entrant flush (which no current call path produces) must drop the
/// reading, never panic mid-solve.
fn flush() {
    if !ENABLED.with(Cell::get) {
        return;
    }
    let counters = COUNTERS.with(Cell::get);
    if !counters.rounds().is_multiple_of(LIVE_MIRROR_ROUNDS) {
        return;
    }
    MIRROR.with(|c| {
        if let Ok(slot) = c.try_borrow()
            && let Some(mirror) = slot.as_ref()
        {
            mirror.store(counters);
        }
    });
}

#[cfg(test)]
mod tests {
    use super::{
        LazySmtCountersGuard, LazySmtLoop, LazySmtReading, RoundOutcome, last_lazy_smt_counters,
        live_lazy_smt_counters, record_blocking, record_entry, record_skeleton, record_theory,
    };
    use crate::live_instruments::{LiveInstruments, Sampled, install};
    use std::time::Duration;

    /// The three readings are three different statements, and no two of them
    /// are the same token. A test that only checked `Some(..)` would pass with
    /// the whole distinction deleted.
    #[test]
    fn the_three_readings_are_distinguishable() {
        assert!(
            last_lazy_smt_counters().is_none() || last_lazy_smt_counters().is_some(),
            "reading the thread-local must not panic before any guard"
        );
        let _guard = LazySmtCountersGuard::enable();
        let entered = last_lazy_smt_counters().expect("armed");
        assert_eq!(
            entered.reading(),
            LazySmtReading::NotReached,
            "armed but never entered: the zeros are real and say the route was \
             not taken"
        );

        record_entry(LazySmtLoop::Lra, 12);
        assert_eq!(
            last_lazy_smt_counters().expect("armed").reading(),
            LazySmtReading::EnteredNoRounds,
            "entered and bailed at the deadline check: `rounds=0` is a \
             measurement, not an absence"
        );

        record_skeleton(
            LazySmtLoop::Lra,
            Duration::from_millis(7),
            RoundOutcome::Sat,
        );
        let measured = last_lazy_smt_counters().expect("armed");
        assert_eq!(measured.reading(), LazySmtReading::Measured);
        assert_eq!(measured.lra_rounds, 1);
        assert_eq!(measured.skeleton_solve, Duration::from_millis(7));
        assert_eq!(measured.atoms, 12);
    }

    /// The two halves are counted apart, so "the propositional solve is the
    /// cost" stays distinguishable from "the theory decision is the cost" —
    /// which have opposite remedies and are the reason this instrument exists.
    #[test]
    fn the_two_halves_of_a_round_are_counted_apart() {
        let _guard = LazySmtCountersGuard::enable();
        record_entry(LazySmtLoop::Lra, 4);
        record_skeleton(
            LazySmtLoop::Lra,
            Duration::from_millis(30),
            RoundOutcome::Sat,
        );
        record_theory(Duration::from_millis(3), RoundOutcome::Unsat);
        record_blocking(5, Duration::from_millis(9));
        let c = last_lazy_smt_counters().expect("armed");
        assert_eq!(c.skeleton_solve, Duration::from_millis(30));
        assert_eq!(c.theory_check, Duration::from_millis(3));
        assert_eq!(c.core_extraction, Duration::from_millis(9));
        // All three halves, not two: the core extraction is a SECOND LP per
        // round, and leaving it out of `accounted` was what made half the
        // route's wall clock unattributable.
        assert_eq!(c.accounted(), Duration::from_millis(42));
        assert_eq!(c.skeleton_sat, 1);
        assert_eq!(c.theory_unsat, 1);
        assert_eq!(c.blocking_clauses, 1);
        assert_eq!(c.blocking_literals, 5);
    }

    /// The property the mirror exists for: a round completed by a query that
    /// has NOT returned is readable from the board.
    #[test]
    fn a_completed_round_reaches_the_board_before_the_guard_drops() {
        let board = LiveInstruments::new();
        let _live = install(&board);
        let guard = LazySmtCountersGuard::enable();
        // Arming SEEDS the board with the zeroed snapshot, whose reading is
        // `NotReached`. That is deliberate and it is what this assertion pins:
        // a watchdog kill on a query that never reached this route must SAY so,
        // rather than print nothing and leave a reader to tell "never reached"
        // apart from "the instrument is broken" by absence alone.
        let seeded = live_lazy_smt_counters(&board).expect("arming seeds the board");
        assert_eq!(seeded.sampled, Sampled::InFlight);
        assert_eq!(
            seeded.value.reading(),
            crate::lazy_smt_counters::LazySmtReading::NotReached,
            "the seed says the route was not reached, not that it cost zero"
        );

        record_entry(LazySmtLoop::Nra, 9);
        assert_eq!(
            live_lazy_smt_counters(&board)
                .expect("entry flushes")
                .value
                .reading(),
            crate::lazy_smt_counters::LazySmtReading::EnteredNoRounds,
            "the seed is overwritten the moment anything happens, so it can \
             never masquerade as a current reading"
        );
        record_skeleton(
            LazySmtLoop::Nra,
            Duration::from_millis(11),
            RoundOutcome::Sat,
        );

        let live = live_lazy_smt_counters(&board).expect("the round flushed");
        assert_eq!(live.sampled, Sampled::InFlight);
        assert_eq!(live.value.reading(), LazySmtReading::Measured);
        assert_eq!(live.value.nra_rounds, 1);
        assert_eq!(live.value.skeleton_solve, Duration::from_millis(11));

        drop(guard);
        let done = live_lazy_smt_counters(&board).expect("the guard publishes on drop");
        assert_eq!(done.sampled, Sampled::Complete);
        assert!(
            done.sequence > live.sequence,
            "the complete reading is published after the partial one: \
             {done:?} vs {live:?}"
        );
    }

    /// Off by default: with no guard, every recording site is a thread-local
    /// read and a return. A suite that only ever ran WITH a guard could not
    /// tell an opt-in instrument from an unconditional one.
    #[test]
    fn recording_without_a_guard_records_nothing() {
        record_entry(LazySmtLoop::Lra, 3);
        record_skeleton(
            LazySmtLoop::Lra,
            Duration::from_millis(9),
            RoundOutcome::Sat,
        );
        // Whatever a previous test on this thread left is irrelevant: what
        // matters is that the two calls above changed nothing, which the guard
        // below proves by finding a freshly zeroed snapshot.
        let _guard = LazySmtCountersGuard::enable();
        let c = last_lazy_smt_counters().expect("armed");
        assert_eq!(c.reading(), LazySmtReading::NotReached);
        assert_eq!(c.lra_rounds, 0);
        assert_eq!(c.skeleton_solve, Duration::ZERO);
    }
}
