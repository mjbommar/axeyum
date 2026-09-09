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
//! That route is `crate::dpll_t::check_with_lra_dpll_within`'s abstraction /
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
use std::fmt::Write as _;
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

/// Which of the three lazy-SMT loops a recording belongs to.
///
/// Counted separately because they are different deciders behind one route
/// label: the linear loop decides each cube with the exact-rational
/// `check_with_lra_within`, the nonlinear one with the sign-cell CAD, and the
/// integer one re-solves a whole linear relaxation per round. Summing them
/// would produce a "theory check" total whose mean says nothing about any of
/// the three engines.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LazySmtLoop {
    /// `crate::dpll_t::check_with_lra_dpll_within`, linear real arithmetic.
    Lra,
    /// `check_with_nra_dpll_within`, nonlinear real arithmetic over the CAD.
    Nra,
    /// `crate::nia_linearize::solve_with_refinement`, the integer
    /// **incremental-linearization** loop: each round re-solves the linear
    /// relaxation and, on a spurious model, cuts it off with tangent-plane
    /// lemmas.
    ///
    /// Added 2026-09-08 because it was the loop the `QF_NIA` files actually
    /// spend their budget in and the only one of the three with no instrument
    /// at all. The 2026-09-08 span-log sweep read "all 50 `QF_NIA` files enter
    /// the refinement loop, 25 of them for exactly one round" off
    /// [`LazySmtLoop::Nra`] — a *different* loop, reached from
    /// `int_real_relax::refute_int_via_real_relaxation` before the nonlinear
    /// integer route is entered at all. Two loops behind one span is how that
    /// happened; three named arms is the fix.
    Nia,
}

impl LazySmtLoop {
    /// Index into [`LazySmtCounters::round_hist`]. `as usize` on the enum would
    /// do the same thing and would silently follow a reordering of the
    /// variants; this will not compile through one.
    #[must_use]
    pub const fn index(self) -> usize {
        match self {
            LazySmtLoop::Lra => 0,
            LazySmtLoop::Nra => 1,
            LazySmtLoop::Nia => 2,
        }
    }

    /// The token a report line prints for this loop.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            LazySmtLoop::Lra => "lra",
            LazySmtLoop::Nra => "nra",
            LazySmtLoop::Nia => "nia",
        }
    }

    /// The three loops in [`LazySmtLoop::index`] order, so a consumer that
    /// walks the histograms cannot disagree with the recorder about which slot
    /// is which.
    pub const ALL: [LazySmtLoop; LAZY_SMT_LOOPS] =
        [LazySmtLoop::Lra, LazySmtLoop::Nra, LazySmtLoop::Nia];
}

/// How many distinct lazy-SMT loops [`LazySmtCounters`] keeps a histogram for.
pub const LAZY_SMT_LOOPS: usize = 3;

/// Buckets in a `RoundHistogram`: bucket `0` is `<1 ms`, bucket `k` is
/// `[2^(k-1), 2^k)` ms for `1 <= k <= 14`, and bucket `15` is the saturating
/// tail `>= 2^14 ms = 16.4 s` — so the standard 24 s budget lands inside the
/// range rather than at its edge.
pub const ROUND_BUCKETS: usize = 16;

/// The per-round wall-clock **distribution** of one refinement loop.
///
/// # Why a distribution and not a mean
///
/// A refinement loop's round count and its round cost need opposite fixes and,
/// until this existed, looked identical from outside: a route that returned
/// `unknown` after 24 s reported one number, `rounds`, and a consumer was left
/// to guess whether that was four enormous rounds or forty thousand small ones.
/// The 2026-09-08 span log went one step further and reported `loop_hist: null`
/// with `loop_hist_available: false` — an honest refusal, and the gap this type
/// closes.
///
/// The measurement that made it decisive: 25 of 50 `QF_NIA` files ran exactly
/// one round of the [`LazySmtLoop::Nra`] loop, and the question "is that round
/// enormous, or is the loop not iterating" had no answer in the data. It has a
/// third answer, which a histogram shows at a glance — those 25 single rounds
/// all land in the **same bucket**, because each is exactly the size of the
/// slice that loop's caller was handed
/// (`auto::INT_REAL_RELAX_BUDGET_SHARE`, 24 s / 6 = 4.00 s; 23 of the 25 fall
/// between 3.993 and 4.009 s). A count cannot say that; a bucketed
/// distribution says it without a per-round log.
///
/// # Clock-free
///
/// This type reads no clock. It is fed the per-stage durations the loops
/// already measure (and only measure when counting is armed), summed over one
/// round — so arming the histogram adds no clock read anywhere, and disarming
/// it costs the same single thread-local `bool` read as the rest of this
/// module.
///
/// # Fixed size
///
/// [`LazySmtCounters`] lives in a `Cell` and is `Copy`, so a histogram here
/// cannot allocate. Log2 buckets give the full dynamic range from a
/// microsecond round to a whole budget in 16 `u32`s.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct RoundHistogram {
    buckets: [u32; ROUND_BUCKETS],
    rounds: u32,
    total_ns: u64,
    max_ns: u64,
    max_round: u32,
}

impl RoundHistogram {
    /// The bucket a duration falls in; see [`ROUND_BUCKETS`].
    #[must_use]
    pub fn bucket_of(elapsed: Duration) -> usize {
        let ms = elapsed.as_millis();
        if ms == 0 {
            return 0;
        }
        // `k` such that `2^(k-1) <= ms < 2^k`, clamped to the tail bucket.
        let k = 128 - u128::leading_zeros(ms) as usize;
        k.min(ROUND_BUCKETS - 1)
    }

    /// Files one completed round.
    fn record(&mut self, elapsed: Duration) {
        let slot = Self::bucket_of(elapsed);
        self.buckets[slot] = self.buckets[slot].saturating_add(1);
        self.rounds = self.rounds.saturating_add(1);
        let ns = u64::try_from(elapsed.as_nanos()).unwrap_or(u64::MAX);
        self.total_ns = self.total_ns.saturating_add(ns);
        if ns > self.max_ns {
            self.max_ns = ns;
            self.max_round = self.rounds;
        }
    }

    /// Rounds filed. **Not** the loop's round count: a round whose stages were
    /// never timed (counting armed mid-loop) is not here, and the loop's own
    /// `*_rounds` counter is the authority on how many rounds ran.
    #[must_use]
    pub const fn rounds(&self) -> u32 {
        self.rounds
    }

    /// The per-bucket counts, bucket `0` first.
    #[must_use]
    pub const fn buckets(&self) -> &[u32; ROUND_BUCKETS] {
        &self.buckets
    }

    /// The longest round filed.
    #[must_use]
    pub const fn max(&self) -> Duration {
        Duration::from_nanos(self.max_ns)
    }

    /// Which round (1-based) was the longest.
    #[must_use]
    pub const fn max_round(&self) -> u32 {
        self.max_round
    }

    /// Total time across filed rounds.
    #[must_use]
    pub const fn total(&self) -> Duration {
        Duration::from_nanos(self.total_ns)
    }

    /// Whether anything was filed. A consumer must check this before quoting
    /// any other method — an all-zero histogram and a loop that never ran are
    /// the same bytes, and only the caller's `*_entries` can tell them apart.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.rounds == 0
    }

    /// The non-empty buckets as `index:count`, comma-separated — the compact
    /// form a `--trace` line and a span-log `loop_hist` both carry.
    ///
    /// Empty string when nothing was filed, so a reader never mistakes an
    /// absent distribution for a distribution concentrated at zero.
    #[must_use]
    pub fn compact(&self) -> String {
        let mut out = String::new();
        for (i, &count) in self.buckets.iter().enumerate() {
            if count == 0 {
                continue;
            }
            if !out.is_empty() {
                out.push(',');
            }
            let _ = write!(out, "{i}:{count}");
        }
        out
    }
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
    /// Calls into the integer incremental-linearization loop
    /// ([`LazySmtLoop::Nia`]).
    pub nia_entries: u64,
    /// Refinement rounds that loop completed the relaxation solve of.
    pub nia_rounds: u64,

    /// Per-round wall-clock distribution, one histogram per loop, indexed by
    /// `LazySmtLoop::index`. See `RoundHistogram` for why a distribution and
    /// not a mean, and [`LazySmtCounters::hist`] for the accessor that keeps
    /// the index honest.
    ///
    /// Filed from the stage clocks the loops already take, so this adds no
    /// clock read; a round is filed when the NEXT round opens or when the
    /// guard drops, and the round in flight at a watchdog kill is
    /// [`LazySmtCounters::pending_round`] instead of being lost.
    pub round_hist: [RoundHistogram; LAZY_SMT_LOOPS],
    /// The stage time accumulated by the round that has not been filed yet.
    ///
    /// Non-zero in a mirror sample taken mid-round — which, on a watchdog kill,
    /// is every sample that matters. It is a PARTIAL round: the stages that had
    /// finished when the sample was taken, not the round's eventual cost.
    pub pending_round: Duration,
    /// Which loop [`Self::pending_round`] belongs to, by
    /// `LazySmtLoop::index`. Meaningless when `pending_round` is zero.
    pub pending_loop: usize,

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

    /// Literals whose polarity differs from the PREVIOUS round's cube, summed
    /// over rounds that had a predecessor.
    ///
    /// The question the Farkas fix left open. With the second LP gone the loop
    /// runs 1.63x the rounds and still loses, so either each round buys little
    /// or the rounds repeat each other. `cube_flips / (rounds - entries)` is the
    /// mean churn: near [`Self::atoms`] means every round hands the theory a
    /// genuinely different problem and there is nothing to warm-start; a
    /// handful means round *n+1* differs from round *n* in a few bounds and the
    /// cold re-decision is redundant work, not search.
    pub cube_flips: u64,
    /// Rounds whose cube is IDENTICAL to the previous round's.
    ///
    /// A tripwire, not a statistic: the blocking clause learned from a cube
    /// falsifies that cube, so the propositional half cannot legitimately hand
    /// back the same one. Any non-zero reading means a learned clause did not
    /// reach the skeleton solve.
    pub cube_identical: u64,

    /// Calls into the conjunctive `QF_LRA` decision that were counted, i.e. the
    /// denominator for the three stage timings below.
    ///
    /// Not the same as [`Self::theory_check`]'s round count: this counts every
    /// `crate::lra::decide_within` under the armed guard, which on the
    /// lazy-SMT route is one per round but on any other route is whatever that
    /// route does. Read the two together before dividing.
    pub cube_decisions: u64,
    /// Time turning the cube's literals into linear constraints, summed.
    pub cube_collect: Duration,
    /// Time inside Fourier–Motzkin, summed — the FIRST thing the conjunctive
    /// decision tries, on the whole cube.
    pub cube_fm: Duration,
    /// Fourier–Motzkin runs that gave up (size guard or deadline) and handed
    /// the cube to the simplex fallback.
    ///
    /// Read against [`Self::cube_decisions`]: at a ratio near 1 the elimination
    /// is pure overhead on this population and the fallback is the real
    /// decider, which is a routing question, not a simplex question.
    pub cube_fm_declines: u64,
    /// Time inside the exact-rational simplex fallback, summed.
    pub cube_simplex: Duration,
    /// Simplex fallback calls.
    pub cube_simplex_calls: u64,
    /// Decisions that built the dense `n x n` Farkas multiplier matrix.
    ///
    /// The largest allocation on this route — `32*n^2` bytes, the one
    /// `lra::fm_admission` exists to price after three `QF_LRA` files reached
    /// 26.6 GB under an 8 GiB flag — and the one the simplex-first arm skips
    /// entirely rather than merely pricing. Counted because "the matrix was not
    /// built" is otherwise not observable from outside `lra::decide_within`,
    /// and an ORDER that no test can see is an order the next refactor undoes.
    pub cube_matrices: u64,

    /// What the online CDCL(T) LRA probe at the head of the linear loop did.
    ///
    /// The loop below that probe is the WEAK route: offline lazy SMT with total
    /// assignments and a cold theory decision per round. A file only reaches it
    /// because the probe declined, and the probe's `CheckResult::Unknown` reason
    /// was discarded at the call site, so nothing said which decline it was.
    /// The remedies are disjoint — an admission screen is a budget number, an
    /// unsupported skeleton is an encoder gap — so this is recorded as an enum
    /// rather than a count.
    pub online_probe: OnlineProbe,
}

/// What the online CDCL(T) LRA probe at the head of
/// `crate::dpll_t::check_with_lra_dpll_within` did with the query.
///
/// Every variant except [`OnlineProbe::Took`] means the query fell through to
/// the offline refinement loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OnlineProbe {
    /// The probe was never run (no lazy-SMT entry, or the NRA loop).
    #[default]
    NotProbed,
    /// The probe answered `sat`/`unsat`, or timed out owning the budget: the
    /// offline loop was never entered.
    Took,
    /// No linear-real atoms to register.
    NoAtoms,
    /// The Boolean skeleton contains structure the online encoder does not
    /// cover, so it declined before building a theory.
    SkeletonUnsupported,
    /// The atom count exceeded what the memory budget admits (ADR-1752's outer
    /// screen).
    AdmissionScreen,
    /// Theory construction hit the normalization node ceiling.
    BuildNodeCeiling,
    /// Theory construction's own memory projection exceeded the budget.
    BuildMemoryBudget,
    /// The driver answered `sat` but the model did not replay against the
    /// original assertions.
    ModelDidNotReplay,
}

impl OnlineProbe {
    /// The token this variant prints in the `--trace` line.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            OnlineProbe::NotProbed => "not-probed",
            OnlineProbe::Took => "took",
            OnlineProbe::NoAtoms => "no-atoms",
            OnlineProbe::SkeletonUnsupported => "skeleton-unsupported",
            OnlineProbe::AdmissionScreen => "admission-screen",
            OnlineProbe::BuildNodeCeiling => "build-node-ceiling",
            OnlineProbe::BuildMemoryBudget => "build-memory-budget",
            OnlineProbe::ModelDidNotReplay => "model-did-not-replay",
        }
    }
}

impl LazySmtCounters {
    /// Which of the three statements this snapshot is making; see
    /// [`LazySmtReading`].
    #[must_use]
    pub fn reading(&self) -> LazySmtReading {
        if self.entries() == 0 {
            LazySmtReading::NotReached
        } else if self.rounds() == 0 {
            LazySmtReading::EnteredNoRounds
        } else {
            LazySmtReading::Measured
        }
    }

    /// Entries across all three loops.
    #[must_use]
    pub fn entries(&self) -> u64 {
        self.lra_entries
            .saturating_add(self.nra_entries)
            .saturating_add(self.nia_entries)
    }

    /// Rounds across all three loops.
    #[must_use]
    pub fn rounds(&self) -> u64 {
        self.lra_rounds
            .saturating_add(self.nra_rounds)
            .saturating_add(self.nia_rounds)
    }

    /// Entries into one loop.
    #[must_use]
    pub fn entries_of(&self, which: LazySmtLoop) -> u64 {
        match which {
            LazySmtLoop::Lra => self.lra_entries,
            LazySmtLoop::Nra => self.nra_entries,
            LazySmtLoop::Nia => self.nia_entries,
        }
    }

    /// Rounds in one loop.
    #[must_use]
    pub fn rounds_of(&self, which: LazySmtLoop) -> u64 {
        match which {
            LazySmtLoop::Lra => self.lra_rounds,
            LazySmtLoop::Nra => self.nra_rounds,
            LazySmtLoop::Nia => self.nia_rounds,
        }
    }

    /// One loop's per-round distribution.
    ///
    /// The accessor exists so no consumer indexes `round_hist` with a literal:
    /// a slot chosen by hand is a slot that can disagree with the recorder, and
    /// a histogram attributed to the wrong loop is worse than none.
    #[must_use]
    pub fn hist(&self, which: LazySmtLoop) -> &RoundHistogram {
        &self.round_hist[which.index()]
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

    /// The three per-round distributions in `key=value` shape, one group per
    /// loop: `<loop>_hist=<bucket:count,...> <loop>_max_ms=<n>
    /// <loop>_max_round=<n>`.
    ///
    /// A loop with nothing filed prints `<loop>_hist=-`, not an empty value: an
    /// absent distribution and a distribution concentrated in bucket 0 are
    /// different statements and a reader must not have to tell them apart by
    /// whitespace.
    #[must_use]
    pub fn hist_line(&self) -> String {
        let mut out = String::new();
        for which in LazySmtLoop::ALL {
            let hist = self.hist(which);
            let name = which.label();
            if !out.is_empty() {
                out.push(' ');
            }
            let compact = if hist.is_empty() {
                "-".to_owned()
            } else {
                hist.compact()
            };
            let _ = write!(
                out,
                "{name}_hist={compact} {name}_max_ms={} {name}_max_round={}",
                hist.max().as_millis(),
                hist.max_round(),
            );
        }
        out
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
             nia_entries={} nia_rounds={} {} pending_round_ms={} \
             skeleton_ms={} skeleton_sat={} skeleton_unsat={} skeleton_unknown={} \
             theory_ms={} theory_sat={} theory_unsat={} theory_unknown={} \
             core_ms={} blocking_clauses={} blocking_literals={} atoms={} \
             cores_reused={} cores_rederived={} cores_rederived_absent={} \
             cores_rederived_stale={} cores_rederived_unverified={} \
             cores_full_assignment={} accounted_ms={} \
             cube_flips={} cube_identical={} cube_decisions={} cube_collect_ms={} \
             cube_fm_ms={} cube_fm_declines={} cube_simplex_ms={} cube_simplex_calls={} \
             cube_matrices={} online_probe={}",
            self.reading().label(),
            self.lra_entries,
            self.lra_rounds,
            self.nra_entries,
            self.nra_rounds,
            self.nia_entries,
            self.nia_rounds,
            self.hist_line(),
            self.pending_round.as_millis(),
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
            self.cube_flips,
            self.cube_identical,
            self.cube_decisions,
            self.cube_collect.as_millis(),
            self.cube_fm.as_millis(),
            self.cube_fm_declines,
            self.cube_simplex.as_millis(),
            self.cube_simplex_calls,
            self.cube_matrices,
            self.online_probe.label(),
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
/// A zeroed histogram, so [`zero_counters`] stays `const` (`Default` is not).
const ZERO_HISTOGRAM: RoundHistogram = RoundHistogram {
    buckets: [0; ROUND_BUCKETS],
    rounds: 0,
    total_ns: 0,
    max_ns: 0,
    max_round: 0,
};

const fn zero_counters() -> LazySmtCounters {
    LazySmtCounters {
        lra_entries: 0,
        lra_rounds: 0,
        nra_entries: 0,
        nra_rounds: 0,
        nia_entries: 0,
        nia_rounds: 0,
        round_hist: [ZERO_HISTOGRAM; LAZY_SMT_LOOPS],
        pending_round: Duration::ZERO,
        pending_loop: 0,
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
        cube_flips: 0,
        cube_identical: 0,
        cube_decisions: 0,
        cube_collect: Duration::ZERO,
        cube_fm: Duration::ZERO,
        cube_fm_declines: 0,
        cube_simplex: Duration::ZERO,
        cube_simplex_calls: 0,
        cube_matrices: 0,
        online_probe: OnlineProbe::NotProbed,
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
    fn store(&self, counters: &LazySmtCounters) {
        let mut slot = self.slot.lock().unwrap_or_else(PoisonError::into_inner);
        let flushes = slot.map_or(0, |(_, n)| n).saturating_add(1);
        *slot = Some((*counters, flushes));
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
            mirror.store(&COUNTERS.with(Cell::get));
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
        // The loop's LAST round closes here and nowhere else: it exits between
        // its two halves, so no later `record_skeleton` will ever file it.
        // Without this the histogram is systematically missing exactly the
        // round that ended the loop — which, on a route bound by its budget, is
        // the round that spent it.
        COUNTERS.with(|c| {
            let mut counters = c.get();
            file_pending(&mut counters);
            c.set(counters);
        });
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
///
/// # The pending round is FOLDED IN here, and only here
///
/// A round is filed into its histogram when the next one opens or the guard
/// drops, so a loop's LAST round has no closing event until the query ends.
/// This is the *completed-query* read — every caller takes it after the solve
/// returned — so folding is what the data actually says, and not folding made
/// the common case report `nia_hist=-` on a loop that had just run a round
/// (measured on `QF_NIA` file 34, 2026-09-08: one 6.7 s round, invisible).
///
/// [`live_lazy_smt_counters`] deliberately does NOT fold: that read happens
/// *during* the solve, where the pending round is a PARTIAL round and filing it
/// would put a lower bound into a bucket as if it were the round's cost. The
/// two reads correspond exactly to the span log's `Complete` and `InFlight`
/// samplings, which is why they differ here rather than at the call site.
#[must_use]
pub fn last_lazy_smt_counters() -> Option<LazySmtCounters> {
    ARMED.with(Cell::get).then(|| {
        let mut counters = COUNTERS.with(Cell::get);
        file_pending(&mut counters);
        counters
    })
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

/// Files the round now complete into its loop's histogram and clears the
/// pending slot.
///
/// Called at the three points a round CLOSES on the live counters: the opening
/// of the next one ([`record_skeleton`]), a fresh loop entry
/// ([`record_entry`]), and the guard's drop. A loop that exits between its two
/// halves closes its last round at none of the first two, which is why the
/// guard's drop is one of them.
///
/// [`last_lazy_smt_counters`] applies it to a COPY as well, so a read taken
/// while the guard is still alive — which is every `--trace` read — sees the
/// finished round rather than an empty distribution beside a non-zero round
/// count. [`live_lazy_smt_counters`] deliberately does not: there the pending
/// round is partial.
fn file_pending(c: &mut LazySmtCounters) {
    if c.pending_round.is_zero() {
        return;
    }
    let slot = c.pending_loop.min(LAZY_SMT_LOOPS - 1);
    let pending = c.pending_round;
    c.round_hist[slot].record(pending);
    c.pending_round = Duration::ZERO;
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
        // A nested entry (one loop calling into another) would otherwise file
        // the outer loop's half-round against the inner one's histogram.
        file_pending(c);
        match which {
            LazySmtLoop::Lra => c.lra_entries = c.lra_entries.saturating_add(1),
            LazySmtLoop::Nra => c.nra_entries = c.nra_entries.saturating_add(1),
            LazySmtLoop::Nia => c.nia_entries = c.nia_entries.saturating_add(1),
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
        // The propositional solve OPENS a round, so this is where the previous
        // one is complete and can be filed. See [`file_pending`].
        file_pending(c);
        c.pending_loop = which.index();
        c.pending_round = elapsed;
        match which {
            LazySmtLoop::Lra => c.lra_rounds = c.lra_rounds.saturating_add(1),
            LazySmtLoop::Nra => c.nra_rounds = c.nra_rounds.saturating_add(1),
            LazySmtLoop::Nia => c.nia_rounds = c.nia_rounds.saturating_add(1),
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
        c.pending_round += elapsed;
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

/// One round's cube churn against the previous round's, and whether the two
/// were identical.
///
/// `flips` is the Hamming distance over the atom assignment. The first round of
/// an entry has no predecessor and must not be recorded.
pub(crate) fn record_cube_churn(flips: u64) {
    record(|c| {
        c.cube_flips = c.cube_flips.saturating_add(flips);
        if flips == 0 {
            c.cube_identical = c.cube_identical.saturating_add(1);
        }
    });
}

/// One conjunctive `QF_LRA` decision, split into the three stages the decider
/// actually has.
///
/// `simplex` is `None` when Fourier–Motzkin decided the system itself, so
/// `cube_simplex_calls` counts fallbacks rather than decisions.
pub(crate) fn record_cube_stages(
    collect: Duration,
    fm: Duration,
    fm_declined: bool,
    simplex: Option<Duration>,
    matrix_built: bool,
) {
    record(|c| {
        c.cube_decisions = c.cube_decisions.saturating_add(1);
        c.cube_collect += collect;
        c.cube_fm += fm;
        if fm_declined {
            c.cube_fm_declines = c.cube_fm_declines.saturating_add(1);
        }
        if let Some(simplex) = simplex {
            c.cube_simplex += simplex;
            c.cube_simplex_calls = c.cube_simplex_calls.saturating_add(1);
        }
        if matrix_built {
            c.cube_matrices = c.cube_matrices.saturating_add(1);
        }
    });
}

/// What the online CDCL(T) LRA probe did with the query; see [`OnlineProbe`].
pub(crate) fn record_online_probe(outcome: OnlineProbe) {
    record(|c| c.online_probe = outcome);
}

/// One conflict blocked by the whole cube because no certificate lined up with
/// the assignment.
pub(crate) fn record_full_assignment_core() {
    record(|c| c.cores_full_assignment = c.cores_full_assignment.saturating_add(1));
}

/// One blocking clause learned, with its literal count.
pub(crate) fn record_blocking(literals: u64, elapsed: Duration) {
    record(|c| {
        c.pending_round += elapsed;
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
            mirror.store(&counters);
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
    /// A loop's LAST round has no closing event of its own, so the two reads
    /// must disagree about it -- and the disagreement is the point.
    ///
    /// The in-flight read (the watchdog path) must show it PENDING and keep it
    /// out of the buckets, because at that moment it is a partial round and
    /// filing it would put a lower bound into a bucket as if it were the cost.
    /// The completed read must show it FILED, because by then the query is over
    /// and a round that ran is a round that ran. Without the fold every loop
    /// that ends between its halves -- which on `QF_NIA` is most of them --
    /// reports an empty distribution beside a non-zero round count.
    #[test]
    fn the_last_round_is_pending_in_flight_and_filed_once_the_query_is_over() {
        let board = LiveInstruments::new();
        let _live = install(&board);
        let guard = LazySmtCountersGuard::enable();
        record_entry(LazySmtLoop::Nia, 4);
        record_skeleton(
            LazySmtLoop::Nia,
            Duration::from_millis(6_700),
            RoundOutcome::Unknown,
        );

        let in_flight = live_lazy_smt_counters(&board).expect("a mirror is installed");
        assert_eq!(
            in_flight.value.pending_round,
            Duration::from_millis(6_700),
            "the round in flight must be reported as pending"
        );
        assert!(
            in_flight.value.hist(LazySmtLoop::Nia).is_empty(),
            "and must NOT be in a bucket yet: it is a lower bound, not a cost"
        );

        let completed = last_lazy_smt_counters().expect("armed");
        let hist = completed.hist(LazySmtLoop::Nia);
        assert_eq!(
            hist.rounds(),
            1,
            "the completed read folds the last round in"
        );
        assert_eq!(hist.max(), Duration::from_millis(6_700));
        assert_eq!(
            hist.buckets()[13],
            1,
            "6700 ms is bucket 13 ([4096, 8192) ms); got {:?}",
            hist.buckets()
        );
        assert_eq!(completed.nia_rounds, 1, "and the round count is unchanged");
        drop(guard);
    }

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
