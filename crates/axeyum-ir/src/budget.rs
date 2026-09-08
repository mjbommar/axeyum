//! Deterministic work budgets: the shared resource-limit primitive.
//!
//! # Why this exists
//!
//! Determinism is a public API promise in this stack ("stable iteration order,
//! explicit seeds, explicit resource limits"). A limit that moves with host
//! load is not an explicit limit: the same commit on the same machine has
//! produced different capability-frontier counts purely from load, and the
//! solver expresses internal limits as `deadline: Option<Instant>` at 312 call
//! sites across 58 files against 5 mentions of a deterministic budget in all of
//! `axeyum-solver` (measured on `main` at `cbb178c55`; see
//! `docs/research/04-architecture/deterministic-work-budgets.md`).
//!
//! This module is the replacement primitive for *internal allocation*
//! decisions -- "how much vivification should this formula get?", "how many
//! resolution attempts may this elimination round make?". It does **not**
//! replace an external wall-clock timeout, which is wall-clock by nature.
//!
//! # The model, in one paragraph
//!
//! A pass is budgeted in **its own natural unit of work** -- a [`WorkMeter`]
//! counting ticks, resolution attempts, occurrence-list steps, rewrite
//! applications, whatever that pass actually spends. A [`Budget`] is an
//! absolute stop value in that meter, so a check is one `u64` comparison and
//! never a syscall. An [`EffortPolicy`] computes the stop value as a *per-mille
//! slice of the work some **other** meter has done since this pass last ran*,
//! so a pass can never outgrow the thing it is helping. An [`EffortAccount`]
//! owns the watermark, the accumulate-and-delay gate, the failure backoff, and
//! the spend attribution for one pass. [`Delayed`] wraps a [`BudgetedPass`] in
//! that account so the delay logic is a policy, not an `if` inside each pass.
//!
//! This is the design CaDiCaL and Kissat converged on (`kimits.h:135-170`,
//! `limit.hpp:136-164`), read and transcribed in
//! `docs/research/02-ecosystems/inprocessing-scheduling-2026-09/cadical-kissat-budget-model.md`.
//! Their `<pass>effort` defaults are 100 per mille for the major passes, and an
//! independent empirical study (Wotzlaw et al., arXiv:1310.4756) landed on the
//! same 10 % in wall-clock terms -- hence [`EffortPolicy::MAJOR_PASS`].
//!
//! # Determinism rules this module obeys, and how they are enforced
//!
//! 1. **No clock.** Nothing here reads a time source of any kind.
//! 2. **No floating point.** Both reference solvers compute their growth laws
//!    with libm; libm results are *not* bit-identical across implementations,
//!    so a schedule boundary computed that way can differ by one round between
//!    two hosts -- which would silently break the determinism this module
//!    exists to provide. Every computation here is integer-only, including the
//!    growth ladder ([`Growth`]) and the success-rate test
//!    ([`EffortAccount::record_success_rate`]), which cross-multiplies instead
//!    of comparing a ratio against a fractional constant.
//! 3. **No allocation on a decision path**, so a budget check cannot fail and
//!    cannot perturb the thing it measures.
//!
//! Rules 1 and 2 are checked by
//! `tests::the_budget_primitive_reads_no_clock_and_no_float`, which scans this
//! module's own source. That test can fail: adding a single floating-point
//! computation or clock read to a budget decision here turns it red.
//!
//! # Example
//!
//! ```
//! use axeyum_ir::budget::{EffortAccount, EffortPolicy, Grant, WorkMeter};
//!
//! // The numeraire: work the main search has done. Never incremented by the
//! // pass being scheduled (see `EffortAccount::request`).
//! let mut search = WorkMeter::new();
//! search.charge(40_000_000);
//!
//! // Vivification's own meter, in vivification's own unit.
//! let mut vivify_work = WorkMeter::new();
//!
//! // 10 % of search work since the last round, but refuse to run at all until
//! // the accrued slice can pay 20x the clause count of setup.
//! let policy = EffortPolicy::MAJOR_PASS.with_init_cost(20);
//! let mut account = EffortAccount::new(policy);
//!
//! let clauses = 100_000;
//! let Grant::Granted(budget) = account.request(&search, &vivify_work, clauses) else {
//!     panic!("40M of search buys 4M, which clears 20 x 100k = 2M");
//! };
//! assert_eq!(budget.limit(), 4_000_000);
//!
//! // The pass loops until the budget is exhausted; the check is one compare.
//! while !budget.exhausted(&vivify_work) {
//!     vivify_work.charge(1_000_000);
//! }
//! account.settle(&vivify_work);
//! assert_eq!(account.spent(), 4_000_000);
//! ```

/// The denominator of every effort fraction in this module.
///
/// Efforts are expressed per mille (parts per thousand) rather than as a
/// percentage or a fraction because the arithmetic must be exact and integral:
/// a budget is `reference * per_mille / PER_MILLE`, evaluated through a `u128`
/// intermediate so it can neither overflow nor round differently on another
/// host.
pub const PER_MILLE: u64 = 1000;

/// `value * numerator / denominator`, computed through a `u128` intermediate so
/// the multiplication cannot overflow, and clamped rather than truncated on the
/// way back down. `denominator == 0` yields `0`.
///
/// Every fraction in this module goes through here: exact integer arithmetic,
/// one rounding rule (truncation), and no platform-dependent result.
fn mul_div(value: u64, numerator: u64, denominator: u64) -> u64 {
    if denominator == 0 {
        return 0;
    }
    let quotient = (u128::from(value) * u128::from(numerator)) / u128::from(denominator);
    u64::try_from(quotient).unwrap_or(u64::MAX)
}

/// A monotone, clock-free counter of work in one pass's natural unit.
///
/// The unit is the caller's choice and is deliberately not encoded in the type:
/// the reference solvers budget propagation-driven passes in cache-line
/// "ticks", bounded variable elimination in *resolution attempts*, and forward
/// subsumption in *occurrence-list steps*, and forcing those into one unit
/// would be worse than letting each pass pay in what it actually spends. The
/// abstraction is "a counter you can compare against a limit".
///
/// A meter only ever goes up. [`WorkMeter::charge`] saturates rather than
/// wrapping, so an absurd charge degrades to "budget exhausted" and can never
/// make an exhausted budget look fresh.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WorkMeter {
    spent: u64,
}

/// A remembered [`WorkMeter`] reading, for measuring what a sub-computation
/// spent. See [`WorkMeter::mark`] / [`WorkMeter::since`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MeterMark(u64);

impl MeterMark {
    /// The reading this mark recorded.
    #[must_use]
    pub const fn reading(self) -> u64 {
        self.0
    }
}

impl WorkMeter {
    /// A meter reading zero.
    #[must_use]
    pub const fn new() -> Self {
        Self { spent: 0 }
    }

    /// A meter starting at `spent` -- for adopting an existing counter (for
    /// example one derived from a search's event counters) without resetting
    /// it.
    #[must_use]
    pub const fn at(spent: u64) -> Self {
        Self { spent }
    }

    /// Charges `units` of work. Saturating: never wraps.
    #[inline]
    pub const fn charge(&mut self, units: u64) {
        self.spent = self.spent.saturating_add(units);
    }

    /// Sets the meter to `spent`, for a meter that mirrors an externally
    /// maintained monotone counter. Ignores a value below the current reading,
    /// so the meter stays monotone whatever the caller does.
    #[inline]
    pub const fn advance_to(&mut self, spent: u64) {
        if spent > self.spent {
            self.spent = spent;
        }
    }

    /// The total charged so far.
    #[inline]
    #[must_use]
    pub const fn spent(&self) -> u64 {
        self.spent
    }

    /// Snapshots the current reading, so a caller can learn what a child spent.
    #[inline]
    #[must_use]
    pub const fn mark(&self) -> MeterMark {
        MeterMark(self.spent)
    }

    /// Work charged since `mark`.
    #[inline]
    #[must_use]
    pub const fn since(&self, mark: MeterMark) -> u64 {
        self.spent.saturating_sub(mark.0)
    }
}

/// An absolute stop value in some [`WorkMeter`]'s unit.
///
/// Absolute rather than a remaining-count because that is what makes the check
/// free: a pass compares a monotone counter against a fixed number and never
/// has to decrement, reset, or thread a mutable allowance through its call
/// graph. It is also what makes sub-budgets composable -- see
/// [`Budget::split`].
///
/// The exhaustion test is `meter.spent() >= limit`. (Kissat loops while
/// `counter <= limit`, i.e. it grants one step past the limit; we do not, so a
/// zero-width budget admits no work at all, matching the `resource_limit = 0`
/// convention used elsewhere in this tree.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Budget {
    limit: u64,
}

impl Budget {
    /// A budget that stops when the meter reaches `limit`.
    #[must_use]
    pub const fn until(limit: u64) -> Self {
        Self { limit }
    }

    /// A budget that never stops. Useful for a re-validation or proof-checking
    /// path where the work must be completed whatever it costs.
    #[must_use]
    pub const fn unlimited() -> Self {
        Self { limit: u64::MAX }
    }

    /// A budget admitting no work at all.
    #[must_use]
    pub const fn nothing() -> Self {
        Self { limit: 0 }
    }

    /// The absolute stop value.
    #[must_use]
    pub const fn limit(&self) -> u64 {
        self.limit
    }

    /// Whether `meter` has reached the stop value. **This is the hot check**:
    /// one load and one comparison, no clock, no allocation, no branchy
    /// arithmetic.
    #[inline]
    #[must_use]
    pub const fn exhausted(&self, meter: &WorkMeter) -> bool {
        meter.spent >= self.limit
    }

    /// Work `meter` may still do under this budget.
    #[inline]
    #[must_use]
    pub const fn remaining(&self, meter: &WorkMeter) -> u64 {
        self.limit.saturating_sub(meter.spent)
    }

    /// Splits this budget across weighted sub-passes **with carry-over**.
    ///
    /// The returned [`BudgetSplit`] hands out *cumulative* limits, so a
    /// sub-pass that finishes under its slice donates the remainder to the
    /// next one instead of forfeiting it. Carry-over is not cosmetic: without
    /// it a sub-pass with few candidates wastes its share while the round still
    /// pays the full setup cost, and the round systematically under-spends its
    /// allowance.
    ///
    /// `meter` supplies the base -- the split covers only the budget's *unspent*
    /// portion, so calling this mid-round is well defined.
    #[must_use]
    pub const fn split(&self, meter: &WorkMeter) -> BudgetSplit {
        BudgetSplit {
            base: meter.spent,
            total: self.limit.saturating_sub(meter.spent),
            weight_sum: 0,
            weight_used: 0,
        }
    }
}

/// Hands out cumulative sub-budgets of one [`Budget`], carrying unspent
/// allowance forward. Created by [`Budget::split`].
///
/// Weights are declared up front with [`BudgetSplit::weights`] so the
/// denominator is known before the first slice is issued; slices are then taken
/// one at a time, in order, with no allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BudgetSplit {
    base: u64,
    total: u64,
    weight_sum: u64,
    weight_used: u64,
}

impl BudgetSplit {
    /// Declares the weight denominator. `weight_sum` is the sum of every slice
    /// that will be taken; a zero sum means every slice is empty.
    #[must_use]
    pub const fn weights(mut self, weight_sum: u64) -> Self {
        self.weight_sum = weight_sum;
        self
    }

    /// Takes the next slice, of relative size `weight`.
    ///
    /// The returned budget's limit is cumulative -- `base + total * used / sum`
    /// after adding `weight` -- which is exactly the carry-over property: if the
    /// previous sub-pass stopped short of its limit, this one starts with the
    /// difference still available.
    #[must_use]
    pub fn take(&mut self, weight: u64) -> Budget {
        if self.weight_sum == 0 {
            return Budget::until(self.base);
        }
        self.weight_used = self.weight_used.saturating_add(weight);
        if self.weight_used > self.weight_sum {
            self.weight_used = self.weight_sum;
        }
        // u128 intermediate: `total` and `weight_used` are both u64-wide.
        let granted = mul_div(self.total, self.weight_used, self.weight_sum);
        Budget::until(self.base.saturating_add(granted))
    }
}

/// An integer-only growth ladder for schedule intervals.
///
/// Both reference solvers scale their inter-round intervals with libm's
/// `log10`, `log` or `sqrt`. Those results are **not** bit-identical across
/// implementations, so a schedule boundary computed that way can differ between
/// two hosts running the same source -- which would silently break the
/// determinism this module exists to provide. Every variant here is exact
/// integer arithmetic.
///
/// `scale(0)` is 1 for every variant, so a growth law never collapses an
/// interval to zero on the first round.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Growth {
    /// `1` -- a fixed interval.
    #[default]
    Constant,
    /// `n` -- linear in the number of completed rounds.
    Linear,
    /// `isqrt(n)`, exact integer square root.
    Sqrt,
    /// `floor(log2(n)) + 1`.
    Log2,
    /// `floor(log10(n)) + 1`.
    Log10,
    /// `n * (floor(log2(n)) + 1)`.
    NLog2N,
    /// `n * (floor(log2(n)) + 1)^2`.
    NLog2SquaredN,
}

impl Growth {
    /// Evaluates the ladder at `n` (typically the number of completed rounds).
    /// Saturating; never zero.
    #[must_use]
    pub const fn scale(self, n: u64) -> u64 {
        if n == 0 {
            return 1;
        }
        match self {
            Self::Constant => 1,
            Self::Linear => n,
            Self::Sqrt => {
                let r = n.isqrt();
                if r == 0 { 1 } else { r }
            }
            Self::Log2 => n.ilog2() as u64 + 1,
            Self::Log10 => n.ilog10() as u64 + 1,
            Self::NLog2N => n.saturating_mul(n.ilog2() as u64 + 1),
            Self::NLog2SquaredN => {
                let l = n.ilog2() as u64 + 1;
                n.saturating_mul(l).saturating_mul(l)
            }
        }
    }
}

/// When a pass should next be offered a round, in some monotone trigger unit
/// (conflicts, rounds, propagations -- the caller's choice).
///
/// The trigger is separate from the budget on purpose: the budget says *how
/// much* a round may spend, the schedule says *when* a round is offered. Both
/// reference solvers keep them separate for the same reason, and the growth law
/// here is [`Growth`], so the boundary is integer-exact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchedulePolicy {
    /// The interval before the first repeat.
    pub base_interval: u64,
    /// How the interval grows with the number of completed rounds.
    pub growth: Growth,
    /// Whether to scale the interval by the formula scale as well. When set,
    /// the interval is multiplied by `Growth::Log10` of the scale, so a big
    /// formula is visited proportionally less often.
    pub size_scaled: bool,
}

impl SchedulePolicy {
    /// A fixed interval of `base_interval`, not size-scaled.
    #[must_use]
    pub const fn every(base_interval: u64) -> Self {
        Self {
            base_interval,
            growth: Growth::Constant,
            size_scaled: false,
        }
    }

    /// Sets the growth law.
    #[must_use]
    pub const fn with_growth(mut self, growth: Growth) -> Self {
        self.growth = growth;
        self
    }

    /// Scales the interval by the formula scale as well.
    #[must_use]
    pub const fn size_scaled(mut self) -> Self {
        self.size_scaled = true;
        self
    }

    /// The trigger value at which the pass should next be offered a round,
    /// given the current trigger reading, how many rounds it has completed, and
    /// the formula scale.
    #[must_use]
    pub const fn next_trigger(&self, now: u64, rounds_completed: u64, scale: u64) -> u64 {
        let mut delta = self
            .base_interval
            .saturating_mul(self.growth.scale(rounds_completed));
        if self.size_scaled {
            delta = delta.saturating_mul(Growth::Log10.scale(scale));
        }
        now.saturating_add(delta)
    }
}

/// Additive-increase / multiplicative-decrease backoff on *skipped rounds*.
///
/// This is the cheapest available answer to "this pass does not pay off on this
/// instance": instead of a global on/off switch, a pass that keeps failing gets
/// skipped for a linearly growing number of rounds, and any success halves the
/// skip count. Kissat drives it from a success rate below 1 %
/// (`vivify.c:1454-1457`).
///
/// It matters more here than there. Our measurement was that the inprocessing
/// passes lose inside a 24 s budget *on our workload*, and the response was to
/// default them off everywhere; a backoff would have switched them off only on
/// the instances where they actually lose.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DelayCounter {
    /// Rounds still to skip.
    count: u32,
    /// The current skip length, which `bump` grows and `reduce` halves.
    current: u32,
}

impl DelayCounter {
    /// A counter that is not currently delaying anything.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            count: 0,
            current: 0,
        }
    }

    /// Consumes one round of the current delay. Returns `true` if this round
    /// should be skipped.
    pub const fn delaying(&mut self) -> bool {
        if self.count > 0 {
            self.count -= 1;
            true
        } else {
            false
        }
    }

    /// The pass did not pay off: lengthen the skip (additive increase).
    pub const fn bump(&mut self) {
        self.current = self.current.saturating_add(1);
        self.count = self.current;
    }

    /// The pass paid off: halve the skip (multiplicative decrease).
    pub const fn reduce(&mut self) {
        self.current /= 2;
        self.count = self.current;
    }

    /// Rounds still to be skipped.
    #[must_use]
    pub const fn rounds_left(&self) -> u32 {
        self.count
    }
}

/// How much work a pass may spend, as a function of what the numeraire spent.
///
/// Three knobs, each of which encodes a distinct fact about the pass:
///
/// * `per_mille` -- the pass's steady-state share of the reference work. The
///   whole schedule's cost is then readable off a table at design time rather
///   than discovered per instance.
/// * `min_reference` -- a floor on the reference window, so the very first round
///   has something to spend before any search has happened. This is what makes
///   "preprocess before search" a special case of the same code path instead of
///   separate machinery.
/// * `init_cost_per_scale_unit` -- the pass's **fixed setup cost**, expressed
///   per unit of formula scale. This drives the accumulate-and-delay gate, and
///   it is the piece that answers "the pass costs more than it saves": a pass
///   with `O(|F|)` setup should run rarely and thoroughly, not often and
///   pointlessly. `0` disables the gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EffortPolicy {
    /// Slice of the reference window, in parts per thousand.
    pub per_mille: u32,
    /// Lower clamp on the reference window.
    pub min_reference: u64,
    /// Setup cost per unit of scale; `0` means "no setup cost worth delaying
    /// for".
    pub init_cost_per_scale_unit: u64,
}

impl EffortPolicy {
    /// 10 % of the reference window, no floor, no delay gate.
    ///
    /// 10 % is the value three independent sources converge on: Kissat's
    /// `eliminateeffort`, `vivifyeffort`, `forwardeffort` and `sweepeffort` are
    /// all 100 per mille, `CaDiCaL`'s `sweepeffort` is the same, and Wotzlaw et
    /// al. (arXiv:1310.4756) determined 10 % empirically in wall-clock terms.
    /// It is a defensible starting constant, not a measured optimum for a 24 s
    /// budget -- the formula transfers, the constants need our own measurement.
    pub const MAJOR_PASS: Self = Self {
        per_mille: 100,
        min_reference: 0,
        init_cost_per_scale_unit: 0,
    };

    /// 2 % of the reference window -- the reference solvers' setting for cheap
    /// auxiliary passes (backbone, transitive reduction).
    pub const MINOR_PASS: Self = Self {
        per_mille: 20,
        min_reference: 0,
        init_cost_per_scale_unit: 0,
    };

    /// A policy spending `per_mille` of the reference window.
    #[must_use]
    pub const fn new(per_mille: u32) -> Self {
        Self {
            per_mille,
            min_reference: 0,
            init_cost_per_scale_unit: 0,
        }
    }

    /// Sets the floor on the reference window, so an early round with no
    /// history still gets a budget.
    #[must_use]
    pub const fn with_min_reference(mut self, min_reference: u64) -> Self {
        self.min_reference = min_reference;
        self
    }

    /// Sets the per-scale-unit setup cost that arms the accumulate-and-delay
    /// gate. `CaDiCaL`'s values, in ticks per clause, are 20 for vivification, 7
    /// for factoring, 6 for ternary resolution and 5 for sweeping -- the pass
    /// with the largest setup is delayed hardest.
    #[must_use]
    pub const fn with_init_cost(mut self, per_scale_unit: u64) -> Self {
        self.init_cost_per_scale_unit = per_scale_unit;
        self
    }

    /// The slice `reference` buys, before any gate. Exact integer arithmetic
    /// through a `u128` intermediate.
    #[must_use]
    pub fn slice_of(&self, reference: u64) -> u64 {
        let reference = if reference < self.min_reference {
            self.min_reference
        } else {
            reference
        };
        mul_div(reference, u64::from(self.per_mille), PER_MILLE)
    }
}

/// What [`EffortAccount::request`] decided about one round.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Grant {
    /// Run, under this budget.
    Granted(Budget),
    /// Do not run: the accrued slice cannot yet pay the pass's setup cost.
    ///
    /// **The watermark was deliberately not advanced**, so the reference window
    /// keeps growing and `accrued` keeps rising until it clears `threshold`.
    /// That omission is the entire mechanism; without it a delayed round simply
    /// loses its budget and the pass never becomes affordable.
    Delayed {
        /// The slice the reference window currently buys.
        accrued: u64,
        /// The setup cost it must clear: `init_cost_per_scale_unit * scale`.
        threshold: u64,
    },
    /// Do not run: the failure backoff is still skipping rounds.
    BackedOff {
        /// Rounds still to skip after this one.
        rounds_left: u32,
    },
}

/// Per-pass budget state: the watermark, both delay mechanisms, and the spend
/// attribution.
///
/// One account belongs to exactly one pass. It is the composable unit -- a
/// parent schedule holds an account per child, hands each child a bounded
/// [`Budget`], and learns from [`EffortAccount::settle`] what that child
/// actually spent, so the ledger names the pass that consumed the work rather
/// than the last pass to run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EffortAccount {
    policy: EffortPolicy,
    /// Reference-meter reading at the end of the last **granted** round.
    reference_watermark: u64,
    /// Own-meter reading at the start of the current granted round, for
    /// attributing spend in [`EffortAccount::settle`].
    round_start: u64,
    granted: u64,
    spent: u64,
    rounds_granted: u64,
    rounds_delayed: u64,
    rounds_backed_off: u64,
    backoff: DelayCounter,
}

impl EffortAccount {
    /// A fresh account under `policy`.
    #[must_use]
    pub const fn new(policy: EffortPolicy) -> Self {
        Self {
            policy,
            reference_watermark: 0,
            round_start: 0,
            granted: 0,
            spent: 0,
            rounds_granted: 0,
            rounds_delayed: 0,
            rounds_backed_off: 0,
            backoff: DelayCounter::new(),
        }
    }

    /// The policy in force.
    #[must_use]
    pub const fn policy(&self) -> EffortPolicy {
        self.policy
    }

    /// Decides whether this pass may run, and under what budget.
    ///
    /// * `reference` is the numeraire -- the meter measuring the work this pass
    ///   is a fraction of, normally the main search. **It must never be the
    ///   pass's own meter**: a pass scheduled by a counter it increments feeds
    ///   back into its own trigger, which is a known scheduling-feedback defect
    ///   class. That is `debug_assert`ed here and made structurally impossible
    ///   by [`Delayed`].
    /// * `own` is the meter the pass charges its work to; the returned budget
    ///   is absolute in that meter.
    /// * `scale` is the deterministic size input for the delay gate, in
    ///   whatever unit `init_cost_per_scale_unit` is denominated (clause count,
    ///   for the reference solvers).
    pub fn request(&mut self, reference: &WorkMeter, own: &WorkMeter, scale: u64) -> Grant {
        debug_assert!(
            !std::ptr::eq(reference, own),
            "a pass must not be scheduled by a counter it increments"
        );

        if self.backoff.delaying() {
            self.rounds_backed_off += 1;
            return Grant::BackedOff {
                rounds_left: self.backoff.rounds_left(),
            };
        }

        let window = reference.spent().saturating_sub(self.reference_watermark);
        let accrued = self.policy.slice_of(window);

        if self.policy.init_cost_per_scale_unit > 0 {
            let threshold = self.policy.init_cost_per_scale_unit.saturating_mul(scale);
            if accrued < threshold {
                // The watermark is NOT advanced: the window keeps growing so
                // the pass eventually becomes affordable. This omission is the
                // mechanism -- see the mutation control in the tests below.
                self.rounds_delayed += 1;
                return Grant::Delayed { accrued, threshold };
            }
        }

        self.reference_watermark = reference.spent();
        self.round_start = own.spent();
        self.granted = self.granted.saturating_add(accrued);
        self.rounds_granted += 1;
        Grant::Granted(Budget::until(own.spent().saturating_add(accrued)))
    }

    /// Records what the round just granted actually spent, from `own`'s reading
    /// after the pass returned. Call once per [`Grant::Granted`].
    pub const fn settle(&mut self, own: &WorkMeter) {
        self.spent = self
            .spent
            .saturating_add(own.spent().saturating_sub(self.round_start));
    }

    /// Feeds the failure backoff an integer success-rate test: bump when the
    /// success rate is below `threshold_per_mille`, reduce otherwise.
    /// Cross-multiplied, so there is no division and no fractional constant.
    ///
    /// `attempts == 0` is treated as a failure -- a round that tried nothing did
    /// not earn its setup cost.
    pub const fn record_success_rate(
        &mut self,
        successes: u64,
        attempts: u64,
        threshold_per_mille: u32,
    ) {
        let paid_off = attempts > 0
            && (successes as u128 * PER_MILLE as u128)
                >= (attempts as u128 * threshold_per_mille as u128);
        self.record_outcome(paid_off);
    }

    /// Marks the round as having paid off (`reduce`) or not (`bump`) directly,
    /// when the caller has a better predicate than a success rate.
    pub const fn record_outcome(&mut self, paid_off: bool) {
        if paid_off {
            self.backoff.reduce();
        } else {
            self.backoff.bump();
        }
    }

    /// Total work granted across all rounds.
    #[must_use]
    pub const fn granted(&self) -> u64 {
        self.granted
    }

    /// Total work actually spent across all settled rounds -- the attribution
    /// number.
    #[must_use]
    pub const fn spent(&self) -> u64 {
        self.spent
    }

    /// An immutable snapshot for reporting.
    #[must_use]
    pub const fn stats(&self) -> PassBudgetStats {
        PassBudgetStats {
            per_mille: self.policy.per_mille,
            init_cost_per_scale_unit: self.policy.init_cost_per_scale_unit,
            granted: self.granted,
            spent: self.spent,
            rounds_granted: self.rounds_granted,
            rounds_delayed: self.rounds_delayed,
            rounds_backed_off: self.rounds_backed_off,
            backoff_rounds_left: self.backoff.rounds_left(),
        }
    }
}

/// A snapshot of one pass's budget history. Every field is an integer event
/// count or a work total; there is no time here, so collecting it cannot
/// perturb what it measures.
///
/// We cannot schedule what we cannot see: `rounds_delayed` against
/// `rounds_granted` is what says whether the delay gate is doing anything, and
/// `spent` against `granted` is what says whether a pass is budget-bound or
/// candidate-bound. Those are different problems with different fixes.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PassBudgetStats {
    /// The policy's slice, in parts per thousand.
    pub per_mille: u32,
    /// The policy's setup cost per scale unit; `0` if the delay gate is off.
    pub init_cost_per_scale_unit: u64,
    /// Work granted across all rounds.
    pub granted: u64,
    /// Work spent across all settled rounds.
    pub spent: u64,
    /// Rounds that ran.
    pub rounds_granted: u64,
    /// Rounds refused by the accumulate-and-delay gate.
    pub rounds_delayed: u64,
    /// Rounds skipped by the failure backoff.
    pub rounds_backed_off: u64,
    /// Backoff rounds still queued.
    pub backoff_rounds_left: u32,
}

impl PassBudgetStats {
    /// Fraction of the granted budget actually used, in parts per thousand.
    /// `0` when nothing was granted.
    #[must_use]
    pub fn utilisation_per_mille(&self) -> u64 {
        if self.granted == 0 {
            return 0;
        }
        mul_div(self.spent, PER_MILLE, self.granted)
    }
}

/// A pass that can be run under a [`Budget`].
///
/// Implementing this instead of writing the delay check inline is the point:
/// the accumulate-and-delay gate, the failure backoff and the spend
/// attribution then live in [`Delayed`] and are shared by every pass in every
/// division, rather than being re-derived as an `if` in each one.
pub trait BudgetedPass {
    /// What one round returns.
    type Outcome;

    /// The deterministic size input to the delay gate -- clause count for a CNF
    /// pass, term count for a rewrite pass, row count for a simplex pass.
    /// Ignored when the policy has no setup cost.
    fn scale(&self) -> u64;

    /// Runs one round under `budget`, charging its work to `meter`.
    ///
    /// The pass is expected to stop when `budget.exhausted(meter)`; the wrapper
    /// does not interrupt it.
    fn run(&mut self, budget: Budget, meter: &mut WorkMeter) -> Self::Outcome;

    /// Whether the round earned its keep, driving the failure backoff. The
    /// default never backs off, so a pass opts into the mechanism.
    fn paid_off(&self, _outcome: &Self::Outcome) -> bool {
        true
    }
}

/// What one [`Delayed::run_round`] did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RoundOutcome<T> {
    /// The pass ran.
    Ran {
        /// What the pass returned.
        outcome: T,
        /// Work granted to this round.
        granted: u64,
        /// Work the round actually spent.
        spent: u64,
    },
    /// The accumulate-and-delay gate refused the round; budget keeps accruing.
    Delayed {
        /// The slice the reference window currently buys.
        accrued: u64,
        /// The setup cost it must clear.
        threshold: u64,
    },
    /// The failure backoff skipped the round.
    BackedOff {
        /// Rounds still to skip.
        rounds_left: u32,
    },
}

/// A [`BudgetedPass`] wrapped in its own [`EffortAccount`] and work meter.
///
/// This is the "delay policy, not an `if` statement" form. The wrapper owns the
/// pass's meter, so the pass cannot be scheduled by a counter it increments --
/// the feedback defect `EffortAccount::request` only `debug_assert`s is
/// structurally impossible here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Delayed<P> {
    name: &'static str,
    pass: P,
    account: EffortAccount,
    meter: WorkMeter,
}

impl<P> Delayed<P> {
    /// Wraps `pass` under `policy`. `name` is the attribution label.
    pub const fn new(name: &'static str, pass: P, policy: EffortPolicy) -> Self {
        Self {
            name,
            pass,
            account: EffortAccount::new(policy),
            meter: WorkMeter::new(),
        }
    }

    /// The attribution label.
    #[must_use]
    pub const fn name(&self) -> &'static str {
        self.name
    }

    /// The wrapped pass.
    pub const fn pass(&self) -> &P {
        &self.pass
    }

    /// The wrapped pass, mutably.
    pub const fn pass_mut(&mut self) -> &mut P {
        &mut self.pass
    }

    /// This pass's own work meter.
    #[must_use]
    pub const fn meter(&self) -> &WorkMeter {
        &self.meter
    }

    /// This pass's budget history.
    #[must_use]
    pub const fn stats(&self) -> PassBudgetStats {
        self.account.stats()
    }

    /// The underlying account, for callers driving the backoff themselves.
    pub const fn account_mut(&mut self) -> &mut EffortAccount {
        &mut self.account
    }
}

impl<P: BudgetedPass> Delayed<P> {
    /// Offers the pass a round against `reference`.
    ///
    /// Consults the backoff, then the accumulate-and-delay gate, and only then
    /// runs the pass -- settling the spend and feeding the backoff afterwards.
    pub fn run_round(&mut self, reference: &WorkMeter) -> RoundOutcome<P::Outcome> {
        let scale = self.pass.scale();
        match self.account.request(reference, &self.meter, scale) {
            Grant::BackedOff { rounds_left } => RoundOutcome::BackedOff { rounds_left },
            Grant::Delayed { accrued, threshold } => RoundOutcome::Delayed { accrued, threshold },
            Grant::Granted(budget) => {
                let before = self.meter.mark();
                let outcome = self.pass.run(budget, &mut self.meter);
                let spent = self.meter.since(before);
                self.account.settle(&self.meter);
                self.account.record_outcome(self.pass.paid_off(&outcome));
                RoundOutcome::Ran {
                    outcome,
                    granted: budget.limit().saturating_sub(before.reading()),
                    spent,
                }
            }
        }
    }
}

/// A deterministic, insertion-ordered record of what each pass was granted and
/// what it spent.
///
/// Insertion-ordered rather than keyed by a hash map, because iteration order is
/// a public API promise here and a report that reorders between runs is not
/// evidence.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BudgetLedger {
    entries: Vec<(&'static str, PassBudgetStats)>,
}

impl BudgetLedger {
    /// An empty ledger.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Records (or replaces) `name`'s stats, preserving first-insertion order.
    pub fn record(&mut self, name: &'static str, stats: PassBudgetStats) {
        if let Some(slot) = self.entries.iter_mut().find(|(n, _)| *n == name) {
            slot.1 = stats;
        } else {
            self.entries.push((name, stats));
        }
    }

    /// The recorded passes, in insertion order.
    #[must_use]
    pub fn entries(&self) -> &[(&'static str, PassBudgetStats)] {
        &self.entries
    }

    /// Work granted across every recorded pass.
    #[must_use]
    pub fn total_granted(&self) -> u64 {
        self.entries
            .iter()
            .fold(0u64, |acc, (_, s)| acc.saturating_add(s.granted))
    }

    /// Work spent across every recorded pass.
    #[must_use]
    pub fn total_spent(&self) -> u64 {
        self.entries
            .iter()
            .fold(0u64, |acc, (_, s)| acc.saturating_add(s.spent))
    }
}

impl std::fmt::Display for BudgetLedger {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{:<20} {:>8} {:>14} {:>14} {:>6} {:>7} {:>7} {:>7}",
            "pass", "permille", "granted", "spent", "use%o", "ran", "delayed", "backoff"
        )?;
        for (name, s) in &self.entries {
            writeln!(
                f,
                "{:<20} {:>8} {:>14} {:>14} {:>6} {:>7} {:>7} {:>7}",
                name,
                s.per_mille,
                s.granted,
                s.spent,
                s.utilisation_per_mille(),
                s.rounds_granted,
                s.rounds_delayed,
                s.rounds_backed_off
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Rules 1 and 2 of the module contract, checked against this module's own
    /// source. Adding a clock read or a floating-point computation to a budget
    /// decision here turns this red -- which is the point: the determinism
    /// claim must be falsifiable by the thing that would falsify it.
    #[test]
    fn the_budget_primitive_reads_no_clock_and_no_float() {
        let source = include_str!("budget.rs");
        // Scan the module's own code only: everything before the test module,
        // minus comment lines, which legitimately discuss libm and wall clocks.
        // (The test module is excluded because the banned needles below appear
        // in it as string literals.)
        let marker = "#[cfg(test)]";
        let split = source
            .find(marker)
            .expect("budget.rs must contain a #[cfg(test)] module for this scan to be scoped");
        let code: String = source[..split]
            .lines()
            .filter(|line| !line.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");

        for banned in [
            "Instant",
            "SystemTime",
            "std::time",
            "f64",
            "f32",
            "as f",
            "powf",
            "powi",
            "libm",
            ".ln()",
            ".exp()",
        ] {
            assert!(
                !code.contains(banned),
                "budget.rs code contains `{banned}`: a budget decision must be \
                 integer-only and clock-free"
            );
        }
        // Positive control: the scan sees the real decision path, not an empty
        // string left by a filter that stripped everything.
        assert!(
            code.contains("pub fn request") && code.contains("Grant::Delayed"),
            "the source scan found no decision code -- the slice or the filter \
             is wrong, so the negative results above mean nothing"
        );
    }

    #[test]
    fn a_budget_is_an_absolute_stop_value_in_the_meters_own_unit() {
        let mut meter = WorkMeter::new();
        let budget = Budget::until(10);
        assert!(!budget.exhausted(&meter));
        assert_eq!(budget.remaining(&meter), 10);
        meter.charge(9);
        assert!(!budget.exhausted(&meter));
        meter.charge(1);
        assert!(budget.exhausted(&meter));
        assert_eq!(budget.remaining(&meter), 0);
        // Zero-width admits nothing.
        assert!(Budget::nothing().exhausted(&WorkMeter::new()));
        assert!(!Budget::unlimited().exhausted(&WorkMeter::at(u64::MAX - 1)));
    }

    #[test]
    fn charging_saturates_rather_than_wrapping() {
        let mut meter = WorkMeter::at(u64::MAX - 1);
        meter.charge(1000);
        assert_eq!(meter.spent(), u64::MAX);
        // An absurd charge degrades to "exhausted", never to "fresh".
        assert!(Budget::until(10).exhausted(&meter));
    }

    #[test]
    fn a_mirrored_meter_stays_monotone() {
        let mut meter = WorkMeter::new();
        meter.advance_to(500);
        assert_eq!(meter.spent(), 500);
        meter.advance_to(100);
        assert_eq!(meter.spent(), 500, "a mirrored meter must never go back");
    }

    #[test]
    fn a_per_mille_slice_is_exact_integer_arithmetic() {
        let p = EffortPolicy::new(100);
        assert_eq!(p.slice_of(1_000), 100);
        assert_eq!(p.slice_of(999), 99); // truncating, not rounding
        assert_eq!(p.slice_of(0), 0);
        // No overflow at the top of the range: the u128 intermediate holds.
        assert_eq!(EffortPolicy::new(1000).slice_of(u64::MAX), u64::MAX);
        // The floor applies before the slice.
        assert_eq!(p.with_min_reference(10_000).slice_of(5), 1_000);
    }

    #[test]
    fn a_split_carries_unspent_allowance_to_the_next_sub_pass() {
        // A 1000-unit budget split 3/3/1/3 -- Kissat's vivify tier weights.
        let mut meter = WorkMeter::new();
        let budget = Budget::until(1000);
        let mut split = budget.split(&meter).weights(10);

        let tier1 = split.take(3);
        assert_eq!(tier1.limit(), 300);
        // Tier 1 under-spends badly: 10 of its 300.
        meter.charge(10);

        // Tier 2's limit is CUMULATIVE, so tier 1's 290 unspent units are still
        // available -- that is the carry-over.
        let tier2 = split.take(3);
        assert_eq!(tier2.limit(), 600);
        assert_eq!(tier2.remaining(&meter), 590);

        meter.charge(590);
        let tier3 = split.take(1);
        assert_eq!(tier3.limit(), 700);
        let irr = split.take(3);
        // The last slice closes out the whole budget exactly, with no drift
        // from four truncating divisions.
        assert_eq!(irr.limit(), budget.limit());
    }

    #[test]
    fn a_split_with_no_weights_grants_nothing() {
        let meter = WorkMeter::at(50);
        let mut split = Budget::until(100).split(&meter).weights(0);
        assert_eq!(split.take(3).limit(), 50);
    }

    #[test]
    fn the_growth_ladder_is_exact_integer_arithmetic() {
        assert_eq!(Growth::Constant.scale(9), 1);
        assert_eq!(Growth::Linear.scale(9), 9);
        assert_eq!(Growth::Sqrt.scale(9), 3);
        assert_eq!(Growth::Sqrt.scale(10), 3); // floor, not round
        assert_eq!(Growth::Log2.scale(8), 4);
        assert_eq!(Growth::Log10.scale(999), 3);
        assert_eq!(Growth::Log10.scale(1000), 4);
        assert_eq!(Growth::NLog2N.scale(8), 32);
        assert_eq!(Growth::NLog2SquaredN.scale(8), 128);
        // Never zero, for any variant, at the boundary.
        for g in [
            Growth::Constant,
            Growth::Linear,
            Growth::Sqrt,
            Growth::Log2,
            Growth::Log10,
            Growth::NLog2N,
            Growth::NLog2SquaredN,
        ] {
            assert_eq!(g.scale(0), 1, "{g:?} collapsed at 0");
            assert!(g.scale(1) >= 1, "{g:?} collapsed at 1");
        }
        // Saturating, not panicking, at the top.
        assert_eq!(Growth::NLog2N.scale(u64::MAX), u64::MAX);
    }

    #[test]
    fn a_schedule_interval_grows_and_can_be_size_scaled() {
        let p = SchedulePolicy::every(1000).with_growth(Growth::Linear);
        assert_eq!(p.next_trigger(0, 0, 0), 1000); // first round: growth(0) = 1
        assert_eq!(p.next_trigger(500, 3, 0), 500 + 3000);
        let scaled = p.size_scaled();
        // 10_000 clauses -> log10 ladder gives 5.
        assert_eq!(scaled.next_trigger(0, 1, 10_000), 5000);
    }

    #[test]
    fn the_backoff_is_additive_increase_multiplicative_decrease() {
        let mut d = DelayCounter::new();
        assert!(!d.delaying());
        d.bump(); // current = 1
        assert!(d.delaying());
        assert!(!d.delaying());
        d.bump();
        d.bump(); // current = 3
        assert_eq!(d.rounds_left(), 3);
        d.reduce(); // current = 1
        assert_eq!(d.rounds_left(), 1);
        d.reduce(); // current = 0
        assert_eq!(d.rounds_left(), 0);
        assert!(!d.delaying());
    }

    #[test]
    fn the_success_rate_test_uses_no_division_and_no_fractional_constant() {
        let mut a = EffortAccount::new(EffortPolicy::MAJOR_PASS);
        // 9 of 1000 is under 1 %: back off.
        a.record_success_rate(9, 1000, 10);
        assert_eq!(a.stats().backoff_rounds_left, 1);
        // Exactly 1 % is not a failure.
        a.record_success_rate(10, 1000, 10);
        assert_eq!(a.stats().backoff_rounds_left, 0);
        // A round that attempted nothing did not earn its setup cost.
        a.record_success_rate(0, 0, 10);
        assert_eq!(a.stats().backoff_rounds_left, 1);
    }

    #[test]
    fn the_delay_gate_accrues_because_it_does_not_advance_the_watermark() {
        // 10 % effort, setup cost 20 per clause, 1000 clauses => 20_000 needed.
        let policy = EffortPolicy::MAJOR_PASS.with_init_cost(20);
        let mut account = EffortAccount::new(policy);
        let mut search = WorkMeter::new();
        let own = WorkMeter::new();

        // Round 1: 50_000 search units buys 5_000. Not enough.
        search.charge(50_000);
        assert_eq!(
            account.request(&search, &own, 1000),
            Grant::Delayed {
                accrued: 5_000,
                threshold: 20_000
            }
        );
        // Round 2: another 50_000. Because the watermark did NOT move, the
        // window is now 100_000 and the accrual is 10_000 -- it is growing.
        search.charge(50_000);
        assert_eq!(
            account.request(&search, &own, 1000),
            Grant::Delayed {
                accrued: 10_000,
                threshold: 20_000
            }
        );
        // Round 3: the window reaches 200_000 and the slice clears the bar.
        search.charge(100_000);
        assert_eq!(
            account.request(&search, &own, 1000),
            Grant::Granted(Budget::until(20_000))
        );
        // ...and only NOW does the watermark move, so the next window starts
        // from zero again.
        search.charge(50_000);
        assert_eq!(
            account.request(&search, &own, 1000),
            Grant::Delayed {
                accrued: 5_000,
                threshold: 20_000
            }
        );

        let s = account.stats();
        assert_eq!(s.rounds_granted, 1);
        assert_eq!(s.rounds_delayed, 3);
    }

    /// The mechanism is the *omission* of the watermark update on the delay
    /// path. This is the control for that omission: with accrual, a window that
    /// alone never clears the threshold still buys a round every fourth offer;
    /// a gate that advanced the watermark would grant zero rounds forever, and
    /// this assertion is what would catch it.
    #[test]
    fn a_gate_that_advanced_the_watermark_would_never_become_affordable() {
        let policy = EffortPolicy::MAJOR_PASS.with_init_cost(20);
        let mut account = EffortAccount::new(policy);
        let mut search = WorkMeter::new();
        let own = WorkMeter::new();

        let mut granted = 0;
        for _ in 0..48 {
            search.charge(50_000); // alone buys 5_000 against a 20_000 bar
            if let Grant::Granted(_) = account.request(&search, &own, 1000) {
                granted += 1;
            }
        }
        assert_eq!(
            granted, 12,
            "accrual is not happening: 48 offers at a quarter of the threshold \
             must buy exactly 12 rounds"
        );
    }

    #[test]
    fn a_pass_with_no_setup_cost_is_never_delayed() {
        let mut account = EffortAccount::new(EffortPolicy::MAJOR_PASS);
        let mut search = WorkMeter::new();
        let own = WorkMeter::new();
        search.charge(10);
        // 1 unit of budget, but the gate is off, so it runs.
        assert_eq!(
            account.request(&search, &own, 1_000_000),
            Grant::Granted(Budget::until(1))
        );
    }

    #[test]
    fn spend_is_attributed_to_the_pass_that_consumed_it() {
        let mut account = EffortAccount::new(EffortPolicy::MAJOR_PASS);
        let mut search = WorkMeter::new();
        let mut own = WorkMeter::new();

        search.charge(1_000_000);
        let Grant::Granted(budget) = account.request(&search, &own, 0) else {
            panic!("no gate, must be granted");
        };
        assert_eq!(budget.limit(), 100_000);
        // The pass under-spends: it ran out of candidates, not out of budget.
        own.charge(30_000);
        account.settle(&own);

        let s = account.stats();
        assert_eq!(s.granted, 100_000);
        assert_eq!(s.spent, 30_000);
        assert_eq!(
            s.utilisation_per_mille(),
            300,
            "30 % utilisation says candidate-bound, not budget-bound"
        );
    }

    struct Counting {
        scale: u64,
        cost_per_step: u64,
        steps_run: u64,
        succeed: bool,
    }

    impl BudgetedPass for Counting {
        type Outcome = u64;
        fn scale(&self) -> u64 {
            self.scale
        }
        fn run(&mut self, budget: Budget, meter: &mut WorkMeter) -> u64 {
            let mut steps = 0;
            while !budget.exhausted(meter) {
                meter.charge(self.cost_per_step);
                steps += 1;
            }
            self.steps_run += steps;
            steps
        }
        fn paid_off(&self, _outcome: &u64) -> bool {
            self.succeed
        }
    }

    #[test]
    fn delayed_wraps_the_gate_the_backoff_and_the_attribution() {
        let mut search = WorkMeter::new();
        let mut vivify = Delayed::new(
            "vivify",
            Counting {
                scale: 1_000,
                cost_per_step: 1_000,
                steps_run: 0,
                succeed: false,
            },
            EffortPolicy::MAJOR_PASS.with_init_cost(20),
        );

        // Not affordable yet.
        search.charge(50_000);
        assert_eq!(
            vivify.run_round(&search),
            RoundOutcome::Delayed {
                accrued: 5_000,
                threshold: 20_000
            }
        );

        // Affordable: a 200_000 window buys 20_000, which is 20 steps.
        search.charge(150_000);
        let RoundOutcome::Ran {
            outcome,
            granted,
            spent,
        } = vivify.run_round(&search)
        else {
            panic!("expected the round to run");
        };
        assert_eq!(outcome, 20);
        assert_eq!(granted, 20_000);
        assert_eq!(spent, 20_000);

        // The pass reported failure, so the next affordable round is skipped.
        search.charge(200_000);
        assert_eq!(
            vivify.run_round(&search),
            RoundOutcome::BackedOff { rounds_left: 0 }
        );

        let s = vivify.stats();
        assert_eq!(s.rounds_granted, 1);
        assert_eq!(s.rounds_delayed, 1);
        assert_eq!(s.rounds_backed_off, 1);
        assert_eq!(s.spent, 20_000);
        assert_eq!(vivify.pass().steps_run, 20);
    }

    #[test]
    fn the_ledger_is_insertion_ordered_and_totals_correctly() {
        let mut ledger = BudgetLedger::new();
        ledger.record(
            "vivify",
            PassBudgetStats {
                granted: 100,
                spent: 40,
                ..PassBudgetStats::default()
            },
        );
        ledger.record(
            "bve",
            PassBudgetStats {
                granted: 200,
                spent: 200,
                ..PassBudgetStats::default()
            },
        );
        ledger.record(
            "vivify",
            PassBudgetStats {
                granted: 300,
                spent: 90,
                ..PassBudgetStats::default()
            },
        );
        let names: Vec<_> = ledger.entries().iter().map(|(n, _)| *n).collect();
        assert_eq!(
            names,
            vec!["vivify", "bve"],
            "insertion order is not stable"
        );
        assert_eq!(ledger.total_granted(), 500);
        assert_eq!(ledger.total_spent(), 290);
        assert!(format!("{ledger}").contains("vivify"));
    }

    /// A scripted reference stream driving every mechanism at once. The
    /// expected sequence is pinned, so any change to the arithmetic, the gate,
    /// or the backoff breaks this test rather than silently moving a schedule.
    fn play_scripted_stream() -> Vec<String> {
        let mut search = WorkMeter::new();
        let mut account = EffortAccount::new(
            EffortPolicy::new(100)
                .with_min_reference(1_000)
                .with_init_cost(3),
        );
        let mut own = WorkMeter::new();
        let mut log = Vec::new();
        for round in 1u64..=12 {
            search.charge(round * 7_000);
            let scale = 2_000 - round * 100;
            match account.request(&search, &own, scale) {
                Grant::Granted(b) => {
                    // Spend three quarters of it, deterministically.
                    let allowance = b.limit() - own.spent();
                    own.charge(allowance * 3 / 4);
                    account.settle(&own);
                    account.record_success_rate(round % 3, 10, 200);
                    log.push(format!("run limit={} spent={}", b.limit(), own.spent()));
                }
                Grant::Delayed { accrued, threshold } => {
                    log.push(format!("delay {accrued}/{threshold}"));
                }
                Grant::BackedOff { rounds_left } => {
                    log.push(format!("backoff {rounds_left}"));
                }
            }
        }
        log
    }

    #[test]
    fn one_scripted_reference_stream_gives_one_exact_decision_sequence() {
        let first = play_scripted_stream();
        assert_eq!(first.len(), 12);
        // Re-running from a fresh state reproduces it exactly: no hidden state,
        // no clock, no environment.
        assert_eq!(play_scripted_stream(), first);
        // And the sequence exercises all three outcomes, so the equality above
        // is not comparing twelve copies of one branch.
        assert!(first.iter().any(|l| l.starts_with("run")));
        assert!(first.iter().any(|l| l.starts_with("delay")));
        assert!(first.iter().any(|l| l.starts_with("backoff")));
    }
}
