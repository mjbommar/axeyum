//! `SolverConfig::memory_limit_mb`, made to mean something on the pure-Rust path.
//!
//! # The defect this closes
//!
//! Until 2026-08-21 the field had exactly **one** read in the workspace —
//! `z3_backend.rs`, under `#[cfg(feature = "z3")]`. On the default build, which
//! is the shipped product, setting a memory limit did nothing whatsoever, and
//! nothing said so. A live caller (`axeyum-verify`'s `tock_log2_external`) set a
//! 2 GB cap on a non-`z3` build, where it was inert.
//!
//! That is the exact shape of the incident CLAUDE.md records for 2026-08-17: a
//! kernel OOM killed a live agent session because one test reached 125 GB, and
//! the lesson written down was "`recv_timeout` on a detached thread bounds
//! **time**, not memory". The solver had no memory bound at all.
//!
//! # What a faithful bound would need, and why it is not here
//!
//! A bound on *every* allocation a query makes needs a `#[global_allocator]`
//! hook. Three things make that an ADR-sized decision rather than a patch:
//!
//! - it is **process-global**, and a library must not install one on its
//!   consumer's behalf — the consumer may already have one, and only one exists;
//! - `impl GlobalAlloc` is `unsafe impl`, and `unsafe_code` is denied
//!   workspace-wide (an exception needs an ADR by the Hard Rules);
//! - attributing an allocation to *this* query needs thread-local accounting,
//!   which changes what a "budget" means for a multi-threaded consumer.
//!
//! So this module deliberately does **not** claim a faithful bound. It claims
//! three narrower things and states exactly where each stops.
//!
//! # The three mechanisms, and what each costs
//!
//! **1. A portable pre-allocation ceiling** ([`MemoryBudget::clause_ceiling`]).
//! The dominant allocation on the pure-Rust path is the bit-blasted AIG/CNF, and
//! `sat_bv_backend` already refuses an oversized encoding *before* `lower_terms`
//! allocates it — in clause units, against `cnf_clause_budget` or an absolute
//! ceiling. Translating megabytes into that same currency makes the field bite
//! on every target, deterministically, and **costs nothing on the hot path**: it
//! changes the value of a comparison that was already there, and adds no new
//! comparison. [`ENCODING_BYTES_PER_CLAUSE`] is the measured conversion.
//!
//! **2. A cooperative resident-set probe** ([`MemoryBudget::exceeded`]), Linux
//! only. This catches growth the clause estimate cannot predict — a route that
//! is not bit-blasting at all, or an encoding whose auxiliary maps outgrow the
//! CNF. It reads `/proc/self/status`.
//!
//! ## The probe's cost is measured, and it decides where the probe may go
//!
//! Measured on this host, 50 000 samples each, release:
//!
//! ```text
//! /proc/self/status  VmRSS:   9 395 ns/sample
//! /proc/self/statm   field 2  3 612 ns/sample
//! Instant::now() + elapsed        34 ns/sample
//! ```
//!
//! The probe is **276x an `Instant::now()`**, so it is categorically not a
//! deadline check and must never sit where a deadline check sits. It goes only
//! at *phase* boundaries — entry, after lowering, before the SAT search.
//! [`PROBE_COUNT`] exists so a test can assert that a check does not multiply
//! them; see `a_check_probes_only_at_phase_boundaries`, which pins the count in
//! **both** directions.
//!
//! ## The end-to-end cost, measured against a tree without this module
//!
//! Two `git archive` snapshots — one at `HEAD`, one with this module wired in —
//! built release, `taskset -c 0-7`, 2240 small `QF_BV` checks per round,
//! us/check, three rounds each (round 1 discarded as warm-up):
//!
//! ```text
//!                      no limit set     memory_limit_mb = 2048
//! baseline (HEAD)     185.3  184.0        181.8  181.4
//! with this module    182.8  183.4        218.0  215.3
//! ```
//!
//! Two readings, and both are the point:
//!
//! - **The default path costs nothing measurable.** 182.8-183.4 against a
//!   185.3-184.0 baseline: the added work when no limit is set is
//!   `Option::map` over a `None`, and it does not show above the noise.
//! - **A configured limit costs ~32 us per check, fixed** — three probes at
//!   9.4 us plus the branch. That is 0.00013 % of a 24 s competition budget,
//!   but it is **17 %** of these deliberately tiny 185 us checks, which is the
//!   honest worst case: the overhead is per *check*, not per unit of work, so
//!   it is only visible to a consumer making millions of trivial queries with
//!   a limit set. The baseline's own two columns are identical (181 vs 185),
//!   which is the field being inert — exactly the defect.
//!
//! The cheaper `/proc/self/statm` was **rejected**: it reports pages, and turning
//! pages into bytes needs the page size, which is 4096 on x86-64 but 16384 or
//! 65536 on some aarch64 kernels. Getting it right needs `sysconf` (an `unsafe`
//! FFI call this workspace denies); getting it wrong under-reports RSS by up to
//! 16x, and a guard that under-reports is a guard that does not fire. 5.8 us is
//! not worth a silent 16x error in the direction of not firing.
//!
//! One consequence of putting a probe at `check_auto`/`solve` rather than only
//! in the backend: routes that call an inner solve in a loop (CEGAR refinement,
//! quantifier instantiation, the fallback ladder) pay one probe per inner call.
//! At 9.4 us, ten thousand inner solves cost 94 ms. That is a real cost and it
//! is stated rather than buried — but a loop of inner solves is also precisely
//! where memory accumulates unobserved, so it is the place the probe earns the
//! most. Only a caller that sets the field pays it.
//!
//! **3. A sampling watchdog** ([`MemoryWatchdog`]), Linux only, added
//! 2026-09-08. Mechanisms 1 and 2 are both entry-shaped: the ceiling is
//! projected before lowering, and all five inline probes sit at boundaries the
//! process reaches while it is still small. Nothing sampled the resident set
//! again while a route allocated, so `--memory-limit-mb 8192` did not stop
//! three `QF_LRA` files reaching **26.6 GB in 18.2 s**, and the kernel OOM
//! killer ended them with no verdict, no trace and no span-log row
//! (`docs/research/12-performance/span-log-sweep-2026-09-08.md`).
//!
//! The reason mechanism 2 could not simply be moved into a loop is the 9.4 us
//! above. The watchdog moves the READ onto its own thread, sampling every
//! [`WATCHDOG_SAMPLE_INTERVAL`], and leaves the loop with
//! [`watchdog_tripped`] — one relaxed atomic load, which can go anywhere. The
//! sampler costs 0.047 % of one core while a budget is installed and nothing
//! at all otherwise: the thread is spawned on the first install and parks on a
//! condvar whenever no budget is set, so a process that never sets a limit
//! never spawns it.
//!
//! # What is NOT bounded, stated plainly
//!
//! - Allocation *between* two samples, or between a sample and the next
//!   cooperative check site. At the 20 ms interval a route allocating at
//!   1 GiB/s is at most ~20 MiB past the limit when the flag is set, plus
//!   whatever it allocates before reaching a check. Only the allocator hook
//!   above makes that zero.
//! - A route with NO cooperative check site is still unbounded. The sites are
//!   listed by `crate::memory_budget::watchdog_tripped`'s callers, and adding a
//!   route means adding one; nothing enforces that mechanically, and this
//!   sentence is the honest statement of it rather than a claim of coverage.
//! - Non-Linux targets get mechanism 1 only (the ceiling), never mechanism 2.
//!   The field is still not inert there — the ceiling is portable — but the
//!   resident-set half is absent and [`resident_bytes`] returns `None`.
//! - The probe reads **process** RSS, not this query's share, exactly as the
//!   field's existing doc says of Z3 ("Z3 applies this process-wide"). A
//!   consumer already over the limit before the check starts gets an immediate
//!   `Unknown`. That is deliberate: the hazard is the host dying, and it does
//!   not care which query allocated the bytes.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Condvar, Mutex, Once};
use std::time::Duration;

use crate::backend::{SolverConfig, UnknownKind, UnknownReason};

/// Bytes of encoding memory to charge per bit-blasted CNF clause.
///
/// **Measured, not assumed.** 2026-08-21, this host, peak resident set
/// (`VmHWM`) across one full lowering + AIG + Tseitin encoding in a **fresh
/// process per width**, over `bvmul` commutativity miters:
///
/// ```text
/// width   clauses    B/clause (release)   B/clause (debug)
///    32    14 775          309.1                359.0
///    64    61 287          271.9                286.6
///   128   249 543          262.8                266.6
///   192   564 775          245.3                247.0
///   256 1 006 983          259.9                260.9
///   384 2 272 327          243.6                244.0
///   512 4 045 575          258.7                  —
/// ```
///
/// Two things that measurement had to get right, both of which the obvious
/// method gets wrong in the **unsafe** direction:
///
/// - *Fresh process per width.* `VmHWM` is monotone, so several widths in one
///   process report only the largest.
/// - *Peak, not `VmRSS` delta.* Freed-then-reused heap makes a plain delta
///   under-report by 3-7x (measured: 28 B/clause at width 192 against a true
///   245), and for a ceiling, under-reporting is the dangerous direction —
///   it lets an encoding through that does not fit.
///
/// The value is set **above** every measurement (1.34x the 286.6 worst case at
/// a width whose fixed cost is amortized) precisely so it over-charges: a
/// larger number means a smaller clause ceiling, so the budget refuses earlier.
/// `crates/axeyum-solver/tests/memory_budget.rs` re-measures and fails if the
/// real cost climbs into this headroom.
///
/// Below ~64 bits the ratio is worse (452 B/clause at width 16) because a few
/// MB of fixed setup is charged against a few thousand clauses. That does not
/// matter for a ceiling: those encodings are kilobytes in absolute terms.
pub const ENCODING_BYTES_PER_CLAUSE: u64 = 384;

/// How many times [`MemoryBudget::exceeded`] has sampled the resident set in
/// this process. Used by the phase-boundary test; a probe is ~9.4 us, so a
/// change that multiplies this is a performance defect.
pub(crate) static PROBE_COUNT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Phase boundaries `SatBvBackend::check` probes at: entry, after bit-vector
/// lowering, and before the SAT search. Pinned by
/// `a_check_probes_only_at_phase_boundaries` in both directions — fewer means a
/// boundary went back to ignoring the field, more means a probe reached a loop.
#[cfg(test)]
pub(crate) const PROBES_PER_SAT_BV_CHECK: u64 = 3;

/// Every test that causes a probe takes this, because
/// `a_check_probes_only_at_phase_boundaries` reads the process-wide
/// [`PROBE_COUNT`] and a concurrent probing test lands inside its window. It
/// read 5 instead of 3 on the first run for exactly that reason. Nothing else
/// in this crate sets `memory_limit_mb`, and only a set limit probes, so this
/// lock covers every source in a `--lib` run.
#[cfg(test)]
pub(crate) static PROBE_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

// Test seam: readings `resident_bytes` hands out before falling back to the
// real one, oldest first. Thread-local, so parallel tests do not see each
// other's script.
//
// This exists because the three probe sites are a **chain** — only the first
// one over the limit can ever fire — so with real readings no test can depend
// on the second or third, and a mutation run confirmed exactly that: all three
// probes SURVIVED deletion because whichever one was left still rejected. That
// is the "six of seven guards removable because they share one rejection"
// shape CLAUDE.md warns about, and the fix is a seam, not more assertions.
//
// Scripting the reading also removes the alternative, which was to arrange a
// real resident set to cross a real limit *during* lowering. That is
// arrangeable on paper and hopeless in practice: the process's resident set in
// a `cargo test` binary is mostly other tests running in parallel.
#[cfg(test)]
thread_local! {
    static SCRIPTED_RESIDENT: std::cell::RefCell<std::collections::VecDeque<u64>> =
        const { std::cell::RefCell::new(std::collections::VecDeque::new()) };
}

/// Replaces the next `readings.len()` calls to [`resident_bytes`] on this
/// thread, then falls back to the real one.
#[cfg(test)]
pub(crate) fn script_resident_bytes(readings: &[u64]) {
    SCRIPTED_RESIDENT.with(|queue| {
        let mut queue = queue.borrow_mut();
        queue.clear();
        queue.extend(readings.iter().copied());
    });
}

/// Resident bytes for this process, or `None` when the target has no mechanism.
///
/// Linux only, by way of `/proc/self/status`'s `VmRSS:` line, which is reported
/// in kB and therefore needs no page-size assumption (see the module docs for
/// why the cheaper `statm` route was rejected).
#[must_use]
pub fn resident_bytes() -> Option<u64> {
    #[cfg(test)]
    if let Some(scripted) = SCRIPTED_RESIDENT.with(|queue| queue.borrow_mut().pop_front()) {
        return Some(scripted);
    }
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        parse_vm_rss_kb(&status).map(|kb| kb.saturating_mul(1024))
    }
    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

/// The `VmRSS:` value in kB from a `/proc/self/status` body.
///
/// Split out from [`resident_bytes`] so it is testable on every target, not
/// only the one that has the file.
#[must_use]
pub(crate) fn parse_vm_rss_kb(status: &str) -> Option<u64> {
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmRSS:") {
            return rest.split_ascii_whitespace().next()?.parse().ok();
        }
    }
    None
}

/// A per-query memory budget, built from [`SolverConfig::memory_limit_mb`].
#[derive(Debug, Clone, Copy)]
pub struct MemoryBudget {
    limit_bytes: u64,
}

impl MemoryBudget {
    /// The budget for this configuration, or `None` when no limit is set.
    ///
    /// `Some` for *every* target: mechanism 1 (the pre-allocation ceiling) is
    /// portable, so a configured limit is never silently ignored. Only
    /// [`MemoryBudget::exceeded`] is target-dependent, and it says so by
    /// returning `None` rather than by pretending the budget is satisfied.
    #[must_use]
    pub fn from_config(config: &SolverConfig) -> Option<Self> {
        config.memory_limit_mb.map(|mb| Self {
            // A limit so large it overflows bytes is the same as no limit; saturate
            // rather than wrap, which would turn a huge cap into a tiny one.
            limit_bytes: mb.saturating_mul(1024 * 1024),
        })
    }

    /// The largest bit-blasted CNF, in clauses, that this budget can hold.
    ///
    /// Mechanism 1. Deterministic and target-independent; the caller takes the
    /// minimum of this and any explicit `cnf_clause_budget`.
    #[must_use]
    pub fn clause_ceiling(self) -> u64 {
        self.limit_bytes / ENCODING_BYTES_PER_CLAUSE
    }

    /// Samples the resident set and classifies an overrun.
    ///
    /// Mechanism 2. `None` means "not over the limit **or** not observable" —
    /// the two are deliberately merged at the call site, because a caller that
    /// could distinguish them would have to decide what to do about a target
    /// with no `/proc`, and the answer is the same as being under budget: keep
    /// going, with mechanism 1 still in force.
    ///
    /// `phase` names the checkpoint and appears in the `Unknown` detail, so a
    /// consumer can tell "arrived over budget" from "the encoding pushed it
    /// over" without re-running.
    #[must_use]
    pub fn exceeded(self, phase: &str) -> Option<UnknownReason> {
        PROBE_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let resident = resident_bytes()?;
        if resident <= self.limit_bytes {
            return None;
        }
        Some(UnknownReason {
            kind: UnknownKind::MemoryLimit,
            detail: format!(
                "resident set {} MiB exceeds memory_limit_mb {} at {phase}",
                resident / (1024 * 1024),
                self.limit_bytes / (1024 * 1024),
            ),
        })
    }

    /// The `Unknown` for an encoding that mechanism 1 refuses.
    ///
    /// Separate from [`MemoryBudget::exceeded`] because the two are different
    /// findings and a consumer reading the detail should not have to guess
    /// which one fired: this one never allocated the encoding, so nothing was
    /// measured — the number quoted is a projection.
    #[must_use]
    pub fn encoding_refusal(self, projected_clauses: u64, what: &str) -> UnknownReason {
        UnknownReason {
            kind: UnknownKind::MemoryLimit,
            detail: format!(
                "{what} {projected_clauses} CNF clauses needs about {} MiB at \
                 {ENCODING_BYTES_PER_CLAUSE} B/clause, over memory_limit_mb {}",
                projected_clauses.saturating_mul(ENCODING_BYTES_PER_CLAUSE) / (1024 * 1024),
                self.limit_bytes / (1024 * 1024),
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Mechanism 3: a sampling watchdog, so the limit binds where the bytes are.
// ---------------------------------------------------------------------------
//
// # The defect this closes, measured
//
// Mechanisms 1 and 2 above left the field enforced only at ENTRY-LIKE
// boundaries: `solve` entry, `check_auto` entry, and `SatBvBackend`'s three
// phases. All five run when the process is small. Nothing sampled the resident
// set again while a route allocated, so a query that arrived under budget could
// not be stopped however far over it went.
//
// Measured 2026-09-08 (`docs/research/12-performance/span-log-sweep-2026-09-08.md`):
// three `QF_LRA` files reached **26.6 GB resident in 18.2 s under
// `--memory-limit-mb 8192`** and were killed by the kernel OOM killer. A
// kernel kill loses the verdict, the trace and the span log, so each file left
// no row at all and the division silently reported 47 files for a 50-file list.
//
// The module docs above explain why mechanism 2 is probes and not a loop check,
// and the reason was real: a `/proc` read is 9.4 us, 276x an `Instant::now()`,
// and cannot go inside a Fourier-Motzkin cross product. The resolution is to
// move the READ onto another thread and leave the loop with a relaxed atomic
// load, which can go anywhere.

/// How often the watchdog thread reads the resident set while a budget is
/// installed.
///
/// The read costs ~9.4 us, so sampling at 20 ms spends **0.047 %** of one
/// core — a cost that does not depend on how many checks the caller makes,
/// which is the whole reason the sampler is a thread rather than another inline
/// probe. It is the inline probes that cost 32 us *per check*.
///
/// 20 ms also bounds the overshoot: a route allocating at 1 GiB/s can be at
/// most ~20 MiB past the limit before the flag is set, plus whatever it
/// allocates before the next cooperative check site.
pub(crate) const WATCHDOG_SAMPLE_INTERVAL: Duration = Duration::from_millis(20);

/// How long the watchdog thread waits before re-checking for a newly installed
/// budget when none is installed. It is parked on a condvar that an install
/// notifies, so this is a backstop against a missed notification, not a poll
/// rate.
const WATCHDOG_IDLE_INTERVAL: Duration = Duration::from_millis(500);

/// The installed budget in bytes; `0` means no budget is installed. Written
/// only by [`MemoryWatchdog::install`] and its `Drop`.
static WATCHDOG_LIMIT_BYTES: AtomicU64 = AtomicU64::new(0);

/// Set by the sampler the first time it reads a resident set over the installed
/// budget, and cleared when a budget is installed or uninstalled. **Sticky**
/// for the life of the guard: once the process has been over the limit, every
/// cooperative check site declines, and whichever route reaches one first is
/// the one that reports it.
static WATCHDOG_TRIPPED: AtomicBool = AtomicBool::new(false);

/// The largest resident set the sampler observed since the budget was
/// installed. Reported in the decline, so a consumer learns HOW far over it
/// went rather than only that it went over.
static WATCHDOG_PEAK_BYTES: AtomicU64 = AtomicU64::new(0);

/// How many samples the watchdog thread has taken in this process. A test uses
/// it to wait for a sample rather than sleeping a guessed duration.
static WATCHDOG_SAMPLES: AtomicU64 = AtomicU64::new(0);

/// Install depth. Only the outermost install owns the budget: `check_auto`
/// recurses (CEGAR refinement, quantifier instantiation, the fallback ladder),
/// and an inner install that reset the trip flag would erase the observation
/// the outer one is about to act on.
static WATCHDOG_DEPTH: AtomicU64 = AtomicU64::new(0);

static WATCHDOG_THREAD: Once = Once::new();

/// Woken by [`MemoryWatchdog::install`] so a newly installed budget starts
/// being sampled immediately rather than up to [`WATCHDOG_IDLE_INTERVAL`]
/// later.
static WATCHDOG_WAKE: (Mutex<bool>, Condvar) = (Mutex::new(false), Condvar::new());

/// Test seam: a resident-set reading the SAMPLER sees instead of the real one.
///
/// It is a separate seam from [`script_resident_bytes`] and it has to be: that
/// one is thread-local, so it is invisible to the sampler, which runs on its
/// own thread. Nothing else can express "the process is over its budget"
/// without really allocating gigabytes inside a `cargo test` binary.
#[cfg(test)]
pub(crate) static SAMPLER_OVERRIDE_BYTES: AtomicU64 = AtomicU64::new(0);

/// What the sampler reads.
///
/// Split from [`resident_bytes`] for two reasons, both load-bearing: the
/// sampler's test seam must be process-global (see [`SAMPLER_OVERRIDE_BYTES`]),
/// and the sampler must never touch [`PROBE_COUNT`], which pins the number of
/// INLINE probes in a check and would otherwise become a measurement of how
/// long that check took.
fn sampled_resident_bytes() -> Option<u64> {
    #[cfg(test)]
    {
        let forced = SAMPLER_OVERRIDE_BYTES.load(Ordering::Relaxed);
        if forced != 0 {
            return Some(forced);
        }
    }
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        parse_vm_rss_kb(&status).map(|kb| kb.saturating_mul(1024))
    }
    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

/// Peak resident set for this process (`VmHWM`), or `None` when the target has
/// no mechanism.
///
/// This is the kernel's own high-water mark, so it needs no sampling and cannot
/// miss a spike between two samples — which is why the span log reports THIS
/// and not [`watchdog_peak_bytes`]. It is monotone per process, so on a
/// one-query-per-process harness (`smtcomp_cli`) it is that query's peak, and
/// in a long-lived process it is the peak since the process started; a consumer
/// that needs a per-query figure must fork.
#[must_use]
pub fn peak_resident_bytes() -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        for line in status.lines() {
            if let Some(rest) = line.strip_prefix("VmHWM:") {
                return rest
                    .split_ascii_whitespace()
                    .next()?
                    .parse::<u64>()
                    .ok()
                    .map(|kb| kb.saturating_mul(1024));
            }
        }
        None
    }
    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

/// The installed memory budget in bytes, or `None` when none is installed.
///
/// # Why a process-global, and not a parameter
///
/// The routes that allocate the most do not have a [`SolverConfig`]:
/// `lra::decide_within` takes `(arena, assertions, deadline)` and is four call
/// frames below the last function that has one. Threading the config down would
/// be a wide mechanical diff through code the change is not about, and the
/// field's contract is already process-scoped — its own doc says Z3 applies it
/// process-wide, and [`MemoryBudget::exceeded`] reads PROCESS resident set.
/// So the front door installs the budget and any depth can read it.
///
/// The honest cost of that choice, stated rather than discovered: a consumer
/// running two queries with different limits on two threads gets the outermost
/// installer's limit for both. That is the same limitation the resident-set
/// probe already has.
#[must_use]
pub(crate) fn current_limit_bytes() -> Option<u64> {
    match WATCHDOG_LIMIT_BYTES.load(Ordering::Relaxed) {
        0 => None,
        bytes => Some(bytes),
    }
}

/// Whether the sampler has seen the process over its installed budget.
///
/// **This is the check that goes on a hot path.** One relaxed atomic load,
/// against 9 400 ns for [`MemoryBudget::exceeded`]'s `/proc` read — which is
/// what makes it affordable inside a Fourier–Motzkin cross product or a pivot
/// loop, the places an inline `/proc` read could never go and therefore
/// precisely the places where the limit never bound.
#[must_use]
#[inline]
pub(crate) fn watchdog_tripped() -> bool {
    WATCHDOG_TRIPPED.load(Ordering::Relaxed)
}

/// The largest resident set the sampler has seen since the budget was
/// installed, or 0 when it has taken no sample.
#[must_use]
pub(crate) fn watchdog_peak_bytes() -> u64 {
    WATCHDOG_PEAK_BYTES.load(Ordering::Relaxed)
}

/// The `Unknown` for a route that found the watchdog tripped, or `None` when it
/// is not.
///
/// `phase` names the loop that noticed, so a consumer can tell WHICH route was
/// holding the bytes — the distinction a kernel OOM kill destroys, and the
/// reason this exists at all.
#[must_use]
pub(crate) fn watchdog_decline(phase: &str) -> Option<UnknownReason> {
    if !watchdog_tripped() {
        return None;
    }
    let limit = WATCHDOG_LIMIT_BYTES.load(Ordering::Relaxed);
    Some(UnknownReason {
        kind: UnknownKind::MemoryLimit,
        detail: format!(
            "memory watchdog: resident set reached {} MiB over the {} MiB \
             memory_limit_mb, observed at {phase}",
            watchdog_peak_bytes() / (1024 * 1024),
            limit / (1024 * 1024),
        ),
    })
}

/// Installs [`SolverConfig::memory_limit_mb`] as a process-global budget and
/// samples the resident set against it for as long as the guard lives.
///
/// # Nesting
///
/// Only the outermost guard owns the budget. `check_auto` re-enters itself, and
/// an inner install that cleared [`WATCHDOG_TRIPPED`] would erase an
/// observation the outer route is about to act on.
#[derive(Debug)]
pub(crate) struct MemoryWatchdog {
    /// Whether this guard is the one that installed the budget.
    outermost: bool,
}

impl MemoryWatchdog {
    /// Installs the budget, or `None` when the caller set no limit or the
    /// target cannot observe a resident set.
    ///
    /// `None` for an unobservable target is NOT the field going inert there:
    /// [`MemoryBudget::clause_ceiling`] is portable and still applies. What is
    /// absent is only the half that needs `/proc`, and the absence is reported
    /// by returning `None` rather than by installing a watchdog that could
    /// never fire.
    pub(crate) fn install(config: &SolverConfig) -> Option<Self> {
        let limit = config
            .memory_limit_mb
            .map(|mb| mb.saturating_mul(1024 * 1024))?;
        sampled_resident_bytes()?;
        let depth = WATCHDOG_DEPTH.fetch_add(1, Ordering::AcqRel);
        if depth != 0 {
            return Some(Self { outermost: false });
        }
        WATCHDOG_PEAK_BYTES.store(0, Ordering::Relaxed);
        WATCHDOG_TRIPPED.store(false, Ordering::Relaxed);
        WATCHDOG_LIMIT_BYTES.store(limit, Ordering::Release);
        WATCHDOG_THREAD.call_once(spawn_watchdog);
        wake_watchdog();
        Some(Self { outermost: true })
    }
}

impl Drop for MemoryWatchdog {
    fn drop(&mut self) {
        if self.outermost {
            // The LIMIT goes first: the sampler reads it before anything else,
            // so from here on it idles.
            WATCHDOG_LIMIT_BYTES.store(0, Ordering::Release);
            WATCHDOG_TRIPPED.store(false, Ordering::Relaxed);
        }
        WATCHDOG_DEPTH.fetch_sub(1, Ordering::AcqRel);
    }
}

fn wake_watchdog() {
    let (lock, condvar) = &WATCHDOG_WAKE;
    if let Ok(mut armed) = lock.lock() {
        *armed = true;
        condvar.notify_all();
    }
}

/// The sampler: one thread per process, spawned on the first install and never
/// joined. It parks on a condvar whenever no budget is installed, so a process
/// that sets a limit once does not pay for a thread that polls forever, and a
/// process that never sets one never spawns it at all.
fn spawn_watchdog() {
    let spawned = std::thread::Builder::new()
        .name("axeyum-memory-watchdog".to_owned())
        .stack_size(64 * 1024)
        .spawn(watchdog_loop);
    // A process that cannot spawn a thread is already in trouble; the inline
    // probes and the clause ceiling remain, so this degrades rather than fails.
    drop(spawned);
}

fn watchdog_loop() {
    loop {
        let limit = WATCHDOG_LIMIT_BYTES.load(Ordering::Acquire);
        if limit == 0 {
            let (lock, condvar) = &WATCHDOG_WAKE;
            let Ok(armed) = lock.lock() else { return };
            let Ok((mut armed, _)) = condvar.wait_timeout(armed, WATCHDOG_IDLE_INTERVAL) else {
                return;
            };
            *armed = false;
            continue;
        }
        if let Some(resident) = sampled_resident_bytes() {
            WATCHDOG_SAMPLES.fetch_add(1, Ordering::Relaxed);
            WATCHDOG_PEAK_BYTES.fetch_max(resident, Ordering::Relaxed);
            if resident > limit {
                WATCHDOG_TRIPPED.store(true, Ordering::Relaxed);
            }
        }
        std::thread::sleep(WATCHDOG_SAMPLE_INTERVAL);
    }
}

/// Blocks until the sampler has taken at least one more sample than it had when
/// called, or the wait times out; returns whether a sample was observed. A test
/// that slept a guessed duration instead would be a test of this host's
/// scheduler.
#[cfg(test)]
pub(crate) fn wait_for_watchdog_sample(timeout: Duration) -> bool {
    let before = WATCHDOG_SAMPLES.load(Ordering::Relaxed);
    let deadline = std::time::Instant::now() + timeout;
    while std::time::Instant::now() < deadline {
        if WATCHDOG_SAMPLES.load(Ordering::Relaxed) > before {
            return true;
        }
        std::thread::sleep(Duration::from_millis(1));
    }
    false
}

/// Test seam: assert the tripped state directly, without arranging a real
/// over-limit resident set.
///
/// The two halves of this mechanism fail differently and so are tested
/// separately: whether the SAMPLER trips on an over-limit reading
/// (`the_watchdog_samples_and_trips_on_an_over_limit_reading`), and whether a
/// COOPERATIVE CHECK SITE turns a tripped watchdog into a reported `unknown`
/// (this seam). Arranging both at once needs a test that really allocates past
/// a real limit inside a parallel `cargo test` binary, where the resident set
/// is mostly other tests.
#[cfg(test)]
pub(crate) fn trip_watchdog_for_test(limit_bytes: u64, peak_bytes: u64) {
    WATCHDOG_LIMIT_BYTES.store(limit_bytes, Ordering::Relaxed);
    WATCHDOG_PEAK_BYTES.store(peak_bytes, Ordering::Relaxed);
    WATCHDOG_TRIPPED.store(true, Ordering::Relaxed);
}

/// Undoes [`trip_watchdog_for_test`]. Every test that trips must clear: the
/// state is process-global, and a leaked trip declines every later test in the
/// binary.
#[cfg(test)]
pub(crate) fn clear_watchdog_for_test() {
    WATCHDOG_TRIPPED.store(false, Ordering::Relaxed);
    WATCHDOG_LIMIT_BYTES.store(0, Ordering::Relaxed);
    WATCHDOG_PEAK_BYTES.store(0, Ordering::Relaxed);
    SAMPLER_OVERRIDE_BYTES.store(0, Ordering::Relaxed);
}

/// Serializes every test that touches the process-global watchdog state, for
/// the same reason [`PROBE_LOCK`] exists: the state is one word shared by the
/// whole test binary, and two tests scripting it concurrently read each other's
/// script.
#[cfg(test)]
pub(crate) static WATCHDOG_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_limit_is_no_budget() {
        assert!(MemoryBudget::from_config(&SolverConfig::default()).is_none());
    }

    #[test]
    fn megabytes_convert_to_a_clause_ceiling() {
        let config = SolverConfig::default().with_memory_limit_mb(1024);
        let budget = MemoryBudget::from_config(&config).expect("a limit is a budget");
        assert_eq!(
            budget.clause_ceiling(),
            1024 * 1024 * 1024 / ENCODING_BYTES_PER_CLAUSE
        );
    }

    /// A limit large enough to overflow `u64` bytes must saturate, not wrap.
    /// Wrapping would turn "no practical limit" into a tiny one — a budget that
    /// refuses everything, which is the failure mode that looks like a solver
    /// regression rather than a config bug.
    #[test]
    fn an_absurd_limit_saturates_rather_than_wrapping() {
        let config = SolverConfig::default().with_memory_limit_mb(u64::MAX);
        let budget = MemoryBudget::from_config(&config).expect("a limit is a budget");
        // Wrapping would make this a handful of clauses instead of ~4.8e16.
        assert_eq!(
            budget.clause_ceiling(),
            u64::MAX / ENCODING_BYTES_PER_CLAUSE
        );
        assert!(budget.clause_ceiling() > 1 << 40);
    }

    #[test]
    fn vm_rss_is_parsed_from_the_status_body() {
        let body = "Name:\tprobe\nVmPeak:\t 1000 kB\nVmRSS:\t   2048 kB\nThreads:\t1\n";
        assert_eq!(parse_vm_rss_kb(body), Some(2048));
        // A body with no VmRSS is "not observable", never "zero" — reporting 0
        // would read as "far under budget" and silently disable the guard.
        assert_eq!(parse_vm_rss_kb("Name:\tprobe\nThreads:\t1\n"), None);
        assert_eq!(parse_vm_rss_kb("VmRSS:\tnot-a-number kB\n"), None);
    }

    /// A budget under the process's own resident set must fire. Uses the live
    /// process rather than a fixture, so it also proves the mechanism exists
    /// here at all — a fixture would pass on a target with no `/proc`.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_budget_below_the_live_resident_set_fires() {
        let _guard = PROBE_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let resident = resident_bytes().expect("Linux exposes VmRSS");
        assert!(resident > 0, "a running process has a nonzero resident set");
        let budget = MemoryBudget { limit_bytes: 0 };
        let reason = budget.exceeded("test").expect("0 bytes is under any RSS");
        assert_eq!(reason.kind, UnknownKind::MemoryLimit);
        assert!(reason.detail.contains("at test"), "{}", reason.detail);

        let generous = MemoryBudget {
            limit_bytes: resident.saturating_mul(1000).max(1 << 40),
        };
        assert!(generous.exceeded("test").is_none());
    }

    /// A `SatBvBackend::check` must probe the resident set a small, FIXED number
    /// of times.
    ///
    /// Both halves of the bound matter and they fail differently:
    ///
    /// - the **lower** bound fails if the wiring is removed, which is the whole
    ///   defect this module exists to close — a configured limit that probes
    ///   zero times is the inert field again;
    /// - the **upper** bound fails if a probe migrates onto a hot path. At
    ///   9.4 us it is 276x an `Instant::now()`, so one per CNF clause on a
    ///   2 M-clause encoding would cost 19 s against a 24 s budget.
    #[test]
    fn a_check_probes_only_at_phase_boundaries() {
        use axeyum_ir::TermArena;
        use std::sync::atomic::Ordering::Relaxed;

        use crate::backend::SolverBackend;
        use crate::sat_bv_backend::SatBvBackend;

        let _guard = PROBE_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);

        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 16).unwrap();
        let y = arena.bv_var("y", 16).unwrap();
        let product = arena.bv_mul(x, y).unwrap();
        let target = arena.bv_const(16, 0x5a5a).unwrap();
        let assertion = arena.eq(product, target).unwrap();

        // A limit large enough that no gate fires: this measures probe SITES,
        // not refusals.
        let config = SolverConfig::default().with_memory_limit_mb(1 << 20);
        let before = PROBE_COUNT.load(Relaxed);
        let _ = SatBvBackend::new()
            .check(&arena, &[assertion], &config)
            .expect("the backend decides a 16-bit product");
        let probes = PROBE_COUNT.load(Relaxed) - before;

        assert_eq!(
            probes, PROBES_PER_SAT_BV_CHECK,
            "SatBvBackend::check probed {probes} times; the module documents \
             {PROBES_PER_SAT_BV_CHECK} phase boundaries. Fewer means a boundary \
             lost its probe (the field goes back to being inert there); more \
             means a probe reached a loop, and at 9.4 us each that is a \
             performance defect, not a rounding error."
        );
    }

    /// [`ENCODING_BYTES_PER_CLAUSE`] must stay an OVER-estimate of what an
    /// encoding really costs, because the ceiling divides by it: too small a
    /// number lets through an encoding that does not fit, which is the failure
    /// that matters.
    ///
    /// Measured out of process, one width per child, for two reasons that both
    /// break the obvious in-process version:
    ///
    /// - `VmHWM` is monotone per process, so a second width in the same process
    ///   measures nothing;
    /// - a `cargo test` binary runs its tests in parallel, so a peak-RSS reading
    ///   in the shared process is another test's memory as much as this one's.
    ///
    /// A plain `VmRSS` delta was tried first and under-reported by 3-7x
    /// (28 B/clause at width 192 against a true 245) because freed heap is
    /// reused — under-reporting in exactly the direction that would let the
    /// constant rot downward unnoticed.
    #[cfg(target_os = "linux")]
    #[test]
    #[allow(clippy::cast_precision_loss)] // a byte count near 2^52 is not reachable here
    fn encoding_bytes_per_clause_is_not_an_under_estimate() {
        const WIDTH_ENV: &str = "AXEYUM_MEMORY_BUDGET_MEASURE_WIDTH";
        const TEST: &str =
            "memory_budget::tests::encoding_bytes_per_clause_is_not_an_under_estimate";

        if let Ok(width) = std::env::var(WIDTH_ENV) {
            measure_child(width.parse().expect("width"));
            return;
        }

        let exe = std::env::current_exe().expect("this test binary has a path");
        let mut measured = Vec::new();
        for width in [192u32, 256] {
            let output = std::process::Command::new(&exe)
                .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
                .env(WIDTH_ENV, width.to_string())
                .output()
                .expect("re-run this test binary for one width");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let line = stdout
                .lines()
                .find_map(|line| line.split("MEASURED ").nth(1))
                .unwrap_or_else(|| {
                    panic!("child for width {width} printed no measurement:\n{stdout}")
                });
            let bytes_per_clause: f64 = line.parse().expect("a measurement is a number");
            measured.push((width, bytes_per_clause));
        }

        for (width, bytes_per_clause) in measured {
            assert!(
                bytes_per_clause > 0.0,
                "width {width} measured nothing: a zero here is a broken \
                 measurement, not a free encoding"
            );
            assert!(
                bytes_per_clause <= ENCODING_BYTES_PER_CLAUSE as f64,
                "width {width} costs {bytes_per_clause:.1} B/clause, over the \
                 {ENCODING_BYTES_PER_CLAUSE} the memory budget charges. The \
                 clause ceiling divides by that constant, so an under-charge \
                 admits encodings the budget cannot hold. Raise the constant \
                 (and re-check what it does to callers' ceilings), or find what \
                 made the encoding fatter."
            );
        }
    }

    /// One width, in this (fresh) process: encode and report peak-RSS growth per
    /// clause on stdout for the parent to read.
    #[cfg(target_os = "linux")]
    #[allow(clippy::cast_precision_loss)] // ditto
    fn measure_child(width: u32) {
        use axeyum_ir::TermArena;

        use crate::backend::SolverBackend;
        use crate::sat_bv_backend::SatBvBackend;

        fn peak_rss_bytes() -> u64 {
            let status = std::fs::read_to_string("/proc/self/status").expect("procfs");
            for line in status.lines() {
                if let Some(rest) = line.strip_prefix("VmHWM:") {
                    let kb: u64 = rest
                        .split_ascii_whitespace()
                        .next()
                        .and_then(|value| value.parse().ok())
                        .expect("VmHWM is a kB count");
                    return kb * 1024;
                }
            }
            panic!("no VmHWM in /proc/self/status");
        }

        let mut arena = TermArena::new();
        let x = arena.bv_var("x", width).unwrap();
        let y = arena.bv_var("y", width).unwrap();
        let left = arena.bv_mul(x, y).unwrap();
        let right = arena.bv_mul(y, x).unwrap();
        let equal = arena.eq(left, right).unwrap();
        let assertion = arena.not(equal).unwrap();

        // `resource_limit` 0 stops the SAT search the moment it starts, so this
        // measures the ENCODING — which is what the ceiling has to predict.
        let config = SolverConfig::default().with_resource_limit(0);
        let before = peak_rss_bytes();
        let mut backend = SatBvBackend::new();
        let _ = backend.check(&arena, &[assertion], &config).expect("check");
        let after = peak_rss_bytes();
        let clauses = backend
            .last_stats()
            .expect("the backend records stats")
            .backend
            .iter()
            .find(|(name, _)| name == "cnf_clauses")
            .map_or(0.0, |(_, value)| *value);
        assert!(clauses > 0.0, "width {width} encoded no clauses");
        println!("MEASURED {}", after.saturating_sub(before) as f64 / clauses);
    }
}

/// The sampling watchdog: the half of the memory limit that binds while a route
/// is allocating, rather than only at the door.
#[cfg(test)]
mod watchdog_tests {
    use super::*;

    /// Every test here takes this: the watchdog's state is process-global, so
    /// two tests scripting it concurrently read each other's script.
    fn locked() -> std::sync::MutexGuard<'static, ()> {
        let guard = WATCHDOG_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clear_watchdog_for_test();
        guard
    }

    /// The sampler reads the resident set, records the peak, and trips when it
    /// is over the installed budget.
    ///
    /// Both directions are asserted in ONE test and in this order, because the
    /// under-budget half is the negative control: without it, a watchdog that
    /// trips unconditionally would pass the over-budget half. This is the guard
    /// that turns a 26.6 GB kernel kill into a reported `unknown`, and a guard
    /// that cannot fail to fire is as useless as one that cannot fire.
    #[test]
    fn the_watchdog_samples_and_trips_on_an_over_limit_reading() {
        let _lock = locked();
        let config = SolverConfig::default().with_memory_limit_mb(1024);

        // Under budget: the sampler runs and does NOT trip.
        SAMPLER_OVERRIDE_BYTES.store(512 * 1024 * 1024, Ordering::Relaxed);
        let watchdog = MemoryWatchdog::install(&config).expect("Linux installs a watchdog");
        assert!(
            wait_for_watchdog_sample(Duration::from_secs(5)),
            "the sampler never took a sample; nothing below is a measurement"
        );
        assert!(
            !watchdog_tripped(),
            "512 MiB is under a 1024 MiB budget: a watchdog that trips here \
             would decline every query the moment a limit is set"
        );
        assert_eq!(watchdog_peak_bytes(), 512 * 1024 * 1024);
        assert!(watchdog_decline("test").is_none());

        // Over budget: the same sampler trips, and the decline names both
        // numbers plus the phase that observed it.
        SAMPLER_OVERRIDE_BYTES.store(4096 * 1024 * 1024, Ordering::Relaxed);
        assert!(
            wait_for_watchdog_sample(Duration::from_secs(5)),
            "the sampler stopped sampling"
        );
        assert!(watchdog_tripped(), "4096 MiB is over a 1024 MiB budget");
        let reason = watchdog_decline("the elimination loop").expect("a tripped watchdog declines");
        assert_eq!(reason.kind, UnknownKind::MemoryLimit);
        assert!(
            reason.detail.contains("4096 MiB")
                && reason.detail.contains("1024 MiB")
                && reason.detail.contains("the elimination loop"),
            "a decline must say how far over, what the budget was, and where it \
             was seen: {}",
            reason.detail
        );

        drop(watchdog);
        clear_watchdog_for_test();
    }

    /// No limit set is no watchdog and no thread — the default build pays
    /// nothing at all, which is the property the module's A/B measured.
    #[test]
    fn no_limit_installs_no_watchdog() {
        let _lock = locked();
        assert!(MemoryWatchdog::install(&SolverConfig::default()).is_none());
        assert_eq!(current_limit_bytes(), None);
        assert!(!watchdog_tripped());
    }

    /// A nested install must not clear the outer guard's trip.
    ///
    /// `check_auto` re-enters itself on every fallback rung, CEGAR round and
    /// quantifier instantiation, so without the depth counter an inner install
    /// would erase the observation the outer route is about to report — and the
    /// query would carry on allocating exactly as it did before this existed.
    #[test]
    fn a_nested_install_does_not_erase_the_outer_trip() {
        let _lock = locked();
        let config = SolverConfig::default().with_memory_limit_mb(1024);
        SAMPLER_OVERRIDE_BYTES.store(4096 * 1024 * 1024, Ordering::Relaxed);
        let outer = MemoryWatchdog::install(&config).expect("outer install");
        assert!(wait_for_watchdog_sample(Duration::from_secs(5)));
        assert!(watchdog_tripped());

        let inner = MemoryWatchdog::install(&config).expect("inner install");
        assert!(watchdog_tripped(), "the inner install cleared the trip");
        drop(inner);
        assert!(
            watchdog_tripped(),
            "dropping the inner guard uninstalled the outer budget"
        );
        assert_eq!(current_limit_bytes(), Some(1024 * 1024 * 1024));

        drop(outer);
        assert_eq!(
            current_limit_bytes(),
            None,
            "the outermost drop must uninstall the budget"
        );
        clear_watchdog_for_test();
    }

    /// `VmHWM` is readable on this target and is at least the live resident set.
    ///
    /// This is the span log's memory instrument, so a `None` here would mean the
    /// gallery silently shows `null` for every run on Linux — the same shape of
    /// blindness the sweep just spent a day removing.
    #[cfg(target_os = "linux")]
    #[test]
    fn the_peak_resident_instrument_reads_a_real_high_water_mark() {
        let peak = peak_resident_bytes().expect("Linux exposes VmHWM");
        let live = resident_bytes().expect("Linux exposes VmRSS");
        assert!(peak > 0, "a running process has a nonzero peak");
        assert!(
            peak >= live,
            "VmHWM {peak} is below the live VmRSS {live}, which is not a \
             high-water mark"
        );
    }
}
