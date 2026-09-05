//! Roadmap-aligned **progress-frontier** regression suite (oracle-free).
//!
//! This is the missing *frontier* counterpart to the soundness-only corpus gate
//! ([`corpus_regression.rs`](./corpus_regression.rs)). Where that gate asks "did
//! we ever return a wrong verdict?", this one asks "**how far** can axeyum push
//! a parametric family before it runs out of room?" — and pins that reach as a
//! committed baseline so a roadmap lever improving raises a visible number and a
//! regression lowers it past the floor (a hard test failure).
//!
//! # The frontier metric
//!
//! Each benchmark *family* has a difficulty knob `N = 1, 2, 3, …`. As `N` grows
//! the instance gets harder until axeyum times out / returns `unknown`. The
//! **frontier** is the largest `N` axeyum *decides* (sat/unsat) **and** whose
//! self-check confirms that verdict is correct, within a fixed per-instance
//! budget. It is one integer per family that **rises** when the underlying
//! lever improves. We commit `BASELINE_<family>` = the measured current
//! frontier; the test asserts `frontier >= baseline` and prints the live value
//! plus a `PROGRESS` flag when it exceeds the floor.
//!
//! An isolated miss below the frontier does **not** discard the reach above it.
//! These families are not monotone in `N` — `lia_cuts` decides `N=26` in ~25 ms
//! immediately after `N=25` takes ~3.5 s, and decides `N=30..32` after missing
//! `N=27..29` — so the older "largest `N` with an unbroken decided prefix" rule
//! reported *the position of the first knife-edge instance*, not the reach of
//! the lever. On a clean monotone curve the two definitions agree, so the
//! committed baselines carry over unchanged.
//!
//! # This is a WALL-CLOCK measurement — run it on an idle box
//!
//! The frontier is "how far do we get in [`BUDGET`]", so it is only as stable as
//! the machine. Measured on 2026-08-04 (24-core box shared with an unrelated
//! workload, load average 15-25), interleaving two commits A/B/A/B, 5 runs per
//! side:
//!
//! - `bv_reduction` reported **26..32 on both commits**, straddling its
//!   committed floor of 30 — while the commit under test contained **no
//!   bit-vector code on any path it touches**. The unmodified base commit fell
//!   below its own baseline in **3 of 7** runs. Every instance from `N=27` up
//!   solves in 1.4-4.0 s against the 4 s budget, so which one crosses first is
//!   decided by the box, not the solver.
//! - `lia_cuts` came down entirely to `N=25` at 3.27-3.63 s (82-91 % of budget).
//!
//! Two mitigations are built in rather than left to the operator: every
//! *timing-edge* miss is retried up to [`ATTEMPTS`] times (see
//! [`is_timing_edge`]), and the 1-minute load average plus the list of
//! near-budget instances are printed with every `FRONTIER` line and embedded in
//! the failure message. What remains the operator's job is the obvious part:
//! **do not trust a `REGRESSION` from this suite taken next to a parallel
//! `cargo test` or another solver sweep.** Re-run it idle first. This gate has
//! produced a disputed `REGRESSION` twice, both times under parallel load.
//!
//! # Oracle-free / self-checking — soundness is the contract
//!
//! Every instance carries its own ground truth, established **independently** of
//! the bit-blast-to-SAT search path (the same discipline as `axeyum-scenarios`,
//! ADR-0008):
//!
//! - **SAT** instances carry a concrete witness. The witness is verified by
//!   evaluating the query terms against it (via [`axeyum_scenarios::Scenario`]'s
//!   evaluator-only `self_check`, or — for the string family — by evaluating the
//!   string-theory constraints against the concrete witness string in plain
//!   Rust). A family that builds a *bad* witness fails its own self-check before
//!   the solver is ever consulted.
//! - **UNSAT** instances are the negation of a true-by-construction identity,
//!   refuted by exhaustive enumeration over the (small) finite domain — a
//!   genuine proof of UNSAT, not an oracle's say-so.
//!
//! A *decided-but-wrong* verdict (the solver's answer contradicts the
//! self-checked ground truth) is a **hard test failure** — this is the
//! soundness guard. We never trust an unverified decided result.
//!
//! # The five families and their levers
//!
//! | family          | knob `N` scales …                                  | roadmap lever                                                  |
//! |-----------------|----------------------------------------------------|----------------------------------------------------------------|
//! | `bv_reduction`  | depth of a constant-folding multiplier tower       | `QF_BV` **word-level reduction** (`preprocess`, ADR-0037)     |
//! | `lia_cuts`      | size/coupling of an integer-linear system          | `QF_LIA` **branch-and-bound** (the bounded integer engine)    |
//! | `string_bound`  | required string length                             | **bounded-string** `STRING_MAX_LEN` (currently 8, ADR-0029)   |
//! | `nra_degree`    | even degree of a shifted sum-of-powers refutation  | `QF_NRA` **CAD / high-degree refutation** (the NRA decider)   |
//! | `nia_unsat`     | bound/modulus of an integer-nonlinear refutation   | `QF_NIA` **integer-nonlinear UNSAT** (the NIA decider gap)    |
//!
//! Each family's fall-off is *attributable to its lever*: `bv_reduction` decides
//! far past where the same instances fall off with `preprocess` **disabled**
//! (proving reduction is doing the work — see `bv_reduction_falloff_is_the_lever`);
//! `string_bound` falls off exactly at the packed-string bound; `nra_degree`
//! falls off at the CAD/high-degree-SOS refutation cliff; `nia_unsat` sits at the
//! measured integer-nonlinear blind spot (frontier `0` today — a tracking row
//! that *rises the moment the NIA decider gains UNSAT capability*). When a lever
//! deepens, the corresponding baseline can be bumped — gradual progress, made
//! visible and attributable.
//!
//! ## `nra_degree` and `nia_unsat` are ported from the measured graduated corpus
//!
//! The two nonlinear families port the by-construction UNSAT constructions of the
//! neutral graduated corpus (`scripts/gen-graduated-nra-nia.py`, commit
//! `97d903b`) into Rust generators, so the oracle-free CI dashboard tracks the
//! exact NRA/NIA decider frontiers that the neutral measurement pinned:
//!
//! - `nra_degree` ports **`sos-strict-unsat-dN`**: `(x-1)^{2d} + (y-2)^{2d} + 1
//!   < 0`, infeasible because a sum of even powers plus 1 is `>= 1 > 0`. The
//!   measured cliff is degree `~4` (degrees `6/8/10` → `unknown` today).
//! - `nia_unsat` ports **`no-square-mod-bN`**: `x^2 = m·t + r` with `r` a
//!   quadratic **non-residue** mod `m` and `0 <= x < b·m` — no integer square is
//!   `≡ r (mod m)`. The measured frontier is `0` (axeyum returns `unknown` on
//!   all): an UNSAT blind spot, captured as a tracking row.
#![cfg(feature = "full")]

use std::ffi::OsString;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value};
use axeyum_query::Query;
use axeyum_scenarios::{Expectation, Family, Scenario, UnsatEvidence};
use axeyum_solver::{CheckResult, SolverConfig, SolverError, check_auto, solve_smtlib};

/// Per-instance solve budget. Modest so the whole sweep finishes in a couple of
/// minutes under `scripts/mem-run.sh`; large enough that the frontier reflects
/// real solving power, not a too-tight clock.
const BUDGET: Duration = Duration::from_secs(4);

/// How far past the frontier we keep sweeping, to log the shape of the fall-off
/// (decided → undecided) rather than stopping the instant we hit the wall.
const OVERSHOOT: u32 = 3;

/// How many times an instance that missed **on the clock** is re-solved before
/// the sweep believes the miss.
///
/// The frontier is a wall-clock measurement, so any instance that lands within a
/// few hundred milliseconds of [`BUDGET`] is decided by whatever else the
/// machine happens to be doing. That is not a hypothesis — it is measured. In an
/// interleaved A/B of two commits, 5 runs per side (2026-08-04, 24-core box
/// shared with an unrelated workload at load average 15-25):
///
/// - `bv_reduction` instances `N=27..32` all solve in **1.4-4.0 s** against the
///   4 s budget. The reported frontier ranged **26..32 on BOTH commits**, and
///   the commit under test contained *no bit-vector code at all* — so the entire
///   spread was box noise. The unmodified base commit fell below its own
///   committed baseline in **3 of 7** runs.
/// - `lia_cuts` `N=25` solves in **3.27-3.63 s** — 82-91 % of budget — while
///   `N=26` solves in **~25 ms**. Whether `N=25` happens to cross 4 s therefore
///   decided the whole family's reported number.
///
/// Retrying costs nothing on a healthy run: only a *timing-edge* miss is
/// retried (see [`is_timing_edge`]), so an instance the solver declines quickly
/// — a real capability wall — is never re-run. A genuine loss still has to fail
/// [`ATTEMPTS`] times in a row.
const ATTEMPTS: u32 = 3;

/// Fraction of [`BUDGET`] above which an undecided instance is treated as a
/// *timing edge* (worth retrying) rather than a structural wall.
///
/// An instance that returns `unknown` after burning most of its clock might have
/// made it on a quieter box; one that declines in 20 ms is at a real capability
/// wall and re-running it only wastes time.
const TIMING_EDGE_FRACTION: f64 = 0.5;

/// Optional destination for volatile hardware-relative timing curves.
///
/// The SMT-COMP readiness gate sets this to a unique temporary directory so
/// an otherwise successful `just check` cannot dirty the exact-main worktree.
/// Ordinary developer and measurement runs retain the historical committed
/// artifact location when the variable is absent.
const FRONTIER_ARTIFACT_DIR_ENV: &str = "AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR";

// ---------------------------------------------------------------------------
// Committed baselines — the measured current frontier per family.
//
// These were measured by running this very suite (`-- --nocapture`) and reading
// the `FRONTIER` lines. The test asserts `frontier >= baseline`, so improving a
// lever shows up as a `PROGRESS` line and lets the baseline be bumped; a
// regression drops the frontier below the floor and fails the gate.
// ---------------------------------------------------------------------------

/// `bv_reduction`: largest `N` whose `N²`-multiplier tower reduction collapses
/// and decides UNSAT within budget. Measured frontier ≈ 33; the committed floor
/// is set below it with margin for timing noise near the knee. Rises when
/// word-level reduction deepens (collapses more multipliers per unit budget).
const BASELINE_BV_REDUCTION: u32 = 30;

/// `lia_cuts`: largest integer-linear system size decided (SAT, witness-checked)
/// under the bounded integer engine. Measured frontier ≈ 26; floor set below it
/// with margin (branch-and-bound runtime near the knee is noisy). Rises as the
/// LIA engine deepens.
const BASELINE_LIA_CUTS: u32 = 26;

/// `string_bound`: largest required string length decided before the
/// packed-string bound (`STRING_MAX_LEN`, currently 8) cuts it off. The fall-off
/// is deterministic (a hard packing bound, not a timing edge), so the floor sits
/// exactly at the measured frontier. Rises when the bound is raised.
const BASELINE_STRING_BOUND: u32 = 8;

/// `nra_degree`: largest even-degree exponent `2N` whose shifted sum-of-powers
/// refutation `(x-1)^{2N} + (y-2)^{2N} + 1 < 0` axeyum refutes (UNSAT) within
/// budget. The knob `N` is the *half-degree*, so instance `N` has degree `2N`.
/// The linear-abstraction/McCormick relaxation reached only `N=2` (degree 4)
/// before the branch-and-bound search timed out at `N=3` (degree 6). Now **40** =
/// [`MAX_N`], the full sweep: the syntactic even-power refutation
/// (`nra_even_power`, wired as a cheap pre-check at the top of `check_with_nra`)
/// recognizes the shape `Σ tᵢ^{2kᵢ} + c < 0` directly — every even power is `≥ 0`
/// so the sum is `≥ c ≥ 0`, never `< 0` — and decides it in O(term size) at ANY
/// degree (each instance clears in ≈ 15 ms vs a 4 s budget, so the cap is the
/// sweep ceiling, not the decider). The certificate is re-scanned in the evidence
/// route, so the verdict is a from-first-principles nonnegativity fact. The floor
/// is ratcheted to the measured frontier; `frontier >= BASELINE` holds.
const BASELINE_NRA_DEGREE: u32 = 40;

/// `nia_unsat`: largest bound multiplier `N` whose integer-nonlinear
/// `no-square-mod` refutation axeyum refutes (UNSAT) within budget. The measured
/// frontier was **0** (the NIA decider had no integer-nonlinear UNSAT capability)
/// and is now **40** = [`MAX_N`], the full sweep: the bound-aware EXACT int-blast
/// (`decide_bounded_int_blast` in `auto.rs`) proves the finite box — `x` directly
/// bounded by `0 ≤ x < N·m`, `t`'s upper bound *derived* from `x`'s via the
/// equality `x² = m·t + r` — then blasts at a width that encodes the box exactly,
/// so a bit-vector `Unsat` is a TRUSTED integer `Unsat`. The floor is ratcheted to
/// the measured frontier; `frontier >= BASELINE` holds, so the test PASSES.
const BASELINE_NIA_UNSAT: u32 = 40;

/// The largest `N` any family is ever swept to (a hard ceiling so a regression
/// that suddenly decides "everything" can't run forever).
const MAX_N: u32 = 40;

// ---------------------------------------------------------------------------
// Committed TIMING baselines — see the "TIMING ratchet" section below for the
// design and [`TimingBaseline`] for the field meanings. Measured over
// [`TIMING_BASELINE_RUNS`] runs of this binary on `s4` (i5-12600K, `taskset -c
// 0-7`) on 2026-09-05 at 1-minute loads 27-44, i.e. deliberately including
// heavily contended boxes, because the residual the calibration does not remove
// is what the band has to absorb.
// ---------------------------------------------------------------------------

/// `bv_reduction`: the multiplier tower grows smoothly in `N`, so the pins sit
/// on the steep part of the curve — where a lost word-level reduction would
/// show up first — while staying under a third of the budget so they always
/// decide.
const TIMING_BV_REDUCTION: TimingBaseline = TimingBaseline {
    pins: &[12, 15, 18],
    min_ms: 959.9,
    median_ms: 1216.0,
    max_ms: 1509.5,
    ceiling_ms: 2264.3,
};

/// `lia_cuts`: branch-and-bound is not monotone in `N` here, so the pins are the
/// two stable small points plus `N=20`, the first that costs real search.
const TIMING_LIA_CUTS: TimingBaseline = TimingBaseline {
    pins: &[3, 19, 20],
    min_ms: 238.6,
    median_ms: 323.1,
    max_ms: 393.1,
    ceiling_ms: 589.6,
};

/// `string_bound`: the packed-string route is flat within each length band, so
/// the pins straddle three bands.
const TIMING_STRING_BOUND: TimingBaseline = TimingBaseline {
    pins: &[13, 25, 33],
    min_ms: 387.6,
    median_ms: 426.9,
    max_ms: 646.0,
    ceiling_ms: 969.1,
};

/// `nra_degree`: the syntactic even-power refutation decides every instance in
/// single-digit milliseconds, so no pin is expensive and the total is small.
/// Four pins rather than three, because at ~1 ms per point the scheduler is a
/// large share of each sample and averaging is the only way to tighten the band.
/// The small total is not a weakness here: losing the fast path costs *seconds*,
/// two to three orders of magnitude above this ceiling.
const TIMING_NRA_DEGREE: TimingBaseline = TimingBaseline {
    pins: &[10, 20, 30, 40],
    min_ms: 6.5,
    median_ms: 10.5,
    max_ms: 12.0,
    ceiling_ms: 18.0,
};

/// `nia_unsat`: the bound-aware exact int-blast is cheap only at the small end —
/// the blast width grows with the bound and every instance from `N=6` up costs
/// ~2.7 s of a 4 s budget, far too close to the clock to pin. So the pins are
/// `N=1..5`, five points averaged for the same reason as `nra_degree`. This is
/// the family where the ratchet has the least resolution, and that is a property
/// of the curve, not of the design.
const TIMING_NIA_UNSAT: TimingBaseline = TimingBaseline {
    pins: &[1, 2, 3, 4, 5],
    min_ms: 30.4,
    median_ms: 44.3,
    max_ms: 62.3,
    ceiling_ms: 93.5,
};

// ---------------------------------------------------------------------------
// One point on a family's difficulty curve.
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct CurvePoint {
    n: u32,
    /// `true` iff the solver returned sat/unsat *and* the self-check confirmed
    /// that verdict is the correct one.
    decided_correct: bool,
    /// `"sat"`, `"unsat"`, `"unknown"`, `"timeout"`, or `"error"`.
    status: &'static str,
    solve_ms: f64,
}

/// A built, already-self-checked instance ready to hand to the solver, plus the
/// independent verdict its self-check established.
struct Instance {
    arena: TermArena,
    assertions: Vec<TermId>,
    /// `true` if the ground truth is SAT, `false` if UNSAT.
    expect_sat: bool,
}

/// Outcome of solving one instance under [`BUDGET`].
struct Solved {
    decided_correct: bool,
    status: &'static str,
    solve_ms: f64,
}

/// Whether an undecided outcome looks like it ran out of *clock* rather than
/// hitting a capability wall — the only kind of miss worth retrying.
///
/// See [`ATTEMPTS`] for the measurements that motivate this.
fn is_timing_edge(solved: &Solved, budget_ms: f64) -> bool {
    !solved.decided_correct
        && matches!(solved.status, "unknown" | "timeout")
        && solved.solve_ms >= budget_ms * TIMING_EDGE_FRACTION
}

/// The 1-minute load average, when the platform exposes it.
///
/// Recorded so that a `REGRESSION` line carries the one piece of context needed
/// to tell a lost lever from a busy box. Absent on non-Linux; the ratchet still
/// runs, it just cannot annotate itself.
fn load_average() -> Option<f64> {
    let text = std::fs::read_to_string("/proc/loadavg").ok()?;
    text.split_whitespace().next()?.parse().ok()
}

/// `load_average()` rendered for humans.
fn load_note() -> String {
    match load_average() {
        Some(load) => format!("{load:.2}"),
        None => "unavailable".to_owned(),
    }
}

// ===========================================================================
// The reference frame: which machine, how busy, and the budget that follows.
// ===========================================================================
//
// THE PROBLEM, measured on ONE gate on ONE machine on 2026-08-13/14:
//
//     frontier_bv_reduction = 35   written 23:33 during a 7-agent campaign
//                                  (load 34 on 24 cores)
//                           = 38   the committed artifact
//                           = 39   this lane, load 5.4
//                           = 40   re-run at load 1.17 (= MAX_N, the ceiling)
//
// A 14 % spread from machine load alone, on the same commit. Both directions
// are wrong to commit: the 35 ratchets the roadmap floor down on a contaminated
// reading, and the 40 sets a floor no smaller box can meet. An earlier instance
// is already in the register — `frontier_bv_reduction` failing on a 4-core box
// at 26 against a baseline of 30, with the lost instances returning `unknown` at
// ~4009 ms against a 4000 ms budget, i.e. at the measurement's own resolution
// limit.
//
// WHY NOT "declare a reference machine and refuse to compare elsewhere". It was
// the other option, and it is not enough, because "the machine" is not one
// speed. This box is a 12900K: 8 performance cores + 8 efficiency cores. The
// same binary on the same machine runs at two different speeds depending on
// which core the scheduler picks: this very sweep is **1.84x slower** pinned to
// the efficiency cores, and the stock fixed-budget gate reported
// `FRONTIER bv_reduction = 29` against a baseline of 30 there — a REGRESSION
// that never happened, reproduced three times out of three. A hostname match
// would have certified that comparison as valid, and it would turn every other
// machine's run into no signal at all rather than a weaker one. Measurements in
// `docs/research/08-planning/frontier-ratchet-reference-frame.md`.
//
// WHAT WE DO INSTEAD. Measure the machine's *current* throughput with a frozen
// synthetic kernel immediately before each family's sweep, scale the per-instance
// budget by (measured / reference), and record the machine, the load, the
// calibration and the scale in the JSON artifact next to the frontier. A busy
// box gets a proportionally larger budget, so the frontier it reports stays
// comparable with the reference machine's — which is the only thing that makes
// the committed baselines mean anything.
//
// AND WE SAY WHEN WE CANNOT. Outside [1/`SCALE_LIMIT`, `SCALE_LIMIT`], or when
// the calibration drifts by more than [`DRIFT_LIMIT`] between the start and the
// end of the sweep, the run is declared NOT COMPARABLE: the number is still
// printed and written, but the ratchet does not fail the build on it. Above
// [`RATCHETABLE_SCALE_MAX`] a frontier ABOVE the baseline is advisory only —
// it must not be used to raise a baseline. Those two rules are the 35 and the
// 40 respectively, and each would have been refused.

/// Words in the calibration buffer: 32768 x 8 B = 256 KiB, which is L2-resident
/// on this class of machine. The size is not cosmetic — it is what makes the
/// kernel a usable proxy, and it was chosen by MEASUREMENT, not by taste.
///
/// The first version walked 4 MiB, i.e. main memory, and was therefore
/// latency-bound on a resource the two core types share. On this 12900K it
/// reported efficiency cores as only 1.2x slower than performance cores, while
/// the `bv_reduction` sweep itself is **1.84x** slower there (median over the
/// instances above 200 ms, same commit, same load). A calibration that
/// under-reports the slowdown under-compensates the budget, which is exactly the
/// failure it exists to prevent: the E-core run recovered only 29 -> 30.
///
/// Candidates measured under the test profile's flags (`opt-level=0`,
/// `debug-assertions`, `overflow-checks`), `taskset` on each core class:
///
/// | kernel                  | P-core | E-core | ratio | vs solver's 1.84 |
/// |-------------------------|--------|--------|-------|------------------|
/// | 4 MiB stride walk       | 142.5  | 203.4  | 1.43  | far under, and noisy (P ranged 114.9-143.7) |
/// | 32 KiB dependent chain  |  64.7  | 109.0  | 1.68  | under |
/// | 256 KiB dependent chain |  70.4  | 137.8  | 1.96  | closest, stable to ~2 % |
///
/// If this kernel is ever changed, re-run that comparison: a proxy whose ratio
/// does not track the workload's is a budget that compensates for the wrong
/// thing.
const CALIBRATION_WORDS: usize = 1 << 15;

/// Odd stride mixed into the data-dependent index, so consecutive accesses are
/// unpredictable to the prefetcher.
const CALIBRATION_STRIDE: usize = 4099;

/// Iterations of the dependent chain, chosen so one call takes ~120 ms in the
/// unoptimized test profile on an uncontended performance core: long enough to
/// average over scheduling noise, short enough that two calls per family are
/// free next to a 4 s per-instance budget.
const CALIBRATION_ITERATIONS: usize = 10_000_000;

/// The kernel's output. FROZEN: the reference below describes a specific amount
/// of work, so if the kernel changes the reference is meaningless. Changing the
/// kernel must therefore break this assertion, and re-measuring
/// [`CALIBRATION_REFERENCE_MS`] is part of that change.
const CALIBRATION_CHECKSUM: u64 = 0xa10b_afd9_e492_376a;

/// Repeats per calibration; the MEDIAN is used, so one descheduled sample cannot
/// move the budget. Nine rather than five because the spread of a single sample
/// on a busy box is large: pinned to this machine's P-cores at 1-minute load
/// 12.4, three consecutive medians-of-five were 219 / 114 / 352 ms. Nine samples
/// (~1.2 s) buy a median that survives one lane's build starting mid-window.
const CALIBRATION_REPEATS: usize = 9;

/// Median [`calibration_kernel`] time on the reference machine: five
/// medians-of-nine with `taskset -c 0-7` (performance cores) on 2026-08-14 at
/// 1-minute load 4.0 gave 127.1, 127.3, 127.3, 127.5, 128.1 ms — a 0.8 % spread,
/// so the minimum and the mean agree to within noise. The same binary on the
/// efficiency cores gave 221.5-246.7 ms (scale 1.74x), which is the number the
/// budget has to compensate for.
///
/// The minimum rather than the mean because the error is asymmetric: a reference
/// that is too slow shrinks every budget and manufactures REGRESSIONs. The box
/// was shared while this was taken, so the true idle value may be slightly
/// lower; `calibration_frames_the_measurement` prints the live median on every
/// run, so if a quieter machine ever measures below this, LOWER it here.
const CALIBRATION_REFERENCE_MS: f64 = 127.0;

/// The machine the reference above was taken on. Recorded, not enforced — see
/// the section header for why a hostname match would be a false certificate.
const CALIBRATION_REFERENCE_MACHINE: &str =
    "12th Gen Intel Core i9-12900K, performance cores (taskset -c 0-7), Linux, test profile";

/// Beyond this factor in either direction, this run and the reference are not
/// measuring the same thing and the ratchet stops being an assertion.
const SCALE_LIMIT: f64 = 3.0;

/// The band a run's budget must sit in for its frontier to be used to RAISE a
/// baseline. Outside it the number is reported but not ratchetable: above the
/// maximum a slow or busy box has been handed a bigger budget (that is the 35 in
/// the header, run under load 34), and below the minimum a fast or idle box is
/// doing more work per second than the machine the baselines were set on (that
/// is the 40). Both would commit a floor that the reference machine cannot meet.
const RATCHETABLE_SCALE_MAX: f64 = 1.25;
const RATCHETABLE_SCALE_MIN: f64 = 0.9;

/// Relative change in calibration between the start and the end of one family's
/// sweep above which the environment moved under the measurement.
const DRIFT_LIMIT: f64 = 0.25;

/// A fixed amount of ALU + memory work whose wall time measures what the machine
/// can currently do.
///
/// It must NOT use the solver. An earlier draft calibrated with a small
/// `check_auto` instance, which is self-defeating: improving the very lever the
/// frontier measures would speed the calibration up, shrink the budget, and
/// cancel out the improvement. This kernel is deliberately unrelated to anything
/// this repository optimizes, and frozen by [`CALIBRATION_CHECKSUM`].
fn calibration_kernel() -> u64 {
    let mut buffer: Vec<u64> = (0..CALIBRATION_WORDS as u64)
        .map(|i| i.wrapping_mul(0x9E37_79B9_7F4A_7C15))
        .collect();
    let mask = CALIBRATION_WORDS - 1;
    let mut acc: u64 = 0x0123_4567_89AB_CDEF;
    let mut index = 0usize;
    for _ in 0..CALIBRATION_ITERATIONS {
        acc = acc.rotate_left(7) ^ buffer[index];
        // A data-dependent, statistically unpredictable branch: branch
        // misprediction is a large part of why this workload separates the two
        // core types, and it is what a SAT search does all day.
        if acc & 1 == 0 {
            acc = acc.wrapping_mul(0x2545_F491_4F6C_DD1D);
        } else {
            acc = (acc ^ (acc >> 13)).wrapping_add(0x9E37_79B9_7F4A_7C15);
        }
        buffer[index] = acc;
        // The next index depends on the value just computed, so the loop is a
        // serial dependency chain rather than something the machine can run
        // wide — again, closer to propagation than to a streaming benchmark.
        // `as usize` would be a truncating cast on a 32-bit target; the value is
        // only ever used modulo `mask`, so take the low half explicitly.
        let mixed = (acc & 0xFFFF_FFFF) as u32 as usize;
        index = (mixed ^ (index.wrapping_add(CALIBRATION_STRIDE))) & mask;
    }
    std::hint::black_box(acc)
}

/// Median of [`CALIBRATION_REPEATS`] kernel runs, in milliseconds.
fn calibration_ms() -> f64 {
    let mut samples = Vec::with_capacity(CALIBRATION_REPEATS);
    for _ in 0..CALIBRATION_REPEATS {
        let start = Instant::now();
        let checksum = calibration_kernel();
        samples.push(start.elapsed().as_secs_f64() * 1000.0);
        assert_eq!(
            checksum, CALIBRATION_CHECKSUM,
            "the calibration kernel changed, so CALIBRATION_REFERENCE_MS no longer \
             describes the work it timed. Re-measure the reference (idle box, \
             performance cores) and update both constants together."
        );
    }
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

/// Which machine this is, recorded with every measurement.
struct Machine {
    host: String,
    cpus: usize,
    model: String,
}

fn machine() -> Machine {
    let host = std::fs::read_to_string("/proc/sys/kernel/hostname")
        .map(|text| text.trim().to_owned())
        .ok()
        .or_else(|| std::env::var("HOSTNAME").ok())
        .unwrap_or_else(|| "unknown".to_owned());
    let cpus = std::thread::available_parallelism().map_or(0, std::num::NonZero::get);
    let model = std::fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|text| {
            text.lines()
                .find(|line| line.starts_with("model name"))
                .and_then(|line| line.split(':').nth(1))
                .map(|value| value.trim().to_owned())
        })
        .unwrap_or_else(|| "unknown".to_owned());
    Machine { host, cpus, model }
}

/// One family's measurement environment: the machine, the calibration taken
/// immediately before the sweep, the budget that follows from it, and (after
/// [`Measurement::finish`]) how far the environment moved during the sweep.
struct Measurement {
    machine: Machine,
    calibration_start_ms: f64,
    calibration_end_ms: Option<f64>,
    raw_scale: f64,
    scale: f64,
    load_start: Option<f64>,
    load_end: Option<f64>,
}

impl Measurement {
    /// Calibrate. Call this immediately before the sweep it will budget.
    fn start() -> Self {
        let calibration_start_ms = calibration_ms();
        let raw_scale = calibration_start_ms / CALIBRATION_REFERENCE_MS;
        Measurement {
            machine: machine(),
            calibration_start_ms,
            calibration_end_ms: None,
            raw_scale,
            scale: raw_scale.clamp(1.0 / SCALE_LIMIT, SCALE_LIMIT),
            load_start: load_average(),
            load_end: None,
        }
    }

    /// The per-instance budget on THIS machine at THIS load: the nominal
    /// [`BUDGET`] scaled so a busy or slower box gets proportionally more clock
    /// for the same instance.
    fn budget(&self) -> Duration {
        Duration::from_secs_f64(BUDGET.as_secs_f64() * self.scale)
    }

    fn budget_ms(&self) -> f64 {
        self.budget().as_secs_f64() * 1000.0
    }

    /// Re-calibrate after the sweep, so a box that got busy *during* the
    /// measurement is visible rather than silently folded into the number.
    fn finish(&mut self) {
        self.calibration_end_ms = Some(calibration_ms());
        self.load_end = load_average();
    }

    /// Relative change in machine throughput across the sweep.
    fn drift(&self) -> Option<f64> {
        self.calibration_end_ms
            .map(|end| ((end - self.calibration_start_ms) / self.calibration_start_ms).abs())
    }

    /// Whether this run can be compared with the committed baselines at all.
    fn comparable(&self) -> bool {
        let in_range = self.raw_scale >= 1.0 / SCALE_LIMIT && self.raw_scale <= SCALE_LIMIT;
        let steady = self.drift().is_none_or(|drift| drift <= DRIFT_LIMIT);
        in_range && steady
    }

    /// Whether a frontier ABOVE the baseline measured here may be used to raise
    /// that baseline. A bigger-than-reference budget can manufacture progress,
    /// so it may not.
    fn ratchetable(&self) -> bool {
        self.comparable()
            && self.scale <= RATCHETABLE_SCALE_MAX
            && self.scale >= RATCHETABLE_SCALE_MIN
    }

    fn why_not_comparable(&self) -> String {
        let mut reasons = Vec::new();
        if self.raw_scale > SCALE_LIMIT {
            reasons.push(format!(
                "this machine/load is {:.2}x slower than the reference (limit {SCALE_LIMIT:.1}x)",
                self.raw_scale
            ));
        }
        if self.raw_scale < 1.0 / SCALE_LIMIT {
            reasons.push(format!(
                "this machine is {:.2}x faster than the reference (limit {SCALE_LIMIT:.1}x)",
                1.0 / self.raw_scale
            ));
        }
        if let Some(drift) = self.drift()
            && drift > DRIFT_LIMIT
        {
            reasons.push(format!(
                "throughput moved {:.0} % during the sweep ({:.1} ms -> {:.1} ms)",
                drift * 100.0,
                self.calibration_start_ms,
                self.calibration_end_ms.unwrap_or(f64::NAN),
            ));
        }
        reasons.join("; ")
    }

    /// The one line that has to appear next to every frontier number.
    fn describe(&self) -> String {
        format!(
            "machine {} ({} cpus, {}), load {} -> {}, calibration {:.1} ms vs reference \
             {CALIBRATION_REFERENCE_MS:.1} ms => scale {:.2}x, budget {:.0} ms",
            self.machine.host,
            self.machine.cpus,
            self.machine.model,
            self.load_start
                .map_or_else(|| "unavailable".to_owned(), |l| format!("{l:.2}")),
            self.load_end
                .map_or_else(|| "-".to_owned(), |l| format!("{l:.2}")),
            self.calibration_start_ms,
            self.scale,
            self.budget_ms(),
        )
    }
}

/// The soundness guard: a *decided-but-wrong* verdict is never tolerated, on any
/// attempt. Deliberately not recoverable.
///
/// Applied to **every** attempt, including retries — a retry may only upgrade a
/// timing miss into a decision, never launder a wrong answer.
fn check_verdict(family: &str, n: u32, solved: &Solved, expect_sat: bool) {
    let wrong_verdict = matches!(solved.status, "sat" | "unsat") && !solved.decided_correct;
    assert!(
        !wrong_verdict,
        "SOUNDNESS FAILURE [{family} N={n}]: solver said {} but the self-checked \
         ground truth is {}",
        solved.status,
        if expect_sat { "sat" } else { "unsat" },
    );
}

/// Run `check_auto` on a worker thread under [`BUDGET`]; degrade to a sound
/// timeout on overrun.
///
/// A generous stack mirrors `corpus_regression.rs` — deep bit-blasting can
/// recurse — and the wall-clock cap means a hard instance degrades to a sound
/// timeout (`unknown`), never a hang/OOM.
fn solve_capped(mut instance: Instance, config: SolverConfig, budget: Duration) -> Solved {
    let expect_sat = instance.expect_sat;
    let (tx, rx) = mpsc::channel();
    let t0 = Instant::now();
    thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let res = check_auto(&mut instance.arena, &instance.assertions, &config);
            let _ = tx.send(res);
        })
        .expect("spawn solver thread");

    // Give the thread the budget plus a small margin to deliver its own
    // timeout-driven `unknown` before we declare a hard overrun.
    let outcome = rx.recv_timeout(budget + Duration::from_secs(1));
    let solve_ms = t0.elapsed().as_secs_f64() * 1000.0;

    classify(&outcome, expect_sat, solve_ms)
}

fn classify(
    outcome: &Result<Result<CheckResult, SolverError>, mpsc::RecvTimeoutError>,
    expect_sat: bool,
    solve_ms: f64,
) -> Solved {
    match outcome {
        Ok(Ok(CheckResult::Sat(_))) => Solved {
            // Decided sat: correct iff ground truth is sat. A sat against a
            // self-checked UNSAT ground truth is a soundness failure (caught in
            // `sweep`).
            decided_correct: expect_sat,
            status: "sat",
            solve_ms,
        },
        Ok(Ok(CheckResult::Unsat)) => Solved {
            decided_correct: !expect_sat,
            status: "unsat",
            solve_ms,
        },
        Ok(Ok(CheckResult::Unknown(_))) => Solved {
            decided_correct: false,
            status: "unknown",
            solve_ms,
        },
        Ok(Err(_)) => Solved {
            decided_correct: false,
            status: "error",
            solve_ms,
        },
        Err(_) => Solved {
            decided_correct: false,
            status: "timeout",
            solve_ms,
        },
    }
}

// ===========================================================================
// The TIMING ratchet: the frontier's counterpart on the clock.
// ===========================================================================
//
// THE HOLE THIS CLOSES. Measured 2026-09-05 (`docs/research/11-design-review/
// 2026-09-05-sat-smt-performance-and-architecture-review.md` section 2.2 item
// 1): **nothing in any gate fails when solve time regresses.** This suite
// ratchets *capability at a fixed budget*; the parity ledger ratchets *decide
// count*; the corpus sweep ratchets *soundness*. The 72 baselines under
// `bench-results/baselines/` carry a `summary.par2_mean_s` that is compared to
// nothing. So a change that keeps every verdict and every frontier but makes
// the solver twice as slow is invisible to every gate in this repository —
// right up until an instance crosses the budget and the CAPABILITY ratchet
// reports it as a lost lever, which is the wrong diagnosis at the wrong time.
//
// WHY IT LIVES HERE RATHER THAN IN A NEW SWEEP. Everything a timing ratchet
// needs that is hard, this suite already has: a frozen calibration kernel
// validated against the solver's own core-class sensitivity, a per-family
// `scale`, and a `comparable` / `ratchetable` verdict that says when a number
// may be believed. A second sweep would pay the whole ~6 min again and would
// have to re-derive all of it. The pinned points are read out of the curve the
// sweep has already produced, so the timing ratchet costs **zero extra
// solving** and is registered wherever `progress_frontier` already is
// (`scripts/check.sh`'s `frontier` step and the `justfile`'s `frontier`
// recipe).
//
// THE BAND IS MEASURED, NOT GUESSED. Each family pins a small set of `N` deep
// inside its frontier — chosen so they decide on every run with time to spare,
// and so their total is dominated by real solving rather than by fixed
// overhead. The pinned total is *calibrated* (`solve_ms / scale`), i.e.
// expressed in reference-machine milliseconds, and compared with a committed
// ceiling. Baseline and ceiling both come from [`TIMING_BASELINE_RUNS`] runs of
// this very binary on this box, deliberately spanning quiet and heavily loaded
// conditions, because the residual the calibration does NOT remove is exactly
// what the band has to absorb. The numbers are in
// `docs/research/08-planning/benchmarking-and-performance-methodology.md`.
//
// AND IT SAYS WHEN IT CANNOT COMPARE, on the same flag as the capability
// ratchet: outside the comparable band (`scale` beyond [1/3, 3], or throughput
// drifting more than [`DRIFT_LIMIT`] mid-sweep) the total is printed and
// written to the JSON with `"enforced": false`, and nothing fails. That is the
// same rule that stopped `bv_reduction` reporting a REGRESSION that never
// happened when the sweep landed on the efficiency cores (29 against a baseline
// of 30, four runs in five), and the same rule behind the 35 / 39 / 40 spread
// at 1-minute loads 34 / 5.4 / 1.17 recorded in
// `docs/research/08-planning/frontier-ratchet-reference-frame.md`.

/// How many runs of this binary the committed timing baselines were measured
/// over. Recorded in the artifact so a reader can weigh the band.
const TIMING_BASELINE_RUNS: u32 = 5;

/// The ceiling is this factor times the **slowest** of those runs' calibrated
/// totals.
///
/// Not a taste judgement. The calibration is a proxy (a dependent-chain kernel
/// that tracks the solver's core-class sensitivity to within 6 %), so it does
/// not remove the machine's influence exactly: across the baseline runs the
/// *calibrated* total still moved between the quietest and the busiest box, and
/// the ceiling sits above the worst of them. What that buys is a gate that
/// fires on a genuine 2x slowdown and stays silent on a busy box; what it costs
/// is blindness to a regression smaller than the band on the pinned points,
/// which is stated here rather than left for a reader to discover.
const TIMING_BAND_FACTOR: f64 = 1.5;

/// One family's committed timing baseline: which `N` are pinned, what the
/// calibrated total measured over [`TIMING_BASELINE_RUNS`] runs, and the
/// ceiling that follows from the worst of them.
struct TimingBaseline {
    /// `N` values pinned **deep inside** the frontier, so they decide on every
    /// run and a slowdown shows up as *time*, not as a lost instance.
    pins: &'static [u32],
    /// Minimum / median / maximum calibrated total over the baseline runs.
    min_ms: f64,
    median_ms: f64,
    max_ms: f64,
    /// The enforced ceiling: [`TIMING_BAND_FACTOR`] x `max_ms`.
    ceiling_ms: f64,
}

/// One pinned point as this run measured it.
struct TimingPoint {
    n: u32,
    /// `None` when the sweep never reached this `N` (it stopped early).
    solve_ms: Option<f64>,
    decided: bool,
    calibrated_ms: Option<f64>,
}

/// This run's timing measurement against a committed [`TimingBaseline`].
struct TimingMeasured {
    points: Vec<TimingPoint>,
    /// Sum of the calibrated pinned times; `None` if any pin is missing or
    /// undecided, which is itself a failure when the run is enforceable.
    calibrated_total_ms: Option<f64>,
    /// Empty when the pinned points are healthy; otherwise why they are not.
    faults: Vec<String>,
}

/// Read the pinned points out of the curve the sweep already produced and
/// express them in reference-machine milliseconds.
///
/// Calibrated, not raw: `solve_ms / scale`. The same `scale` that stretches the
/// per-instance budget shrinks the reported time, so a busy box and the
/// reference machine land on one axis. That is the whole reason this ratchet
/// can live in a gate rather than in a nightly report.
fn measure_timing(
    baseline: &TimingBaseline,
    curve: &[CurvePoint],
    measurement: &Measurement,
) -> TimingMeasured {
    let mut points = Vec::with_capacity(baseline.pins.len());
    let mut faults = Vec::new();
    let mut total = 0.0f64;
    let mut complete = true;
    for &n in baseline.pins {
        if let Some(point) = curve.iter().find(|p| p.n == n) {
            let calibrated = point.solve_ms / measurement.scale;
            if point.decided_correct {
                total += calibrated;
            } else {
                complete = false;
                faults.push(format!(
                    "pinned N={n} did not decide ({} at {:.1} ms) — a pin sits deep inside \
                     the frontier and must always decide",
                    point.status, point.solve_ms
                ));
            }
            points.push(TimingPoint {
                n,
                solve_ms: Some(point.solve_ms),
                decided: point.decided_correct,
                calibrated_ms: Some(calibrated),
            });
        } else {
            complete = false;
            faults.push(format!(
                "pinned N={n} was never reached (the sweep stopped at N={})",
                curve.last().map_or(0, |p| p.n)
            ));
            points.push(TimingPoint {
                n,
                solve_ms: None,
                decided: false,
                calibrated_ms: None,
            });
        }
    }
    TimingMeasured {
        points,
        calibrated_total_ms: if complete { Some(total) } else { None },
        faults,
    }
}

/// Per-pin breakdown, for the printed line and the failure message.
fn timing_pin_breakdown(measured: &TimingMeasured) -> String {
    measured
        .points
        .iter()
        .map(|p| match (p.solve_ms, p.calibrated_ms, p.decided) {
            (Some(raw), Some(cal), true) => format!("N={} {cal:.1} ms (raw {raw:.1})", p.n),
            (Some(raw), _, false) => format!("N={} UNDECIDED (raw {raw:.1})", p.n),
            _ => format!("N={} NOT REACHED", p.n),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// The message a timing regression fails with, or `None` when the pinned points
/// are inside the band.
fn timing_regression(
    family: &str,
    baseline: &TimingBaseline,
    measured: &TimingMeasured,
    measurement: &Measurement,
) -> Option<String> {
    if !measured.faults.is_empty() {
        return Some(format!(
            "TIMING REGRESSION [{family}]: {}. Per pin: {}. Reference frame: {}.",
            measured.faults.join("; "),
            timing_pin_breakdown(measured),
            measurement.describe(),
        ));
    }
    let total = measured.calibrated_total_ms?;
    if total <= baseline.ceiling_ms {
        return None;
    }
    Some(format!(
        "TIMING REGRESSION [{family}]: pinned N={:?} took {total:.1} ms calibrated, over the \
         committed ceiling of {:.1} ms (= {TIMING_BAND_FACTOR:.1}x the slowest of \
         {TIMING_BASELINE_RUNS} baseline runs: min {:.1} / median {:.1} / max {:.1} ms).\n\
         Per pin: {}.\n\
         Before believing this: {}. The times above are CALIBRATED — divided by the measured \
         scale, so this box has already been compensated for — and the check is not enforced \
         at all outside the comparable band. Re-run on an otherwise idle machine; if it \
         reproduces, either the solver got slower on these paths or the baseline is stale and \
         must be re-measured over {TIMING_BASELINE_RUNS} runs and re-committed together.",
        baseline.pins,
        baseline.ceiling_ms,
        baseline.min_ms,
        baseline.median_ms,
        baseline.max_ms,
        timing_pin_breakdown(measured),
        measurement.describe(),
    ))
}

// ---------------------------------------------------------------------------
// The frontier sweep.
// ---------------------------------------------------------------------------

/// Sweep `N = 1..` building + self-checking each instance, solving under
/// `config`, and recording the curve. The **frontier** is the largest `N` that
/// is decided *and* self-check-confirmed correct with no undecided `N` below it;
/// we keep sweeping [`OVERSHOOT`] points past the first miss to log the shape of
/// the fall-off.
///
/// `build` returns `None` once a family can no longer construct an instance,
/// which ends the sweep cleanly.
///
/// A **decided-but-wrong** verdict aborts with a panic — that is the soundness
/// guard, and it is intentionally not recoverable.
fn sweep(
    family: &str,
    config: &SolverConfig,
    measurement: &Measurement,
    mut build: impl FnMut(u32) -> Option<Instance>,
) -> (u32, Vec<CurvePoint>) {
    let mut curve = Vec::new();
    let mut frontier = 0u32;
    let mut consecutive_undecided = 0u32;

    for n in 1..=MAX_N {
        let Some(instance) = build(n) else {
            break;
        };
        let expect_sat = instance.expect_sat;
        let mut solved = solve_capped(instance, config.clone(), measurement.budget());
        check_verdict(family, n, &solved, expect_sat);

        // RETRY THE CLOCK, NOT THE WALL. A miss that burned most of its budget
        // may just be the box being busy (see [`ATTEMPTS`]); a fast decline is a
        // real capability wall and is believed immediately.
        let mut attempts = 1;
        while attempts < ATTEMPTS && is_timing_edge(&solved, measurement.budget_ms()) {
            let Some(retry) = build(n) else {
                break;
            };
            let again = solve_capped(retry, config.clone(), measurement.budget());
            attempts += 1;
            check_verdict(family, n, &again, expect_sat);
            let improved = again.decided_correct || again.solve_ms < solved.solve_ms;
            if improved {
                solved = again;
            }
            if solved.decided_correct {
                break;
            }
        }
        if attempts > 1 {
            eprintln!(
                "  retry [{family} N={n}]: {attempts} attempts, final {} at {:.1} ms \
                 (load {})",
                solved.status,
                solved.solve_ms,
                load_note(),
            );
        }

        if solved.decided_correct {
            // The frontier is the largest DECIDED `N`. An isolated miss below it
            // no longer discards everything above: these families are not
            // monotone (measured: `lia_cuts` decides N=26 in ~25 ms right after
            // N=25 takes ~3.5 s, and decides N=30..32 after missing N=27..29),
            // so requiring an unbroken prefix reported the position of the first
            // knife-edge instance rather than the reach of the lever.
            frontier = n;
        } else {
            consecutive_undecided += 1;
        }

        curve.push(CurvePoint {
            n,
            decided_correct: solved.decided_correct,
            status: solved.status,
            solve_ms: solved.solve_ms,
        });

        if consecutive_undecided > OVERSHOOT {
            break;
        }
    }

    (frontier, curve)
}

/// Print the curve, the headline `FRONTIER` line and the `TIMING` line, write
/// the JSON artifact, and assert BOTH ratchets: capability (frontier >= floor)
/// and clock (calibrated pinned time <= ceiling).
///
/// Both asserts run at the end rather than early-returning, so a run that is not
/// comparable still writes its artifact and still reports both numbers — and so
/// a capability regression can never hide a timing regression by panicking
/// first.
fn report_and_assert(
    family: &str,
    baseline: u32,
    frontier: u32,
    curve: &[CurvePoint],
    measurement: &mut Measurement,
    timing: &TimingBaseline,
) {
    // Second calibration: a box that got busy DURING the sweep is a fact about
    // the number, not a footnote.
    measurement.finish();
    eprintln!("--- frontier curve: {family} ---");
    eprintln!(
        "{:>4}  {:>9}  {:>9}  {:>10}",
        "N", "decided", "status", "solve_ms"
    );
    for p in curve {
        eprintln!(
            "{:>4}  {:>9}  {:>9}  {:>10.1}",
            p.n,
            if p.decided_correct { "yes" } else { "no" },
            p.status,
            p.solve_ms,
        );
    }
    // The frontier ratchet is HARDWARE-RELATIVE: the committed baselines were
    // ratcheted on the dev box, and the frontier reached within the fixed time
    // budget collapses on slow shared CI runners (observed 3 vs 20 on a
    // 2-core GitHub runner) — a hardware artifact, not a lost lever. The
    // ratchet stays enforced where it is meaningful (local runs); on CI the
    // curve is still printed and the JSON still written for inspection.
    let ci = std::env::var("CI").is_ok();
    let progress = if frontier > baseline {
        let over = frontier - baseline;
        if measurement.ratchetable() {
            format!(", PROGRESS (+{over} over baseline, ratchetable)")
        } else {
            // The budget was scaled up for this machine/load, so a number above
            // the baseline may be the budget, not the lever. This is the 40 from
            // the header: a quiet-box reading that must not become the floor.
            format!(
                ", PROGRESS (+{over} over baseline) — ADVISORY ONLY, do not raise the \
                 baseline from this run: budget was scaled {:.2}x",
                measurement.scale
            )
        }
    } else {
        String::new()
    };
    eprintln!("FRONTIER {family} = {frontier} (baseline {baseline}){progress}");
    eprintln!("  reference frame [{family}]: {}", measurement.describe());
    if !measurement.comparable() {
        eprintln!(
            "  NOT COMPARABLE [{family}]: {} — the number above is recorded but the \
             ratchet below is not enforced on it. Re-run on an idle box.",
            measurement.why_not_comparable()
        );
    }

    // ---- the timing ratchet, read out of the curve above (no extra solving) --
    //
    // Gated on the SAME two conditions as the capability ratchet below: a CI
    // runner and an uncomparable box both get the number without the assert.
    let measured = measure_timing(timing, curve, measurement);
    let timing_enforced = !ci && measurement.comparable();
    let timing_fault = timing_regression(family, timing, &measured, measurement);
    match measured.calibrated_total_ms {
        Some(total) => eprintln!(
            "TIMING {family} = {total:.1} ms calibrated over pinned N={:?} \
             (baseline median {:.1} ms, ceiling {:.1} ms, {} runs){}",
            timing.pins,
            timing.median_ms,
            timing.ceiling_ms,
            TIMING_BASELINE_RUNS,
            if timing_enforced {
                ""
            } else {
                " — ADVISORY, not enforced on this run"
            },
        ),
        None => eprintln!(
            "TIMING {family} = incomplete over pinned N={:?}: {}",
            timing.pins,
            measured.faults.join("; ")
        ),
    }
    eprintln!("  pinned [{family}]: {}", timing_pin_breakdown(&measured));
    if let Some(message) = &timing_fault
        && !timing_enforced
    {
        eprintln!(
            "  TIMING NOT ENFORCED [{family}]: {} — recorded in the JSON artifact only.",
            message.lines().next().unwrap_or(message)
        );
    }

    write_curve_json(
        family,
        baseline,
        frontier,
        curve,
        measurement,
        timing,
        &measured,
        timing_enforced,
        timing_fault.is_none(),
    );

    // Knife-edge instances: decided, but within 20 % of the budget. These are the
    // points that flip on box load, and they are exactly what a reader needs to
    // see before believing (or disbelieving) a REGRESSION below.
    let edge_ms = measurement.budget_ms() * 0.8;
    let edges: Vec<String> = curve
        .iter()
        .filter(|p| p.decided_correct && p.solve_ms >= edge_ms)
        .map(|p| format!("N={} at {:.0} ms", p.n, p.solve_ms))
        .collect();
    if !edges.is_empty() {
        eprintln!(
            "  near-budget [{family}] (>= {:.0} ms of a {:.0} ms budget): {}",
            edge_ms,
            measurement.budget_ms(),
            edges.join(", ")
        );
    }

    // The capability ratchet's two escape hatches. They used to `return`, which
    // would now skip the timing assert as well — so they set a flag instead and
    // both ratchets are decided together at the end of this function.
    let mut capability_enforced = true;
    if ci && frontier < baseline {
        eprintln!(
            "CI: skipping the frontier ratchet for [{family}] ({frontier} < {baseline}) — \
             hardware-relative baseline, enforced on the dev box"
        );
        capability_enforced = false;
    }
    // Refusing to compare is the whole point of the calibration: a REGRESSION
    // measured outside the comparable band is a statement about the box.
    if frontier < baseline && !measurement.comparable() {
        eprintln!(
            "NOT ENFORCED [{family}]: frontier {frontier} < baseline {baseline}, but this \
             run is not comparable with the reference machine ({}). The measurement is \
             recorded in the JSON artifact; re-run it on an idle box before believing it.",
            measurement.why_not_comparable()
        );
        capability_enforced = false;
    }
    assert!(
        !capability_enforced || frontier >= baseline,
        "REGRESSION [{family}]: frontier {frontier} < committed baseline {baseline} — a \
         roadmap lever lost ground. (Lowering the baseline is only correct if the loss is \
         understood and accepted.)\n\
         Before believing this: {}. This ratchet is a WALL-CLOCK measurement, and the \
         budget above was already scaled to this machine's measured throughput, so the \
         box has been compensated for — but only within {SCALE_LIMIT:.1}x. Each undecided \
         point was also retried up to {ATTEMPTS} times. Re-run on an otherwise idle \
         machine (no parallel `cargo test`, no other solver sweep) before concluding a \
         lever regressed, and compare the `near-budget` line above: if the lost instances \
         sit within 20 % of the {:.0} ms budget, the measurement is at its resolution \
         limit, not the solver.",
        measurement.describe(),
        measurement.budget_ms(),
    );

    // The clock ratchet. Deliberately AFTER the capability assert: a lost lever
    // is the more fundamental finding, and a family that stopped deciding its
    // pinned instances will also have failed above.
    if let Some(message) = timing_fault
        && timing_enforced
    {
        panic!("{message}");
    }
}

/// `bench-results/frontier/<family>.json`. Hand-rolled (no `serde_json` dep in
/// the solver test crate) — the schema is tiny and stable.
#[allow(clippy::too_many_arguments)]
fn write_curve_json(
    family: &str,
    baseline: u32,
    frontier: u32,
    curve: &[CurvePoint],
    measurement: &Measurement,
    timing: &TimingBaseline,
    measured: &TimingMeasured,
    timing_enforced: bool,
    timing_ok: bool,
) {
    let dir = artifact_dir();
    if let Err(error) = std::fs::create_dir_all(&dir) {
        eprintln!("warn: could not create {}: {error}", dir.display());
        return;
    }
    let mut json = String::new();
    json.push_str("{\n");
    let _ = writeln!(json, "  \"family\": \"{family}\",");
    let _ = writeln!(json, "  \"baseline\": {baseline},");
    let _ = writeln!(json, "  \"frontier\": {frontier},");
    let _ = writeln!(json, "  \"budget_ms\": {:.0},", measurement.budget_ms());
    let _ = writeln!(json, "  \"budget_ms_nominal\": {},", BUDGET.as_millis());
    // The measurement's reference frame, recorded WITH the number. A frontier
    // without the machine it was taken on is not a measurement, and the 35/38/40
    // spread in the header is what that costs.
    let _ = writeln!(json, "  \"machine\": {{");
    let _ = writeln!(
        json,
        "    \"host\": \"{}\", \"cpus\": {}, \"model\": \"{}\",",
        measurement.machine.host, measurement.machine.cpus, measurement.machine.model
    );
    let _ = writeln!(
        json,
        "    \"load_start\": {}, \"load_end\": {},",
        measurement
            .load_start
            .map_or_else(|| "null".to_owned(), |l| format!("{l:.2}")),
        measurement
            .load_end
            .map_or_else(|| "null".to_owned(), |l| format!("{l:.2}")),
    );
    let _ = writeln!(
        json,
        "    \"calibration_ms\": {:.1}, \"calibration_end_ms\": {},",
        measurement.calibration_start_ms,
        measurement
            .calibration_end_ms
            .map_or_else(|| "null".to_owned(), |ms| format!("{ms:.1}")),
    );
    let _ = writeln!(
        json,
        "    \"calibration_reference_ms\": {CALIBRATION_REFERENCE_MS:.1},"
    );
    let _ = writeln!(
        json,
        "    \"calibration_reference_machine\": \"{CALIBRATION_REFERENCE_MACHINE}\","
    );
    let _ = writeln!(
        json,
        "    \"scale\": {:.3}, \"raw_scale\": {:.3}, \"comparable\": {}, \"ratchetable\": {}",
        measurement.scale,
        measurement.raw_scale,
        measurement.comparable(),
        measurement.ratchetable(),
    );
    let _ = writeln!(json, "  }},");
    // The TIMING ratchet's whole state, next to the machine that produced it.
    //
    // `"enforced"` is the field a reader checks before believing a `"verdict"`,
    // and it is false exactly when `machine.comparable` is false (or on CI) —
    // the same flag that governs the capability ratchet. A busy box therefore
    // records its numbers and asserts nothing: this is the mechanism that keeps
    // the gate quiet under load, and it is the one the 35 / 39 / 40 spread at
    // 1-minute loads 34 / 5.4 / 1.17 (frontier-ratchet-reference-frame.md) made
    // necessary.
    //
    // `calibrated_ms` = `solve_ms / machine.scale`, i.e. reference-machine
    // milliseconds; `calibrated_total_ms` is their sum over the pinned `N` and
    // is what `ceiling_ms` bounds. `baseline_{min,median,max}_ms` are the
    // measured spread over `baseline_runs` runs of this binary on this box, and
    // `ceiling_ms` = `band_factor` x `baseline_max_ms`.
    let _ = writeln!(json, "  \"timing\": {{");
    let pins: Vec<String> = timing.pins.iter().map(u32::to_string).collect();
    let _ = writeln!(json, "    \"pins\": [{}],", pins.join(", "));
    let _ = writeln!(
        json,
        "    \"calibrated_total_ms\": {},",
        measured
            .calibrated_total_ms
            .map_or_else(|| "null".to_owned(), |ms| format!("{ms:.1}"))
    );
    let _ = writeln!(
        json,
        "    \"baseline_min_ms\": {:.1}, \"baseline_median_ms\": {:.1}, \
         \"baseline_max_ms\": {:.1},",
        timing.min_ms, timing.median_ms, timing.max_ms
    );
    let _ = writeln!(
        json,
        "    \"ceiling_ms\": {:.1}, \"band_factor\": {TIMING_BAND_FACTOR:.2}, \
         \"baseline_runs\": {TIMING_BASELINE_RUNS},",
        timing.ceiling_ms
    );
    let _ = writeln!(
        json,
        "    \"enforced\": {timing_enforced}, \"verdict\": \"{}\",",
        if timing_ok { "ok" } else { "regression" }
    );
    json.push_str("    \"observed\": [\n");
    for (i, p) in measured.points.iter().enumerate() {
        let comma = if i + 1 < measured.points.len() {
            ","
        } else {
            ""
        };
        let _ = writeln!(
            json,
            "      {{ \"n\": {}, \"decided\": {}, \"solve_ms\": {}, \"calibrated_ms\": {} }}{comma}",
            p.n,
            p.decided,
            p.solve_ms
                .map_or_else(|| "null".to_owned(), |ms| format!("{ms:.1}")),
            p.calibrated_ms
                .map_or_else(|| "null".to_owned(), |ms| format!("{ms:.1}")),
        );
    }
    json.push_str("    ]\n  },\n");
    json.push_str("  \"curve\": [\n");
    for (i, p) in curve.iter().enumerate() {
        let comma = if i + 1 < curve.len() { "," } else { "" };
        let _ = writeln!(
            json,
            "    {{ \"n\": {}, \"decided\": {}, \"status\": \"{}\", \"solve_ms\": {:.1} }}{comma}",
            p.n, p.decided_correct, p.status, p.solve_ms,
        );
    }
    json.push_str("  ]\n}\n");

    let path = dir.join(format!("{family}.json"));
    if let Err(error) = std::fs::write(&path, json) {
        eprintln!("warn: could not write {}: {error}", path.display());
    }
}

fn artifact_dir() -> PathBuf {
    artifact_dir_from_override(std::env::var_os(FRONTIER_ARTIFACT_DIR_ENV))
        .unwrap_or_else(|message| panic!("{message}"))
}

fn artifact_dir_from_override(override_dir: Option<OsString>) -> Result<PathBuf, &'static str> {
    if let Some(value) = override_dir {
        if value.is_empty() {
            return Err("AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR must not be empty");
        }
        let path = PathBuf::from(value);
        if !path.is_absolute() {
            return Err("AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR must be absolute");
        }
        return Ok(path);
    }
    // Tests run with CWD = crate dir (crates/axeyum-solver); artifacts live at
    // the workspace root under bench-results/.
    Ok(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../bench-results/frontier"))
}

// ===========================================================================
// Family 1: bv_reduction — lever: QF_BV word-level reduction (`preprocess`).
// ===========================================================================
//
// Instance `N` asserts the negation of a true-by-construction bit-vector
// identity whose left-hand side is a depth-`N` *constant-folding* tower of
// **multiplications**: `(((x * a1) * a2) … * aN) = x * A`, where
// `A = (a1·a2·…·aN) mod 2^width`. After word-level reduction (constant
// propagation + canonicalization, on by default in `check_auto`) the chain of
// constant multipliers folds to a single `x * A`, making the negation trivially
// UNSAT. Without reduction, the same instance bit-blasts **all `N` width-`width`
// multipliers** (each ~`width²` gates) into an AIG/CNF that, as `N` grows, blows
// the encoding budget and degrades to `unknown` — so the frontier is *the
// reduction's reach* (proven by `bv_reduction_falloff_is_the_lever`).
//
// Self-check: UNSAT by exhaustive enumeration over the single `width`-bit symbol
// `x` (an honest finite-domain proof — `2^width` cases). Multipliers (not
// adders) are the knob: an adder bit-blasts small even un-reduced, so it would
// not isolate the lever; a multiplier tower does.

const BV_REDUCTION_WIDTH: u32 = 8;

/// The multiplier-tower depth for `bv_reduction` instance `N`: quadratic, so the
/// bit-blast work grows fast enough to reach a real fall-off within the sweep.
fn bv_reduction_depth(n: u32) -> u32 {
    n * n
}

/// Build the `bv_reduction` instance of depth `N` as a self-checking
/// [`Scenario`] (UNSAT, exhaustively verified), then unwrap it to an
/// [`Instance`].
///
/// Returns `Option` to satisfy the [`sweep`] builder contract (other families
/// can stop building early); this family always constructs an instance.
#[allow(clippy::unnecessary_wraps)]
fn bv_reduction_instance(n: u32) -> Option<Instance> {
    let scenario = bv_reduction_scenario(n);
    scenario
        .self_check()
        .unwrap_or_else(|e| panic!("bv_reduction N={n} failed self-check: {e}"));
    Some(scenario_to_instance(&scenario))
}

fn bv_reduction_scenario(n: u32) -> Scenario {
    let width = BV_REDUCTION_WIDTH;
    let mask = (1u128 << width) - 1;
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);

    // Tower of constant multipliers: acc = (((x * a1) * a2) … * aD), tracking the
    // folded product A = (a1·a2·…·aD) mod 2^width. The constants are odd (so they
    // never collapse the product to 0 and the chain stays a genuine multiplier
    // structure un-reduced).
    //
    // The tower DEPTH grows *quadratically* in `N` (`depth = N²`): reduction must
    // collapse all `N²` width-`width` multipliers (each ~`width²` gates) before
    // the bit-blast fits the budget, so a real (non-ceiling) fall-off lands within
    // a bounded sweep, and the frontier measures the *reach of the collapse*.
    let depth = bv_reduction_depth(n);
    let mut acc = x;
    let mut product: u128 = 1;
    for k in 1..=depth {
        // Odd constants in 3, 5, 7, … (cycled into range).
        let a = ((u128::from(k) * 2 + 1) & mask) | 1;
        let c = arena.bv_const(width, a).unwrap();
        acc = arena.bv_mul(acc, c).unwrap();
        product = (product * a) & mask;
    }
    // Right-hand side: the single folded multiplier `x * A`.
    let a_const = arena.bv_const(width, product).unwrap();
    let folded = arena.bv_mul(x, a_const).unwrap();

    // Assert the *negation* of `acc == x * A`. The identity holds for every `x`,
    // so the negation is UNSAT.
    let eq = arena.eq(acc, folded).unwrap();
    let neq = arena.not(eq).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(neq).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("bv_reduction/n{n}_depth{depth}"),
        family: Family::Identity,
        width,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Unsat {
            // `self_check` recomputes the exhaustive evidence; this is a
            // placeholder of the right variant.
            evidence: UnsatEvidence::Exhaustive { cases: 0 },
        },
    }
}

// ===========================================================================
// Family 2: lia_cuts — lever: QF_LIA bounded integer engine (branch-and-bound).
// ===========================================================================
//
// Instance `N` is a satisfiable integer-linear system over `N` variables whose
// in-box integer solution is pinned by a tower of mutually-constraining boxes,
// strict orderings, and one scaled-sum cut — the kind of system that needs
// progressively deeper branch-and-bound to land on the integer witness as `N`
// (and the coefficients) grow. We keep it SAT and witness-checkable: the witness
// is chosen first and every constraint asserted to hold for it, so the
// self-check is purely the evaluator confirming the witness (UNSAT over
// `Sort::Int` has no finite enumeration, so we deliberately stay
// witness-checkable — fully oracle-free).
//
// The difficulty knob is `N` = the number of coupled variables (and the growth
// of the coefficients `a_i`), which deepens the search needed to find the model.

/// Returns `Option` for the [`sweep`] builder contract; this family always
/// constructs an instance.
#[allow(clippy::unnecessary_wraps)]
fn lia_cuts_instance(n: u32) -> Option<Instance> {
    let scenario = lia_cuts_scenario(n);
    scenario
        .self_check()
        .unwrap_or_else(|e| panic!("lia_cuts N={n} failed self-check: {e}"));
    Some(scenario_to_instance(&scenario))
}

fn lia_cuts_scenario(n: u32) -> Scenario {
    let count = n as usize; // `n <= MAX_N`, no truncation
    let mut arena = TermArena::new();
    let mut witness = Assignment::new();

    // Each variable lives in a WIDE box whose half-width grows with `N`, so the
    // integer feasible region (and therefore the branch-and-bound search) expands
    // with the knob — the tight scaled-sum cut then pins a single integer corner
    // the engine must *find* inside that growing box.
    let half = i128::from(2 * n + 4); // box half-width grows with N
    let mut vars = Vec::with_capacity(count);
    let mut witness_vals = Vec::with_capacity(count);
    for i in 0..count {
        let sym = arena.declare(&format!("x{i}"), Sort::Int).unwrap();
        // Witness sits off-center in its box so the corner is non-obvious.
        let val = 1 + i128::try_from(i).unwrap() * 3;
        witness.set(sym, Value::Int(val));
        vars.push(arena.var(sym));
        witness_vals.push(val);
    }

    let mut goals = Vec::new();

    // Wide box: witness - half <= x_i <= witness + half. The region grows with N.
    for (i, &val) in witness_vals.iter().enumerate() {
        let lo = arena.int_const(val - half);
        let hi = arena.int_const(val + half);
        goals.push(arena.int_ge(vars[i], lo).unwrap());
        goals.push(arena.int_le(vars[i], hi).unwrap());
    }

    // Strict ordering x0 < x1 < … < x_{n-1} (consistent with the witness),
    // coupling the boxes so the search must respect a chain of inequalities.
    for i in 0..count.saturating_sub(1) {
        goals.push(arena.int_lt(vars[i], vars[i + 1]).unwrap());
    }

    // Two tight scaled-sum cuts with growing, coprime-ish coefficients — they
    // intersect the wide boxes in a thin lattice the engine must branch to hit.
    // Both pinned to the witness so the system is SAT by construction.
    for base in [2i128, 3i128] {
        let mut acc: Option<TermId> = None;
        let mut sum_val: i128 = 0;
        for (i, &val) in witness_vals.iter().enumerate() {
            // Coefficient grows with the position `i` and the cut's `base`.
            let coeff = base + i128::try_from(i).unwrap() * (base + 1);
            sum_val += coeff * val;
            let c = arena.int_const(coeff);
            let term = arena.int_mul(c, vars[i]).unwrap();
            acc = Some(match acc {
                None => term,
                Some(prev) => arena.int_add(prev, term).unwrap(),
            });
        }
        let lhs = acc.unwrap();
        let rhs = arena.int_const(sum_val);
        goals.push(arena.eq(lhs, rhs).unwrap());
    }

    let mut builder = Query::builder(&arena);
    for g in goals {
        builder.assert(g).unwrap();
    }
    let query = builder.build();

    Scenario {
        name: format!("lia_cuts/system_n{n}"),
        family: Family::Integer,
        width: 0,
        seed: 0,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

// ===========================================================================
// Family 3: string_bound — lever: bounded-string STRING_MAX_LEN (ADR-0029).
// ===========================================================================
//
// Instance `N` requires a string `s` of length exactly `N` that contains a
// fixed substring — `(str.len s) = N ∧ (str.contains s "ab")`. A concrete
// witness string of length `N` (containing "ab") satisfies it by construction.
// The packed-string model caps `max_len` at `STRING_MAX_LEN` (8), so once `N`
// exceeds the bound the instance can no longer be packed and axeyum degrades to
// `unknown` — the frontier is the bound's reach. Raise the bound ⇒ frontier
// rises.
//
// Self-check: the witness is verified in plain Rust against the *string-theory*
// semantics of the constraints (length and substring containment) — an
// independent check that never touches the solver's packed-BV model. SAT is the
// claim, so a wrong `unsat` from axeyum is caught (a witness provably exists).

/// The fixed substring every `string_bound` witness must contain.
const STRING_NEEDLE: &str = "ab";

fn string_bound_witness(n: u32) -> String {
    // A length-`N` string that contains "ab": "ab" padded with 'c' up to length
    // N. The sweep starts at N = 2 (the needle length).
    let mut s = String::from(STRING_NEEDLE);
    while u32::try_from(s.len()).unwrap_or(u32::MAX) < n {
        s.push('c');
    }
    s
}

/// Independently verify the witness against the string-theory constraints — no
/// solver involved. Returns `true` iff the concrete string satisfies
/// `len == n ∧ contains needle`.
fn string_bound_self_check(witness: &str, n: u32) -> bool {
    u32::try_from(witness.len()).is_ok_and(|len| len == n) && witness.contains(STRING_NEEDLE)
}

fn string_bound_smtlib(n: u32) -> String {
    format!(
        "(set-logic QF_S)\n\
         (declare-const s String)\n\
         (assert (= (str.len s) {n}))\n\
         (assert (str.contains s \"{STRING_NEEDLE}\"))\n\
         (check-sat)\n"
    )
}

/// Solve one `string_bound` instance end-to-end (it bypasses the generic
/// [`sweep`] because its solve path is `solve_smtlib`, not `check_auto`).
fn string_bound_point(n: u32, config: &SolverConfig, budget: Duration) -> CurvePoint {
    let witness = string_bound_witness(n);
    assert!(
        string_bound_self_check(&witness, n),
        "string_bound N={n}: constructed witness {witness:?} fails its own self-check",
    );

    let text = string_bound_smtlib(n);
    let cfg = config.clone();
    let (tx, rx) = mpsc::channel();
    let t0 = Instant::now();
    thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let res = solve_smtlib(&text, &cfg).map(|o| o.result);
            let _ = tx.send(res);
        })
        .expect("spawn string solver thread");
    let outcome = rx.recv_timeout(budget + Duration::from_secs(1));
    let solve_ms = t0.elapsed().as_secs_f64() * 1000.0;

    // Ground truth is SAT (a witness provably exists). A wrong `unsat` is a hard
    // failure; `unknown` past the bound is the expected benign fall-off.
    let (decided_correct, status) = match outcome {
        Ok(Ok(CheckResult::Sat(_))) => (true, "sat"),
        Ok(Ok(CheckResult::Unsat)) => {
            panic!(
                "SOUNDNESS FAILURE [string_bound N={n}]: solver said unsat but witness \
                 {witness:?} (len {n}, contains {STRING_NEEDLE:?}) provably satisfies it",
            );
        }
        Ok(Ok(CheckResult::Unknown(_))) => (false, "unknown"),
        Ok(Err(_)) => (false, "error"),
        Err(_) => (false, "timeout"),
    };

    CurvePoint {
        n,
        decided_correct,
        status,
        solve_ms,
    }
}

// ===========================================================================
// Family 4: nra_degree — lever: QF_NRA CAD / high-degree refutation.
// ===========================================================================
//
// Instance `N` is the shifted sum-of-even-powers infeasibility ported from the
// neutral graduated corpus' `sos-strict-unsat-dN` family
// (`scripts/gen-graduated-nra-nia.py`, commit `97d903b`):
//
//     (assert (< (+ (x-1)^{2N} (y-2)^{2N} 1.0) 0.0))   over Real x, y
//
// where `(x-1)^{2N}` and `(y-2)^{2N}` are *even* powers, hence `>= 0` for every
// real, so the asserted sum is `>= 1 > 0` and the strict `< 0` is impossible:
// UNSAT by construction, for every half-degree `N >= 1`. As `N` grows the degree
// `2N` rises and the CAD/high-degree refutation gets harder — the frontier is the
// largest degree axeyum refutes, *the reach of the NRA decider's high-degree
// refutation*. The measured cliff is `N=2` (degree 4); degrees 6/8/10 → unknown.
//
// Self-check (oracle-free, independent of the bit-blast/CAD search path): the
// UNSAT is a from-first-principles nonnegativity fact — an even power of any real
// is `>= 0`, so the sum of two even powers plus 1 is `>= 1`, never `< 0`. We
// assert that fact directly AND bounded-verify it over a rational sample grid
// (no grid point satisfies the strict inequality), so a corrupted generator that
// emitted a satisfiable instance is caught before the solver is trusted.

/// The fixed real shifts for the two `nra_degree` variables (matching the ported
/// `sos-strict-unsat` construction: `(x-1)` and `(y-2)`).
const NRA_SHIFTS: [i64; 2] = [1, 2];

/// `(* base base … )` `e` times as an SMT-LIB s-expression, `e >= 1`.
fn smt_power(base: &str, e: u32) -> String {
    if e == 1 {
        return base.to_string();
    }
    let mut s = String::from("(*");
    for _ in 0..e {
        s.push(' ');
        s.push_str(base);
    }
    s.push(')');
    s
}

/// The `sos-strict-unsat` SMT-LIB text for half-degree `N` (so even degree
/// `2N`): `(x-1)^{2N} + (y-2)^{2N} + 1 < 0`, an UNSAT real-nonlinear instance.
fn nra_degree_smtlib(n: u32) -> String {
    let deg = 2 * n;
    let xm = format!("(- x {}.0)", NRA_SHIFTS[0]);
    let ym = format!("(- y {}.0)", NRA_SHIFTS[1]);
    let t1 = smt_power(&xm, deg);
    let t2 = smt_power(&ym, deg);
    format!(
        "(set-logic QF_NRA)\n\
         (set-info :status unsat)\n\
         (declare-fun x () Real)\n\
         (declare-fun y () Real)\n\
         (assert (< (+ {t1} {t2} 1.0) 0.0))\n\
         (check-sat)\n"
    )
}

/// Independently confirm the `nra_degree` instance is genuinely UNSAT, with NO
/// solver involved. The strict inequality `(x-1)^{2N} + (y-2)^{2N} + 1 < 0` is
/// impossible because each even power is `>= 0`, so the sum is `>= 1`. We
/// re-establish that two ways:
///
/// 1. **First-principles nonnegativity**: `2N` is even, so `t^{2N} >= 0` for all
///    real `t`; the construction is sound iff the exponent is even and `>= 2`.
/// 2. **Bounded rational grid**: evaluate the left-hand side at a dense grid of
///    rational `(x, y)` (including the shift centers, where the powers vanish and
///    the value is the minimum `1`) and confirm NO point makes it `< 0` — a
///    concrete refutation of the strict inequality on the sampled region.
///
/// Returns `true` iff both hold (the instance is UNSAT by construction).
fn nra_degree_self_check(n: u32) -> bool {
    nra_degree_self_check_with_degree(2 * n)
}

/// The body of [`nra_degree_self_check`] parameterized on the raw exponent, so a
/// soundness-negative test can feed it a corrupted (odd) degree and confirm the
/// check REJECTS it. Used with an even degree in the real path.
fn nra_degree_self_check_with_degree(deg: u32) -> bool {
    // (1) The exponent must be a positive even number for the positivity argument.
    if deg < 2 || !deg.is_multiple_of(2) {
        return false;
    }
    // (2) Bounded rational grid in steps of 1/4 over [-3, 5] in both x and y,
    // which contains both shift centers (x=1, y=2 — where each power is 0 and the
    // LHS attains its minimum of exactly 1). Exact rational arithmetic via i128
    // numerator over a fixed denominator power, so there is no float rounding.
    let denom: i128 = 4; // grid step 1/4
    let lo: i128 = -3 * denom;
    let hi: i128 = 5 * denom;
    for xi in lo..=hi {
        for yi in lo..=hi {
            // value = (x-1)^deg + (y-2)^deg + 1, computed as exact rationals; we
            // only need its SIGN, so compare numerators over the common positive
            // denominator denom^deg.
            let dx = xi - i128::from(NRA_SHIFTS[0]) * denom; // numerator of (x-1) over denom
            let dy = yi - i128::from(NRA_SHIFTS[1]) * denom; // numerator of (y-2) over denom
            let px = ipow_i128(dx, deg); // (x-1)^deg numerator over denom^deg
            let py = ipow_i128(dy, deg);
            let dpow = ipow_i128(denom, deg); // common denominator (positive)
            // value * denom^deg = px + py + denom^deg  (all over denom^deg > 0).
            // Saturating adds: at large degree the even powers can saturate to
            // `i128::MAX` (see `ipow_i128`), and a plain `+` would overflow. Every
            // summand here is a nonnegative even power (or the positive constant),
            // so the sum is nonnegative and saturating can only *over*-state it — it
            // can never turn a genuinely-positive value negative, so the `< 0`
            // refutation stays sound.
            let value_num = px.saturating_add(py).saturating_add(dpow);
            // UNSAT means NO grid point satisfies value < 0; value_num shares the
            // positive denominator's sign, so value < 0 iff value_num < 0.
            if value_num < 0 {
                return false; // a satisfying point => the generator is corrupt
            }
        }
    }
    true
}

/// `base^exp` in `i128`; `exp` small (degrees stay <= 10 in the sweep) and the
/// grid keeps `base` tiny, so this never overflows in practice. Saturating to be
/// safe — a saturated (still-positive) even power can only *over*-state the LHS,
/// so it can never spuriously report a satisfying point.
fn ipow_i128(base: i128, exp: u32) -> i128 {
    let mut acc: i128 = 1;
    for _ in 0..exp {
        acc = acc.saturating_mul(base);
    }
    acc
}

/// Solve one `nra_degree` instance end-to-end via `solve_smtlib` (the SMT-LIB
/// text front door, like `string_bound`). Ground truth is UNSAT; a decided `sat`
/// is a hard soundness failure, `unknown` past the cliff is the benign fall-off.
fn nra_degree_point(n: u32, config: &SolverConfig, budget: Duration) -> CurvePoint {
    assert!(
        nra_degree_self_check(n),
        "nra_degree N={n}: the constructed instance (degree {}) failed its own \
         independent UNSAT self-check (nonnegativity + bounded grid)",
        2 * n,
    );
    let text = nra_degree_smtlib(n);
    solve_smtlib_unsat_point("nra_degree", n, &text, config, budget)
}

// ===========================================================================
// Family 5: nia_unsat — lever: QF_NIA integer-nonlinear UNSAT (the decider gap).
// ===========================================================================
//
// Instance `N` is the bounded integer-nonlinear infeasibility ported from the
// neutral graduated corpus' `no-square-mod-bN` family
// (`scripts/gen-graduated-nra-nia.py`, commit `97d903b`):
//
//     (assert (= (* x x) (+ (* m t) r)))   ; x^2 = m·t + r, i.e. x^2 ≡ r (mod m)
//     (assert (and (<= 0 x) (< x {b·m})))  ; 0 <= x < b·m
//     (assert (>= t 0))
//
// with `r` a quadratic **non-residue** mod `m` (no integer square is ≡ r mod m),
// so the system is infeasible for every bound multiplier `b`. The knob `N = b`
// scales the bound `b·m`. This is the measured NIA *blind spot*: axeyum returns
// `unknown` on every `N` today, so the frontier is `0` — and that `0` is a valid
// tracking row that RISES the moment the NIA decider gains integer-nonlinear
// UNSAT capability.
//
// Self-check (oracle-free, exhaustive bounded enumeration): the bound makes the
// domain finite, so we enumerate EVERY integer `x` in `0 <= x < b·m` and confirm
// none has `x^2 ≡ r (mod m)` (equivalently, `r` is not in the residue table of
// squares mod `m`, which we also recompute). No square in range hits `r` => the
// system is genuinely UNSAT, established without any solver.

/// The `(modulus, non_residue)` pairs for the `nia_unsat` family (ported from the
/// graduated corpus' `nonres_cases`). Each `r` is a quadratic non-residue mod
/// `m`, re-confirmed by enumeration in the self-check.
const NIA_NONRES_CASES: [(i64, i64); 8] = [
    (3, 2), // squares mod 3: {0,1}; 2 non-residue
    (4, 2), // squares mod 4: {0,1}; 2 non-residue
    (4, 3), // 3 non-residue mod 4
    (5, 2), // squares mod 5: {0,1,4}; 2 non-residue
    (5, 3), // 3 non-residue mod 5
    (7, 3), // squares mod 7: {0,1,2,4}; 3 non-residue
    (8, 3), // squares mod 8: {0,1,4}; 3 non-residue
    (8, 5), // 5 non-residue mod 8
];

/// The `(modulus, residue)` for `nia_unsat` instance `N` (1-based into
/// [`NIA_NONRES_CASES`], cycling so the sweep can grow the bound past 8 cases).
fn nia_case(n: u32) -> (i64, i64) {
    let idx = (n as usize - 1) % NIA_NONRES_CASES.len();
    NIA_NONRES_CASES[idx]
}

/// The `no-square-mod` SMT-LIB text for bound multiplier `N`: `x^2 = m·t + r`
/// with `0 <= x < N·m`, `t >= 0` — UNSAT because `r` is a non-residue mod `m`.
fn nia_unsat_smtlib(n: u32) -> String {
    let (m, r) = nia_case(n);
    let upper = i128::from(n) * i128::from(m);
    format!(
        "(set-logic QF_NIA)\n\
         (set-info :status unsat)\n\
         (declare-fun x () Int)\n\
         (declare-fun t () Int)\n\
         (assert (= (* x x) (+ (* {m} t) {r})))\n\
         (assert (and (<= 0 x) (< x {upper})))\n\
         (assert (>= t 0))\n\
         (check-sat)\n"
    )
}

/// Independently confirm the `nia_unsat` instance is genuinely UNSAT by
/// **exhaustive bounded enumeration** — no solver involved. The bound makes the
/// domain finite, so we:
///
/// 1. recompute the residue table of squares mod `m` and confirm `r` is NOT in it
///    (so `r` is a quadratic non-residue), and
/// 2. enumerate every integer `x` in `0 <= x < N·m` and confirm none satisfies
///    `x^2 ≡ r (mod m)` (i.e. no `t >= 0` makes `x^2 = m·t + r`, since that forces
///    `x^2 mod m == r` and `t = (x^2 - r)/m >= 0` for `x^2 >= r`).
///
/// Returns `true` iff no integer in range squares to `r` mod `m` — a genuine,
/// oracle-free proof that the system is infeasible.
fn nia_unsat_self_check(n: u32) -> bool {
    let (m, r) = nia_case(n);
    nia_unsat_self_check_with_case(n, r, m)
}

/// The body of [`nia_unsat_self_check`] parameterized on `(n, r, m)`, so a
/// soundness-negative test can feed it a quadratic RESIDUE `r` and confirm the
/// exhaustive enumeration REJECTS it (finds a satisfying `x`).
fn nia_unsat_self_check_with_case(n: u32, r: i64, m: i64) -> bool {
    if m <= 0 || r < 0 || r >= m {
        return false;
    }
    // (1) Residue table: r must be a non-residue mod m.
    let residues: std::collections::BTreeSet<i64> = (0..m).map(|i| (i * i) % m).collect();
    if residues.contains(&r) {
        return false;
    }
    // (2) Exhaustive enumeration over the finite domain 0 <= x < N·m.
    let upper = i128::from(n) * i128::from(m);
    let mm = i128::from(m);
    let rr = i128::from(r);
    let mut x: i128 = 0;
    while x < upper {
        // x^2 = m·t + r has a solution t >= 0 iff x^2 % m == r and x^2 >= r.
        let sq = x * x;
        if sq % mm == rr && sq >= rr {
            return false; // a satisfying x => the instance is NOT unsat
        }
        x += 1;
    }
    true
}

/// Solve one `nia_unsat` instance end-to-end via `solve_smtlib`. Ground truth is
/// UNSAT; a decided `sat` is a hard soundness failure, `unknown` (the measured
/// status today) is the benign blind-spot fall-off.
fn nia_unsat_point(n: u32, config: &SolverConfig, budget: Duration) -> CurvePoint {
    assert!(
        nia_unsat_self_check(n),
        "nia_unsat N={n}: the constructed instance failed its own independent \
         UNSAT self-check (residue table + exhaustive bounded enumeration)",
    );
    let text = nia_unsat_smtlib(n);
    solve_smtlib_unsat_point("nia_unsat", n, &text, config, budget)
}

// ---------------------------------------------------------------------------
// Shared SMT-LIB-text UNSAT solving (nra_degree, nia_unsat).
// ---------------------------------------------------------------------------

/// Solve a known-UNSAT SMT-LIB script under [`BUDGET`] on a worker thread (sound
/// timeout on overrun) and classify the outcome into a [`CurvePoint`].
///
/// Ground truth is UNSAT (already established by the caller's independent
/// self-check), so a decided `sat` is a **hard soundness failure** (panic);
/// `unknown`/`timeout`/`error` are the benign fall-off past the decider's reach.
fn solve_smtlib_unsat_point(
    family: &str,
    n: u32,
    text: &str,
    config: &SolverConfig,
    budget: Duration,
) -> CurvePoint {
    let text = text.to_string();
    let cfg = config.clone();
    let (tx, rx) = mpsc::channel();
    let t0 = Instant::now();
    thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let res = solve_smtlib(&text, &cfg).map(|o| o.result);
            let _ = tx.send(res);
        })
        .expect("spawn smtlib solver thread");
    let outcome = rx.recv_timeout(budget + Duration::from_secs(1));
    let solve_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let (decided_correct, status) = match outcome {
        Ok(Ok(CheckResult::Unsat)) => (true, "unsat"),
        Ok(Ok(CheckResult::Sat(_))) => {
            panic!(
                "SOUNDNESS FAILURE [{family} N={n}]: solver said sat but the instance is \
                 UNSAT by an independent self-check (nonnegativity / exhaustive enumeration)",
            );
        }
        Ok(Ok(CheckResult::Unknown(_))) => (false, "unknown"),
        Ok(Err(_)) => (false, "error"),
        Err(_) => (false, "timeout"),
    };

    CurvePoint {
        n,
        decided_correct,
        status,
        solve_ms,
    }
}

/// Sweep a point-based SMT-LIB UNSAT family (`nra_degree`, `nia_unsat`),
/// mirroring the generic [`sweep`] frontier rule but over the `solve_smtlib`
/// path. The frontier is the largest `N` decided-correct with no undecided `N`
/// below it; we overshoot [`OVERSHOOT`] points past the first miss to log the
/// fall-off. A `start` lets a family begin its knob above 1.
fn smtlib_unsat_sweep(
    start: u32,
    mut point: impl FnMut(u32) -> CurvePoint,
) -> (u32, Vec<CurvePoint>) {
    let mut curve = Vec::new();
    let mut frontier = 0u32;
    let mut consecutive_undecided = 0u32;

    for n in start..=MAX_N {
        let p = point(n);
        if p.decided_correct {
            if consecutive_undecided == 0 {
                frontier = n;
            }
        } else {
            consecutive_undecided += 1;
        }
        curve.push(p);
        if consecutive_undecided > OVERSHOOT {
            break;
        }
    }

    (frontier, curve)
}

// ---------------------------------------------------------------------------
// Shared helpers.
// ---------------------------------------------------------------------------

/// Flatten a self-checked [`Scenario`] into an [`Instance`] for the solver. The
/// arena is cloned (cheap interned IDs) so the scenario's own copy stays intact.
fn scenario_to_instance(scenario: &Scenario) -> Instance {
    Instance {
        arena: scenario.arena.clone(),
        assertions: scenario.query.solver_terms().collect(),
        expect_sat: scenario.expectation.is_sat(),
    }
}

// ===========================================================================
// Tests.
// ===========================================================================

#[test]
fn artifact_directory_override_is_explicit_and_absolute() {
    let historical = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../bench-results/frontier");
    assert_eq!(artifact_dir_from_override(None).unwrap(), historical);

    let absolute = std::env::temp_dir().join("axeyum-frontier-artifact-test");
    assert_eq!(
        artifact_dir_from_override(Some(absolute.clone().into_os_string())).unwrap(),
        absolute
    );
    assert_eq!(
        artifact_dir_from_override(Some(OsString::new())),
        Err("AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR must not be empty")
    );
    assert_eq!(
        artifact_dir_from_override(Some(OsString::from("relative/frontier"))),
        Err("AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR must be absolute")
    );
}

#[test]
fn frontier_bv_reduction() {
    let mut measurement = Measurement::start();
    let config = SolverConfig::new().with_timeout(measurement.budget());
    let (frontier, curve) = sweep("bv_reduction", &config, &measurement, bv_reduction_instance);
    report_and_assert(
        "bv_reduction",
        BASELINE_BV_REDUCTION,
        frontier,
        &curve,
        &mut measurement,
        &TIMING_BV_REDUCTION,
    );
}

#[test]
fn frontier_lia_cuts() {
    let mut measurement = Measurement::start();
    let config = SolverConfig::new().with_timeout(measurement.budget());
    let (frontier, curve) = sweep("lia_cuts", &config, &measurement, lia_cuts_instance);
    report_and_assert(
        "lia_cuts",
        BASELINE_LIA_CUTS,
        frontier,
        &curve,
        &mut measurement,
        &TIMING_LIA_CUTS,
    );
}

#[test]
fn frontier_string_bound() {
    let mut measurement = Measurement::start();
    let config = SolverConfig::new().with_timeout(measurement.budget());
    let mut curve = Vec::new();
    let mut frontier = 0u32;
    let mut consecutive_undecided = 0u32;

    // Strings start at length 2 (the needle is "ab"); the frontier is reported in
    // the same units as N (so a length-`L` string is point N=L).
    for n in 2..=MAX_N {
        let point = string_bound_point(n, &config, measurement.budget());
        if point.decided_correct {
            if consecutive_undecided == 0 {
                frontier = n;
            }
        } else {
            consecutive_undecided += 1;
        }
        curve.push(point);
        if consecutive_undecided > OVERSHOOT {
            break;
        }
    }

    report_and_assert(
        "string_bound",
        BASELINE_STRING_BOUND,
        frontier,
        &curve,
        &mut measurement,
        &TIMING_STRING_BOUND,
    );
}

#[test]
fn frontier_nra_degree() {
    let mut measurement = Measurement::start();
    let config = SolverConfig::new().with_timeout(measurement.budget());
    let budget = measurement.budget();
    let (frontier, curve) = smtlib_unsat_sweep(1, |n| nra_degree_point(n, &config, budget));
    report_and_assert(
        "nra_degree",
        BASELINE_NRA_DEGREE,
        frontier,
        &curve,
        &mut measurement,
        &TIMING_NRA_DEGREE,
    );
}

#[test]
fn frontier_nia_unsat() {
    let mut measurement = Measurement::start();
    let config = SolverConfig::new().with_timeout(measurement.budget());
    let budget = measurement.budget();
    let (frontier, curve) = smtlib_unsat_sweep(1, |n| nia_unsat_point(n, &config, budget));
    report_and_assert(
        "nia_unsat",
        BASELINE_NIA_UNSAT,
        frontier,
        &curve,
        &mut measurement,
        &TIMING_NIA_UNSAT,
    );
}

/// The reference frame itself, tested: the calibration kernel is frozen, and the
/// comparability rules refuse exactly the two readings that motivated them.
///
/// The 35 (taken at load 34 on 24 cores) and the 40 (taken idle, at the sweep
/// ceiling) are the two numbers this suite must not silently accept, so they are
/// asserted here as scale bands rather than left in a comment.
#[test]
fn calibration_frames_the_measurement() {
    // Frozen: the reference constant times a specific amount of work.
    assert_eq!(calibration_kernel(), CALIBRATION_CHECKSUM);
    assert_eq!(
        calibration_kernel(),
        CALIBRATION_CHECKSUM,
        "and it is stable"
    );

    let live = calibration_ms();
    assert!(
        live > 0.0 && live.is_finite(),
        "calibration produced {live} ms"
    );
    // Printed so `--nocapture` on this one test is enough to re-measure the
    // reference (and to see what a loaded box is doing) without a separate tool.
    let here = machine();
    eprintln!(
        "CALIBRATION median {live:.1} ms (reference {CALIBRATION_REFERENCE_MS:.1} ms, \
         scale {:.2}x) on {} / {} cpus / {}, load {}",
        live / CALIBRATION_REFERENCE_MS,
        here.host,
        here.cpus,
        here.model,
        load_note(),
    );

    let frame = |raw_scale: f64, end_ms: Option<f64>| Measurement {
        machine: machine(),
        calibration_start_ms: CALIBRATION_REFERENCE_MS * raw_scale,
        calibration_end_ms: end_ms,
        raw_scale,
        scale: raw_scale.clamp(1.0 / SCALE_LIMIT, SCALE_LIMIT),
        load_start: None,
        load_end: None,
    };

    // A quiet reference-speed box: comparable, and may raise a baseline.
    let quiet = frame(1.0, Some(CALIBRATION_REFERENCE_MS));
    assert!(quiet.comparable() && quiet.ratchetable());
    assert_eq!(quiet.budget().as_millis(), BUDGET.as_millis());

    // A busy box (the 35): the budget stretches to compensate, and the run may
    // NOT be used to move a baseline in either direction.
    let busy = frame(1.8, Some(CALIBRATION_REFERENCE_MS * 1.8));
    assert!(busy.comparable(), "1.8x is inside the {SCALE_LIMIT}x band");
    assert!(
        !busy.ratchetable(),
        "a stretched budget cannot certify progress"
    );
    assert!(busy.budget() > BUDGET);

    // A machine (or a load) beyond the band: not comparable at all.
    let overloaded = frame(SCALE_LIMIT * 1.5, None);
    assert!(!overloaded.comparable());
    assert!(overloaded.why_not_comparable().contains("slower"));
    // ... and the budget is clamped, so the sweep cannot run away.
    let clamped_ms = overloaded.budget().as_secs_f64() * 1000.0;
    let expected_ms = BUDGET.as_secs_f64() * 1000.0 * SCALE_LIMIT;
    assert!(
        (clamped_ms - expected_ms).abs() < 1.0,
        "clamped budget {clamped_ms:.1} ms should be the {SCALE_LIMIT}x cap {expected_ms:.1} ms"
    );

    // A much faster machine is equally uncomparable — the symmetric failure,
    // and the one that produces a floor smaller boxes cannot meet.
    let faster = frame(1.0 / (SCALE_LIMIT * 1.5), None);
    assert!(!faster.comparable());
    assert!(faster.why_not_comparable().contains("faster"));

    // A moderately faster/idler box (the 40) is comparable — its number is real —
    // but must not raise a baseline either.
    let idle = frame(0.8, Some(CALIBRATION_REFERENCE_MS * 0.8));
    assert!(idle.comparable());
    assert!(!idle.ratchetable());
    assert!(idle.budget() < BUDGET);

    // The environment moving DURING the sweep invalidates the run even when both
    // endpoints are inside the band.
    let drifted = frame(1.0, Some(CALIBRATION_REFERENCE_MS * 1.6));
    assert!(drifted.drift().is_some_and(|d| d > DRIFT_LIMIT));
    assert!(!drifted.comparable());
    assert!(drifted.why_not_comparable().contains("during the sweep"));
}

/// Soundness: the curves are built from self-checking instances. This test
/// re-verifies a sample of each generator independently of the solver — a
/// corrupted generator (one that builds a witness/identity that does not hold)
/// must be caught here, before any frontier number is trusted.
/// Every committed [`TimingBaseline`], checked against its own stated rule.
///
/// A ceiling that is not actually above the measured spread, or a spread that is
/// not ordered, is a band nobody can read — and a `ceiling_ms` typed one digit
/// too large is a ratchet that cannot fail, which this repository has shipped
/// before (six of seven guards in one suite were removable with everything still
/// green). So the arithmetic relation between the four numbers is asserted here
/// rather than trusted to the comment beside them.
#[test]
fn timing_baselines_are_internally_consistent() {
    let families: [(&str, &TimingBaseline); 5] = [
        ("bv_reduction", &TIMING_BV_REDUCTION),
        ("lia_cuts", &TIMING_LIA_CUTS),
        ("string_bound", &TIMING_STRING_BOUND),
        ("nra_degree", &TIMING_NRA_DEGREE),
        ("nia_unsat", &TIMING_NIA_UNSAT),
    ];
    for (family, baseline) in families {
        assert!(
            !baseline.pins.is_empty(),
            "[{family}] pins no timing points, so its timing ratchet cannot fail"
        );
        assert!(
            baseline.pins.windows(2).all(|w| w[0] < w[1]),
            "[{family}] pins must be strictly increasing and distinct: {:?}",
            baseline.pins
        );
        assert!(
            baseline.min_ms <= baseline.median_ms && baseline.median_ms <= baseline.max_ms,
            "[{family}] measured spread is not ordered: min {:.1} / median {:.1} / max {:.1}",
            baseline.min_ms,
            baseline.median_ms,
            baseline.max_ms,
        );
        let expected = baseline.max_ms * TIMING_BAND_FACTOR;
        assert!(
            (baseline.ceiling_ms - expected).abs() <= 0.1 * TIMING_BAND_FACTOR,
            "[{family}] ceiling {:.1} ms is not {TIMING_BAND_FACTOR:.1}x the slowest baseline \
             run ({:.1} ms => {expected:.1} ms). The ceiling is DERIVED from the measurement; \
             re-measure over {TIMING_BASELINE_RUNS} runs rather than widening it by hand.",
            baseline.ceiling_ms,
            baseline.max_ms,
        );
    }
}

/// The timing ratchet's own controls: it accepts what it must accept and fires
/// on each way it is meant to fire.
///
/// Written as an adversarial fixture rather than an observation of a real run,
/// because a real run only ever exercises the accepting branch — and "a checker
/// that cannot fail is worse than no checker".
#[test]
fn timing_ratchet_fires_on_a_slowdown_and_not_on_a_healthy_run() {
    let baseline = TimingBaseline {
        pins: &[2, 3],
        min_ms: 90.0,
        median_ms: 100.0,
        max_ms: 110.0,
        ceiling_ms: 165.0,
    };
    // A box measured at 2x the reference: raw times are doubled, calibrated
    // times are not. This is the load-invariance the whole design rests on, so
    // it is asserted rather than assumed.
    let measurement = Measurement {
        machine: Machine {
            host: "fixture".to_owned(),
            cpus: 8,
            model: "fixture".to_owned(),
        },
        calibration_start_ms: CALIBRATION_REFERENCE_MS * 2.0,
        calibration_end_ms: Some(CALIBRATION_REFERENCE_MS * 2.0),
        raw_scale: 2.0,
        scale: 2.0,
        load_start: None,
        load_end: None,
    };
    let point = |n: u32, decided: bool, solve_ms: f64| CurvePoint {
        n,
        decided_correct: decided,
        status: if decided { "unsat" } else { "unknown" },
        solve_ms,
    };

    // Healthy: 120 + 80 raw on a 2x box = 100 ms calibrated, at the median.
    let healthy = vec![
        point(1, true, 10.0),
        point(2, true, 120.0),
        point(3, true, 80.0),
        point(4, true, 900.0),
    ];
    let measured = measure_timing(&baseline, &healthy, &measurement);
    assert_eq!(measured.calibrated_total_ms, Some(100.0));
    assert!(
        timing_regression("fixture", &baseline, &measured, &measurement).is_none(),
        "a run at the committed median must not fire"
    );

    // Still healthy at the ceiling exactly: 330 raw = 165 calibrated.
    let at_ceiling = vec![point(2, true, 165.0), point(3, true, 165.0)];
    let measured = measure_timing(&baseline, &at_ceiling, &measurement);
    assert_eq!(measured.calibrated_total_ms, Some(165.0));
    assert!(
        timing_regression("fixture", &baseline, &measured, &measurement).is_none(),
        "the ceiling is inclusive"
    );

    // A 2x slowdown on one pinned path, everything still decided and the
    // frontier untouched: exactly the regression no other gate in the repository
    // can see.
    let slow = vec![point(2, true, 240.0), point(3, true, 160.0)];
    let measured = measure_timing(&baseline, &slow, &measurement);
    assert_eq!(measured.calibrated_total_ms, Some(200.0));
    let fired = timing_regression("fixture", &baseline, &measured, &measurement)
        .expect("a 2x slowdown over the ceiling must fire");
    assert!(fired.contains("TIMING REGRESSION"), "{fired}");
    assert!(fired.contains("200.0 ms calibrated"), "{fired}");

    // A pin that stopped deciding is a timing failure too — the instance ran out
    // of clock, which is the same finding arriving one step later.
    let undecided = vec![point(2, true, 120.0), point(3, false, 9000.0)];
    let measured = measure_timing(&baseline, &undecided, &measurement);
    assert_eq!(measured.calibrated_total_ms, None);
    let fired = timing_regression("fixture", &baseline, &measured, &measurement)
        .expect("an undecided pin must fire");
    assert!(fired.contains("did not decide"), "{fired}");

    // A sweep that never reached a pin cannot be silently scored.
    let truncated = vec![point(2, true, 120.0)];
    let measured = measure_timing(&baseline, &truncated, &measurement);
    assert_eq!(measured.calibrated_total_ms, None);
    let fired = timing_regression("fixture", &baseline, &measured, &measurement)
        .expect("a missing pin must fire");
    assert!(fired.contains("never reached"), "{fired}");
}

#[test]
fn every_generated_instance_self_checks() {
    // bv_reduction: each depth is an exhaustively-verified UNSAT identity.
    for n in 1..=8 {
        bv_reduction_scenario(n)
            .self_check()
            .unwrap_or_else(|e| panic!("bv_reduction N={n} self-check: {e}"));
    }
    // lia_cuts: each system is a witness-checked SAT scenario.
    for n in 1..=8 {
        lia_cuts_scenario(n)
            .self_check()
            .unwrap_or_else(|e| panic!("lia_cuts N={n} self-check: {e}"));
    }
    // string_bound: each witness independently satisfies its string constraints.
    for n in 2..=12 {
        let w = string_bound_witness(n);
        assert!(
            string_bound_self_check(&w, n),
            "string_bound N={n}: witness {w:?} failed self-check",
        );
    }
    // nra_degree: each shifted sum-of-even-powers instance is UNSAT by
    // nonnegativity + bounded rational grid (no solver involved).
    for n in 1..=6 {
        assert!(
            nra_degree_self_check(n),
            "nra_degree N={n} (degree {}) failed self-check",
            2 * n,
        );
    }
    // nia_unsat: each no-square-mod instance is UNSAT by residue table +
    // exhaustive bounded enumeration over the finite integer domain.
    for n in 1..=8 {
        assert!(nia_unsat_self_check(n), "nia_unsat N={n} failed self-check");
    }
}

/// Soundness (negative direction): the `nra_degree` / `nia_unsat` self-checks
/// must REJECT a corrupted construction, not just accept the good one — otherwise
/// they would not actually guard soundness. We feed each independent check an
/// instance it must call NOT-unsat and confirm it returns `false`.
#[test]
fn nonlinear_self_checks_reject_corruption() {
    // nra_degree: an ODD exponent breaks the even-power nonnegativity argument
    // (e.g. degree 3 is negative for negative bases), so the self-check — which
    // requires an even exponent and grid-confirms no satisfying point — must
    // reject it. We re-derive the check's verdict on a doctored exponent.
    assert!(
        !nra_degree_self_check_with_degree(3),
        "nra_degree self-check must reject an odd (degree-3) construction — its \
         positivity argument does not hold",
    );

    // nia_unsat: if `r` were a quadratic RESIDUE mod m (e.g. r=1 mod 3, since
    // 1^2 ≡ 1), the system would be satisfiable, so the exhaustive-enumeration
    // self-check must return false (it finds x=1 with x^2 ≡ 1).
    assert!(
        !nia_unsat_self_check_with_case(3, 1, 2),
        "nia_unsat self-check must reject a residue (r=1 mod 3) construction — it \
         IS satisfiable (x=1)",
    );
}

/// The `bv_reduction` fall-off is **the reduction lever**, not a generic limit.
/// With `preprocess` OFF (and a capped encoding so the un-reduced tower can't be
/// brute-bit-blasted under budget), an instance well *inside* the reduction-on
/// frontier degrades to a non-`unsat` result; with `preprocess` ON (the default)
/// the same instance is decided. This is the attributability proof: the frontier
/// moves with the lever.
#[test]
fn bv_reduction_falloff_is_the_lever() {
    // A modest `N` whose `N²` multiplier tower reduction-ON folds trivially but
    // which is well past where the un-reduced bit-blast fits a capped encoding.
    let n = 6;

    let on = SolverConfig::new().with_timeout(BUDGET); // preprocess defaults ON
    let mut off = SolverConfig::new().with_timeout(BUDGET);
    off.preprocess = false;
    // Force the un-reduced path to actually feel the blow-up by capping the
    // encoding so the `N²`-multiplier tower can't be brute-bit-blasted under budget.
    off.cnf_clause_budget = Some(20_000);
    off.cnf_variable_budget = Some(20_000);
    off.node_budget = Some(20_000);

    let solved_on = solve_capped(bv_reduction_instance(n).unwrap(), on, BUDGET);
    assert_eq!(
        solved_on.status,
        "unsat",
        "reduction-ON must decide N={n} (depth {}, got {})",
        bv_reduction_depth(n),
        solved_on.status,
    );

    let solved_off = solve_capped(bv_reduction_instance(n).unwrap(), off, BUDGET);
    assert_ne!(
        solved_off.status, "unsat",
        "reduction-OFF (budget-capped) was expected to fall short at N={n}, but it \
         decided unsat anyway — the family no longer isolates the reduction lever; \
         deepen the tower",
    );
    eprintln!(
        "bv_reduction lever check: N={n} (depth {}) → reduction-ON {} / reduction-OFF(capped) {}",
        bv_reduction_depth(n),
        solved_on.status,
        solved_off.status,
    );
}
